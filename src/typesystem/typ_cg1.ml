(************************************************************************
*
*  types_cg1.ml   -- Constraint generation for elementary types
*
*
*  Created by Hernán Vanzetto on 23 Oct 2013.
Copyright (c) 2013  INRIA and Microsoft Corporation
*
************************************************************************)

open Ext
open Property

open Expr.T
open Expr.Subst
open Expr.Visit

open List

module B = Builtin

module Fu = Fmtutil.Minimal (Tla_parser.Prec)

(****************************************************************************)

open Typ_t
open Typ_e
open Typ_c
module T = Typ_t
module E = Typ_e
module C = Typ_c

module Dq = Deque

(****************************************************************************)
(** Type System *)

let mk_eq (t1,t2) = CAtom (CEq (E.empty,t1,t2))
let mk_eq_cond (t1,t2) = if T.eq t1 t2 then CAtom CTrue else mk_eq (t1, t2)
let mk_iseq (t1,t2) = CAtom (CIsEq (E.empty,t1,t2))
let mk_var a = TyVar ([],a)

let adj = Expr.Visit.adj
let adjs = Expr.Visit.adjs
(* let bump = Expr.Visit.bump *)

(** From [x1, ..., xn] generates [(x1,x2), (x2,x3), ..., (xn-1,xn)] *)
let rec pairs = function
  | a :: b :: es -> (a,b) :: pairs (b :: es)
  | _ -> []

(** Constraint Generation for  [env] |- [scx e] : [t]
    -- Type system without refinements *)
let rec cg_expr (ts:C.cg_mode) (env:E.t) (t:T.t) (scx:unit Expr.Visit.scx) e : Expr.T.expr * C.t =
  (* Util.eprintf "<< %a|- %a%s : %a >>" E.pp env (E.pp_print_expr (snd scx, Ctx.dot)) e (if Smtcommons.apply_u2bool e then "^bool" else "") E.ppt (env,t) ; *)
  match e.core with
  | Apply ({core = Opaque "boolify"}, [{core = Ix n}]) ->
      e, mk_eq_cond (t, Bool)
        (** << G |- f(e1,...,en)^b : t >> ==
            \E a1...an,a'1...a'n .
                /\   |- G(f) == (a1 -> (a2 -> (... -> (an -> Bool))))
                /\ << G |- e_1 : a'1 >>
                /\ ...
                /\ << G |- e_n : a'n >>
                /\ G |- a'1 <? a1
                /\ ...
                /\ G |- a'n <? an
                /\   |- t == Bool *)
  | Apply ({core = Opaque "boolify"}, [{core = Apply (f, es)}]) ->
      let ar = fresh_tyvar (E.to_cx env, e) in
      let a1s,t1s,es,cs = gen_tyvars ts env scx es in
      let a2s = List.map (fun e -> fresh_tyvar (E.to_cx env, e)) es in
      let t2s = List.map mk_var a2s in
      let f,cf = cg_expr ts env (fold_right (fun tv r -> Func ("", tv, r)) t2s (mk_var ar)) scx f in
      Apply (Opaque "boolify" %% [], [Apply (f, es) @@ e]) @@ e,
      CExists (ar::a1s @ a2s,
        CConj (cs @ (List.map2 (fun a b -> mk_iseq (a,b)) t1s t2s)
                  @ [ cf ; mk_eq_cond (t, Bool) ]))

  (* | Apply ({core = Opaque "boolify"}, [{core = Ix n} as ex]) ->
        let id = Smtcommons.lookup_id (E.to_cx env) n in
      ex, CConj (mk_eq (E.find id env, Bool) :: mk_eq_cond (t, Bool) :: [])
        (** << G |- f(e1,...,en)^b : t >> ==
            \E a1...an,a'1...a'n .
                /\   |- G(f) == (a1 -> (a2 -> (... -> (an -> Bool))))
                /\ << G |- e_1 : a'1 >>
                /\ ...
                /\ << G |- e_n : a'n >>
                /\ G |- a'1 <? a1
                /\ ...
                /\ G |- a'n <? an
                /\   |- t == Bool *)
  | Apply ({core = Opaque "boolify"}, [{core = Apply (f, es)}]) ->
      let ar = fresh_tyvar (E.to_cx env, e) in
      let a1s,t1s,es,cs = gen_tyvars ts env scx es in
      let a2s = List.map (fun e -> fresh_tyvar (E.to_cx env, e)) es in
      let t2s = List.map mk_var a2s in
      let f,cf = cg_expr ts env (fold_right (fun tv r -> Func ("", tv, r)) t2s (mk_var ar)) scx f in
      Apply (Opaque "boolify" %% [], [Apply (f, es) @@ e]) @@ e,
      CExists (ar::a1s @ a2s,
        CConj (cs @ (List.map2 (fun a b -> mk_iseq (a,b)) t1s t2s)
                  @ [ cf ; mk_eq_cond (t, Bool) ])) *)
  | Opaque "boolify" ->
      let a = fresh_tyvar (E.to_cx env, e) in
      e, CExists ([a], mk_eq (t, Func ("",mk_var a, Bool)))
  | Opaque "bool2u" ->
      let a = fresh_tyvar (E.to_cx env, e) in
      e, CExists ([a], mk_eq (t, Func ("",Bool, mk_var a)))
  | Opaque "tla__isAFcn" ->
      let a = fresh_tyvar (E.to_cx env, e) in
      e, CExists ([a], mk_eq (t, Func ("",mk_var a, Bool)))
  | Opaque "tla__fcnapp" ->
      let a1 = fresh_tyvar (E.to_cx env, e) in
      let a2 = fresh_tyvar (E.to_cx env, e) in
      e, CExists ([a1;a2], mk_eq (t, Func ("",mk_var a1, mk_var a2)))
  | Opaque ("tla__plus" | "tla__minus" | "tla__times" | "tla__exp" | "tla__div" | "tla__mod") ->
      let a1 = fresh_tyvar (E.to_cx env, e) in
      let a2 = fresh_tyvar (E.to_cx env, e) in
      let a3 = fresh_tyvar (E.to_cx env, e) in
      e, CExists ([a1;a2;a3], mk_eq (t, Func ("",mk_var a1, Func ("",mk_var a2, mk_var a3))))
  | Ix n ->
      let id = Smtcommons.lookup_id (E.to_cx env) n in
      e, mk_eq (t, E.find id env)
  | Opaque s ->
      e, mk_eq (t, E.find s env)
  | FcnApp (f, [ex]) ->
      let af = fresh_tyvar (E.to_cx env, f) in
      let ae = fresh_tyvar (E.to_cx env, ex) in
      let f,cf = cg_expr ts env (mk_var af) scx f in
      let ex,cex = cg_expr ts env (mk_var ae) scx ex in
      FcnApp (f, [ex]) @@ e,
      CExists ([af;ae], CConj [ cf ; cex ;
        mk_iseq (mk_var ae, Tdom (mk_var af)) ;
        mk_eq (t, Tcod (mk_var af))
        ])
  (* | FcnApp (f, [ex]) ->
      let af = fresh_tyvar (E.to_cx env, f) in
      let ae = fresh_tyvar (E.to_cx env, ex) in
      let ar = fresh_tyvar (E.to_cx env, e) in
      let f,cf = cg_expr ts env (mk_var af) scx f in
      let ex,cex = cg_expr ts env (mk_var ae) scx ex in
      FcnApp (f, [ex]) @@ e,
      CExists ([af;ae;ar], CConj [ cf ; cex ;
        mk_iseq (mk_var af, Func ("", mk_var ae, mk_var ar)) ;
        mk_eq (t, mk_var ar)
        ]) *)
  | Fcn (bs, ex) ->
      let scx', bs, cbs, aas, vs, env' = cg_bounds env scx bs in
      let ae = fresh_tyvar (E.to_cx env', ex) in
      let ex,cex = cg_expr ts env' (mk_var ae) scx' ex in
      let tt = fold_right (fun a r -> Func ("",mk_var a,r)) aas (mk_var ae) in
      Fcn (bs, ex) @@ e,
      CExists (aas @ [ae], CConj (cbs @ [ cex ; mk_eq (t, tt) ]))
  | Apply ({core = Internal op}, es) ->
      let mk_ex op es = Apply (Internal op |> noprops, es) @@ e in
      begin match op, es with
      | B.Cup, [e1 ; e2]
      | B.Cap, [e1 ; e2]
      | B.Setminus, [e1 ; e2] ->
          let a1 = fresh_tyvar (E.to_cx env, e1) in
          let a2 = fresh_tyvar (E.to_cx env, e2) in
          let e1,ce1 = cg_expr ts env (Set (mk_var a1)) scx e1 in
          let e2,ce2 = cg_expr ts env (Set (mk_var a2)) scx e2 in
          mk_ex op [e1 ; e2],
          CExists ([a1;a2], CConj [ ce1 ; ce2 ;
            mk_iseq (mk_var a1, mk_var a2) ;
            mk_eq (t, Set (mk_var a1))
            ])
      | B.SUBSET, [s] ->
          let a = fresh_tyvar (E.to_cx env, s) in
          let s,cs = cg_expr ts env (Set (mk_var a)) scx s in
          mk_ex op [s],
          CExists ([a], CConj [ cs ;
            mk_eq (t, Set (Set (mk_var a)))
            ])
      | B.UNION, [s] ->
          let s,cs = cg_expr ts env (Set t) scx s in
          mk_ex op [s], cs
      | B.DOMAIN, [f] ->
          let af = fresh_tyvar (E.to_cx env, f) in
          let f,cf = cg_expr ts env (mk_var af) scx f in
          mk_ex op [f],
          CExists ([af], CConj [ cf ; mk_eq (t, Set (Tdom (mk_var af))) ])
      (* | B.DOMAIN, [f] ->
          let af = fresh_tyvar (E.to_cx env, f) in
          let a1 = fresh_tyvar (E.to_cx env, e) in
          let a2 = fresh_tyvar (E.to_cx env, (noprops (Opaque "dummy"))) in
          let f,cf = cg_expr ts env (mk_var af) scx f in
          mk_ex op [f],
          CExists ([af;a1;a2], CConj [ cf ;
            mk_iseq (mk_var af, Func ("", mk_var a1, mk_var a2)) ;
            mk_eq (t, Set (mk_var a1))
            ]) *)
      | B.Range, [x ; y] ->
          let ax = fresh_tyvar (E.to_cx env, x) in
          let ay = fresh_tyvar (E.to_cx env, y) in
          let x,cx = cg_expr ts env (mk_var ax) scx x in
          let y,cy = cg_expr ts env (mk_var ay) scx y in
          mk_ex op [x ; y],
          CExists ([ax;ay], CConj [ cx ; cy ;
            mk_iseq (mk_var ax, Int) ;
            mk_iseq (mk_var ax, Int) ;
            mk_eq_cond (t, Set Int)
            ])
      | (B.Conj | B.Disj | B.Implies | B.Equiv), [e1 ; e2] ->
          let e1,ce1 = cg_expr ts env Bool scx e1 in
          let e2,ce2 = cg_expr ts env Bool scx e2 in
          mk_ex op [e1 ; e2],
          CConj [ ce1 ; ce2 ; mk_eq (t, Bool) ]
      | B.Neg, [ex] ->
          let ex,c = cg_expr ts env Bool scx ex in
          mk_ex op [ex],
          CConj [c ; mk_eq (t, Bool)]
      | B.Eq, [e1 ; e2] when ts = TypHyp ->
          let a1 = fresh_tyvar (E.to_cx env, e1) in
          let a2 = fresh_tyvar (E.to_cx env, e2) in
          let e1,ce1 = cg_expr OnlySafe env (mk_var a1) scx e1 in
          let e2,ce2 = cg_expr OnlySafe env (mk_var a2) scx e2 in
          mk_ex op [e1 ; e2],
          CExists ([a1;a2], CConj [ ce1 ; ce2 ;
            (* (if (ts = TypHyp) then mk_eq (mk_var a1, mk_var a2) else mk_iseq (mk_var a1, mk_var a2)) ; *)
            mk_eq (mk_var a1, mk_var a2) ;
            mk_eq_cond (t, Bool)
            ])
      | B.Mem, [e1 ; e2] when ts = TypHyp ->
          let a1 = fresh_tyvar (E.to_cx env, e1) in
          let a2 = fresh_tyvar (E.to_cx env, e2) in
          let e1,ce1 = cg_expr OnlySafe env (mk_var a1) scx e1 in
          let e2,ce2 = cg_expr OnlySafe env (Set (mk_var a2)) scx e2 in
          mk_ex op [e1 ; e2],
          CExists ([a1;a2], CConj [ ce1 ; ce2 ;
            mk_eq (mk_var a1, mk_var a2) ;
            mk_eq_cond (t, Bool)
            ])
      | (B.Eq | B.Neq), [e1 ; e2] ->
          let a1 = fresh_tyvar (E.to_cx env, e1) in
          let a2 = fresh_tyvar (E.to_cx env, e2) in
          let e1,ce1 = cg_expr ts env (mk_var a1) scx e1 in
          let e2,ce2 = cg_expr ts env (mk_var a2) scx e2 in
          mk_ex op [e1 ; e2],
          CExists ([a1;a2], CConj [ ce1 ; ce2 ;
            mk_iseq (mk_var a1, mk_var a2) ;
            mk_eq_cond (t, Bool)
            ])
      | (B.Mem | B.Notmem), [e1 ; e2] ->
          let a1 = fresh_tyvar (E.to_cx env, e1) in
          let a2 = fresh_tyvar (E.to_cx env, e2) in
          let e1,ce1 = cg_expr ts env (mk_var a1) scx e1 in
          let e2,ce2 = cg_expr ts env (Set (mk_var a2)) scx e2 in
          mk_ex op [e1 ; e2],
          CExists ([a1;a2], CConj [ ce1 ; ce2 ;
            mk_iseq (mk_var a1, mk_var a2) ;
            mk_eq_cond (t, Bool)
            ])
      | B.Subseteq, [e1 ; e2] ->
          let a1 = fresh_tyvar (E.to_cx env, e1) in
          let a2 = fresh_tyvar (E.to_cx env, e2) in
          let e1,ce1 = cg_expr ts env (Set (mk_var a1)) scx e1 in
          let e2,ce2 = cg_expr ts env (Set (mk_var a2)) scx e2 in
          mk_ex op [e1 ; e2],
          CExists ([a1;a2], CConj [ ce1 ; ce2 ;
            (if ts = TypHyp then mk_eq else mk_iseq) (mk_var a1, mk_var a2) ;
            mk_eq_cond (t, Bool)
            ])
      | (B.Plus | B.Minus | B.Times |
          B.Exp | B.Ratio | B.Quotient | B.Remainder), [x ; y] ->
          let a1 = fresh_tyvar (E.to_cx env, x) in
          let a2 = fresh_tyvar (E.to_cx env, y) in
          let x,cx = cg_expr ts env (mk_var a1) scx x in
          let y,cy = cg_expr ts env (mk_var a2) scx y in
          mk_ex op [x ; y],
          CExists ([a1;a2], CConj [ cx ; cy ;
            mk_iseq (mk_var a1, Int) ;
            mk_iseq (mk_var a2, Int) ;
            mk_eq_cond (t, Int) ;
            ])
      | B.Uminus, [{core = Num (n,"")}] ->
          e, mk_eq (t, Int)
      | B.Uminus, [x] ->
          let a = fresh_tyvar (E.to_cx env, x) in
          let x,c = cg_expr ts env (mk_var a) scx x in
          mk_ex op [x],
          CExists ([a], CConj [ c ;
            mk_iseq (mk_var a, Int) ;
            mk_eq_cond(t, Int)
            ])
      | (B.Lteq | B.Lt | B.Gteq | B.Gt), [x ; y] ->
          let a1 = fresh_tyvar (E.to_cx env, x) in
          let a2 = fresh_tyvar (E.to_cx env, y) in
          let x,cx = cg_expr ts env (mk_var a1) scx x in
          let y,cy = cg_expr ts env (mk_var a2) scx y in
          mk_ex op [x ; y],
          CExists ([a1;a2], CConj [ cx ; cy ;
            mk_iseq (mk_var a1, Int) ;
            mk_iseq (mk_var a2, Int) ;
            mk_eq_cond (t, Bool)
          ])

      | B.Seq, [ex] -> e, CAtom CTrue
      | B.Head, [ex] -> e, CAtom CTrue
      | B.Tail, [ex] -> e, CAtom CTrue
      | B.Len, [ex] -> e, CAtom CTrue
      | B.BSeq, [e1 ; e2] -> e, CAtom CTrue
      | B.Cat, [e1 ; e2] -> e, CAtom CTrue
      | B.Append, [e1 ; e2] -> e, CAtom CTrue
      | B.SelectSeq, [e1 ; e2] -> e, CAtom CTrue
      | B.SubSeq, [e1;e2;e3] -> e, CAtom CTrue

      | _ ->
          Util.eprintf "!! Constraint generation. Expression not supported: %a"
            (E.pp_print_expr (snd scx, Ctx.dot)) e ;
          raise Typeinf_failed
      end
  | Apply (f, es) when T.is_hard_bool e ->
      let ar = fresh_tyvar (E.to_cx env, e) in
      let a1s,t1s,es,cs = gen_tyvars ts env scx es in
      let a2s = List.map (fun e -> fresh_tyvar (E.to_cx env, e)) es in
      let t2s = List.map (fun a -> mk_var a) a2s in
      let f,cf = cg_expr ts env (fold_right (fun tv r -> Func ("", tv, r)) t2s (mk_var ar)) scx f in
      Apply (f, es) @@ e,
      CExists (ar::a1s @ a2s,
        CConj (cs @ (List.map2 (fun a b -> mk_iseq (a,b)) t1s t2s)
                  @ [ cf ; mk_eq_cond (t, Bool) ]))
  | Apply (f, es) ->
      let ar = fresh_tyvar (E.to_cx env, e) in
      let a1s,t1s,es,cs = gen_tyvars ts env scx es in
      let a2s = List.map (fun e -> fresh_tyvar (E.to_cx env, e)) es in
      let t2s = List.map (fun a -> mk_var a) a2s in
      let f,cf = cg_expr ts env (fold_right (fun tv r -> Func ("", tv, r)) t2s (mk_var ar)) scx f in
      Apply (f, es) @@ e,
      CExists (ar::a1s @ a2s,
        CConj (cs @ (List.map2 (fun a b -> mk_iseq (a,b)) t1s t2s)
                  @ [ cf ; mk_eq (t, mk_var ar) ]))
  | SetEnum [] ->
      (* mk_eq (t, Set Emptyset) *)
      let a = fresh_tyvar (E.to_cx env, e) in
      e, CExists ([a], mk_eq (t, Set (mk_var a)))
  | SetEnum [ex] ->
      let a = fresh_tyvar (E.to_cx env, ex) in
      let ex,cex = cg_expr ts env (mk_var a) scx ex in
      SetEnum [ex] @@ e,
      CExists ([a], CConj ([cex ; mk_eq (t, Set (mk_var a)) ]))
  | SetEnum es ->
      let aas,ats,es,cs = gen_tyvars ts env scx es in
      SetEnum es @@ e,
      CExists (aas, CConj
        (cs @ List.map (fun (a,b) -> mk_iseq (a,b)) (pairs ats) @
          [ mk_eq (t, Set (List.hd ats)) ]))
      (* let a = fresh_tyvar (E.to_cx env, e) in
      CExists ([a], CConj
        (List.map (cg_expr ts env (mk_var a) scx) es @ [
        mk_eq (t, Set (mk_var a))
        ])) *)
  | SetSt (v,d,ex) ->
      let a = fresh_tyvar (E.to_cx env, d) in
      let d,cd = cg_expr ts env (Set (mk_var a)) scx d in
      let scx' = adj scx (Fresh (v, Shape_expr, Constant, Bounded (d, Visible)) @@ v) in
      let ex,cex = cg_expr ts (E.adj env (v.core,mk_var a)) Bool scx' ex in
      (* let v = v <<< mk_var a in *)
      SetSt (v <<< mk_var a,d,ex) @@ e,
      CExists ([a], CConj [ cd ; cex ;
        mk_eq (t, Set (mk_var a))
      ])
  | SetOf (ex, bs) ->
      let scx', bs, cbs, aas, vs, env' = cg_bounds env scx bs in
      let ae = fresh_tyvar (E.to_cx env', ex) in
      let ex,cex = cg_expr ts env' (Set (mk_var ae)) scx' ex in
      SetOf (ex, bs) @@ e,
      CExists (aas @ [ae], CConj (cbs @ [ cex ; mk_eq (t, Set (mk_var ae)) ]))
  | String _ ->
      e, mk_eq_cond (t, Str)
  | Num _ ->
      e, mk_eq_cond (t, Int)
  | Internal B.Int ->
      e, mk_eq_cond (t, Set Int)
  | Internal B.Nat ->
      e, mk_eq_cond (t, Set Int)
  | Internal B.STRING ->
      e, mk_eq_cond (t, Set Str)
  | Arrow (x,y) ->
      let a1 = fresh_tyvar (E.to_cx env, x) in
      let a2 = fresh_tyvar (E.to_cx env, y) in
      let x,cx = cg_expr ts env (Set (mk_var a1)) scx x in
      let y,cy = cg_expr ts env (Set (mk_var a2)) scx y in
      Arrow (x,y) @@ e,
      CExists ([a1;a2], CConj [ cx ; cy ;
        mk_eq (t, Set (Func ("",mk_var a1,mk_var a2)))
      ])
  | If (c,a,b) ->
      let a1 = fresh_tyvar (E.to_cx env, c) in
      let a2 = fresh_tyvar (E.to_cx env, a) in
      let a3 = fresh_tyvar (E.to_cx env, b) in
      let c,cc = cg_expr ts env (mk_var a1) scx c in
      let a,ca = cg_expr ts env (mk_var a2) scx a in
      let b,cb = cg_expr ts env (mk_var a3) scx b in
      If (c,a,b) @@ e,
      CExists ([a1;a2;a3], CConj [ cc ; ca ; cb ;
        mk_iseq (mk_var a1, Bool) ;
        mk_iseq (mk_var a2, mk_var a3) ;
        mk_eq (t, mk_var a2)
      ])
  | Except (f, [([Except_apply a], b)]) ->
      let a1 = fresh_tyvar (E.to_cx env, f) in
      let a2 = fresh_tyvar (E.to_cx env, a) in
      let a3 = fresh_tyvar (E.to_cx env, b) in
      let f,cf = cg_expr ts env (mk_var a1) scx f in
      let a,ca = cg_expr ts env (mk_var a2) scx a in
      let b,cb = cg_expr ts env (mk_var a3) scx b in
      Except (f, [([Except_apply a], b)]) @@ e,
      CExists ([a1;a2;a3], CConj [ cf; ca; cb;
        mk_iseq (Func ("", mk_var a2, mk_var a3), mk_var a1);
        (* mk_iseq (mk_var a1, mk_var a4); *)
        (* mk_iseq (mk_var a3, mk_var a5); *)
        mk_eq (t, mk_var a1)
      ])

  (** CHECK: Special case *)
  | Tuple [] ->
      e, mk_eq (t, Func ("",Top,Top))

  | Tuple es ->
      let aas,ats,es,cs = gen_tyvars ts env scx es in
      Tuple es @@ e,
      CExists (aas, CConj
        (cs @ [ mk_eq (t, Func ("",Int, List.hd ats)) ]
      ))
  | Product es ->
      let aas,ats,es,cs = gen_tyvars ~sets:true ts env scx es in
      Product es @@ e,
      CExists (aas, CConj
        (cs @ List.map (fun (a,b) -> mk_iseq (a,b)) (pairs ats) @
          [ mk_eq (t, Set (Func ("",Int, List.hd ats))) ]
      ))

  | Record res ->
      let hs,es = split res in
      let aas,ats,es,cs = gen_tyvars ts env scx es in
      let res = combine hs es in
      Record res @@ e,
      CExists (aas, CConj
        (cs @ [ mk_eq (t, Rec (combine hs ats)) ]
      ))
  | Rect res ->
      let hs,es = split res in
      let aas,ats,es,cs = gen_tyvars ~sets:true ts env scx es in
      let res = combine hs es in
      Rect res @@ e,
      CExists (aas, CConj
        (cs @ [ mk_eq (t, Set (Rec (combine hs ats))) ]
      ))
  | Dot (f,h) ->
      let a = fresh_tyvar (E.to_cx env, f) in
      let f,cf = cg_expr ts env (mk_var a) scx f in
      Dot (f, h) @@ e,
      CExists ([a], CConj [ cf ; mk_eq (t, Rec_dot (mk_var a, h)) ])

  (* TODO *)
  | Choose _ -> e, mk_eq (t, Top)

  | Parens (ex,_) ->
      cg_expr ts env t scx ex
  | Internal B.BOOLEAN ->
      e, mk_eq_cond (t, Set Bool)

(** Constraint Generation for  env |- (cx e) : Bool *)
  | Internal B.TRUE
  | Internal B.FALSE ->
      e, mk_eq_cond (t, Bool)
  | Quant (q, bs, ex) ->
      (** TODO: obtain typing hypotheses from [ex] *)
      let scx', bs, cbs, aas, vs, env' = cg_bounds env scx bs in
      let ex,cex = cg_expr OnlySafe env' Bool scx' ex in
      Quant (q, bs, ex) @@ e, CExists (aas, CConj (cbs @ [ cex ; mk_eq_cond (t, Bool) ]))
  | List (b,es) ->
      let es,ces = split (List.map (cg_expr ts env Bool scx) es) in
      let e = List (b,es) @@ e in
      e, CConj (mk_eq_cond (t, Bool) :: ces)
  | Sequent sq ->
      let e,c = cg_expr ts env Bool scx (Smtcommons.unroll_seq sq) in
      e, CConj [mk_eq_cond (t, Bool) ; c]
  (* | _ ->
      cg_expr ts env Bool cx e *)
  | _ ->
      Util.eprintf "!! Constraint generation. Expression not supported: %a"
        (E.pp_print_expr (E.to_scx env, Ctx.dot)) e ;
      raise Typeinf_failed

(**
  [aas] = [ ..., a_i, ... ]           type variable names
  [ats] = [ ..., TyVar a_i, ... ]     type variables for [es]
  [es]  = [ ..., e_i^t, ... ]         annotated expressions
  [cs]  = [ ..., << env |- e_i : a_i >>, ... ]  constraints
  *)
and gen_tyvars ?sets:(s=false) ts env scx es =
  let aas = List.map (fun e -> fresh_tyvar (E.to_cx env, e)) es in
  let ats = List.map mk_var aas in
  let es,cs = split (map2 (fun e a -> cg_expr ts env (if s then Set a else a) scx e) es ats) in
  aas, ats, es, cs

(** Generates:
  [scx]
  [hs]
  [cbs] = list of constraints in [bs]
  [aas] = list of new type variable names (alpha strings)
  [vs]  = list of bounded variables (alphas)
  [env]
  *)
and cg_bounds env scx bs =
  let bs = Smtcommons.unditto bs in
  let bs, cbs, aas, vs =
    List.map begin
      fun (v,k,d) ->
        let a = fresh_tyvar ~id:("_"^v.core) (E.to_cx env, Opaque v.core @@ v) in
        match d with
        | Domain s ->
            let s,cs = cg_expr OnlySafe env (Set (mk_var a)) scx s in
            (v <<< mk_var a, k, Domain s), [cs], a, v.core
        | _ ->
            (v <<< mk_var a, k, d), [], a, v.core
    end bs
    |> fold_left (fun (bs,cbs,aas,vs) (b,cs,a,v) -> bs@[b], cbs @ cs, aas@[a], vs@[v])
        ([],[],[],[])
  in
  let hs = List.map begin
    fun (v, k, _) -> Fresh (v, Shape_expr, k, Unbounded) @@ v
  end bs in
  let env = fold_left2 (fun e v a -> E.adj e (v,mk_var a)) env vs aas in
  (adjs scx hs, bs, cbs, aas, vs, env)

and cg_hyp (env:E.t) scx h =
(* let ph cx ff h = ignore (E.pp_print_hyp cx ff h) in *)
  match h.core with
  | Fact (e, Visible, tm) ->
(* Util.eprintf "<< [%d-%d] %a|- %a : Bool >>." (Dq.size env) (Dq.size (snd scx)) E.pp env (ph (E.to_scx env, Ctx.dot)) h ; *)
      let e, ce = cg_expr (if Smtcommons.is_typhyp (E.to_scx env) e then TypHyp else OnlySafe) env Bool scx e in
      let h = Fact (e, Visible, tm) @@ h in
      (Expr.Visit.adj scx h, h, env $$ (h,None), None, Some ce)
  | Fresh (nm, shp, lc, dom) ->
(* Util.eprintf "<< %a|- %a : Bool >>.." E.pp env (ph (E.to_scx env, Ctx.dot)) h; *)
      let a = fresh_tyvar ~id:("_"^nm.core) (E.to_cx env, Opaque ("fresh:"^nm.core) @@ nm) in
      let nm = nm <<< mk_var a in
      let env' = E.adj env (nm.core, mk_var a) in
      let dom,c = match dom with
        | Bounded (r, Visible) ->
            let e = Apply (Internal B.Mem %% [], [Opaque nm.core @@ nm ; app_expr (shift 1) r]) %% [] in
            let e, c = cg_expr TypHyp env' Bool scx e in
            let r = match e.core with
              | Apply ({core = Internal B.Mem}, [_ ; r]) -> r
              | _ -> Errors.bug "Typesystem.cg_hyp: Fresh hypothesis"
            in
            let r = app_expr (shift (-1)) r in
            Bounded (r, Visible), Some c
        | Bounded (r, rvis) -> Bounded (r, rvis), None
        | Unbounded -> Unbounded, None
      in
      let h = Fresh (nm, shp, lc, dom) @@ h in
      (Expr.Visit.adj scx h, h, env', Some a, c)
  | Flex nm ->
(* Util.eprintf "<< %a|- %a : ? >>..." E.pp env (ph (E.to_scx env, Ctx.dot)) h; *)
      let a = fresh_tyvar ~id:("_"^nm.core) (E.to_cx env, Opaque ("flex:"^nm.core) @@ nm) in
      let h = Flex (nm <<< mk_var a) @@ h in
      let env = E.adj env (nm.core, mk_var a) in
      (Expr.Visit.adj scx h, h, env, Some a, None)
  | Defn ({core = Operator (nm, _)}, _, Visible, _) ->
(* Util.eprintf "<< %a|- %a : ? >>...." E.pp env (ph (E.to_scx env, Ctx.dot)) h; *)
      let a = fresh_tyvar ~id:("_"^nm.core) (E.to_cx env, Opaque ("defn:"^nm.core) @@ nm) in
      let h = Flex (nm <<< mk_var a) @@ h in
      let env = E.adj env (nm.core, mk_var a) in
      (Expr.Visit.adj scx h, h, env, Some a, None)
  | _ ->
      (adj scx h, h, env $$ (h,None), None, None)

(** argument [scx] is the global context of sq.active
    ignore returning [scx]
    *)
and cg_hyps env scx hs =
  match Dq.front hs with
  | None -> (scx, Dq.empty, env, [], [])
  | Some (h, hs) ->
      let _, h, env, v, c = cg_hyp env scx h in
      let _, hs, env, vs, cs = cg_hyps env scx hs in
      let vs = match v with Some v -> v::vs | None -> vs in
      let cs = match c with Some c -> c::cs | None -> cs in
      (scx, Dq.cons h hs, env, vs, cs)

and cg_sequent env scx sq =
(* Smtcommons.ifprint 3 "<< [%d] %a@, |- %a : Bool >>" (Dq.size env) E.pp env Fu.pp_print_minimal (Fu.Big (fun ff -> ignore (E.pp_print_sequent (snd scx, Ctx.dot) ff sq))) ; *)
  let scx, hs, env, vs, chs = cg_hyps env scx sq.context in
  let c, cc = cg_expr OnlySafe env Bool scx sq.active in
  let cc = C.mk_ex (vs, chs @ [cc]) in
  (scx, { context = hs ; active = c }, env, cc)

let cg sq =
  let tx = Sys.time () in
  Smtcommons.ifprint 2 "** Constraint generation...";
(* Util.eprintf "CG: %a" Fu.pp_print_minimal (Fu.Big (fun ff -> ignore (E.pp_print_sequent (sq.context, Ctx.dot) ff sq))); *)
  let fvs = Smtcommons.fv ((),sq.context) sq in
  let fvs = Smtcommons.subtract fvs "boolify" in
  let _,sq,env,c = cg_sequent E.empty ((),sq.context) sq in
  let c = C.mk_ex (fvs, [c]) in
  Smtcommons.ifprint 2 "** Constraint generation in %5.3fs.%!" (Sys.time() -. tx) ;
  Smtcommons.ifprint 3 "@[<hov2>C_0 == @[<v>%a@] ||-@ @[<hov>%a@]@]" E.pp env C.pp (env,c) ;
  (* Smtcommons.ifprint 3 "   Constraint length = %d" (C.c_length c) ; *)
(* Smtcommons.ifprint 3 "sq': %a" Fu.pp_print_minimal (Fu.Big (fun ff -> ignore (E.pp_print_sequent (sq.context, Ctx.dot) ff sq))); *)
  (sq, env, c)
