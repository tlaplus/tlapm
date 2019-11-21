(************************************************************************
*
*  typ_cg2.ml   -- Constraint generation (CG) for type system with refinement types
*
*
*  Created by Hernán Vanzetto on 23 Oct 2013.
*  Copyright (c) 2013 __MyCompanyName__. All rights reserved.
*
************************************************************************)

Revision.f "$Rev: 32384 $";;

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

let mk_eq (e,t1,t2) = CAtom (CEq (e,t1,t2))
let mk_iseq (e,t1,t2) = CAtom (CIsEq (e,t1,t2))
let mk_eq_bool t = if t = Bool then CAtom CTrue else mk_eq (E.empty, t, Bool)
let mk_sub (e,t1,t2) = CAtom (CSub (e,t1,t2))
let mk_issub (e,t1,t2) = CAtom (CIsSub (e,t1,t2))
let mk_var a = TyVar ([],a)

let adj = Expr.Visit.adj
let adjs = Expr.Visit.adjs
(* let bump = Expr.Visit.bump *)

(** From [x1, ..., xn] generates [(x1,x2), (x2,x3), ..., (xn-1,xn)] *)
let rec pairs = function
  | a :: b :: es -> (a,b) :: pairs (b :: es)
  | _ -> []

(****************************************************************************)

(** Constraint Generation for  [env] |- [scx e] : [t]
    -- Type system without refinements *)
let rec cg_expr
  (mode : C.cg_mode)
  (env : E.t)
  (t : T.t)
  (scx : unit Expr.Visit.scx)       (** just used to calculate offset from final context for [sq.active] *)
  (e : Expr.T.expr)
  : (Expr.T.expr * C.t) =
(* Util.eprintf "<< %a|- %a : %a >>" E.pp env (E.pp_print_expr (E.to_scx env, Ctx.dot)) e E.ppt (env,t) ; *)

  (* let mk e = noprops e in *)
  let app op x y = Apply (Internal op %% [], [x ; y]) %% [] in
  let apps op xs = Apply (Internal op %% [], xs) %% [] in
  let ix1 = Ix 1 %% [] in
  let sh1 e = app_expr (shift 1) e in
  let mk_ex op es = Apply (Internal op %% [], es) @@ e in
  let mk_num n = Num (string_of_int n,"") %% [] in
  let lAnd es = List (And, es) %% [] in
  (* let lOr es = List (Or, es) %% [] in *)

  let diff = Dq.size (snd scx) - Dq.size env in
  let sh_diff e = app_expr (shift diff) e in

  match e.core with
  | Ix n ->
      let id = Smtcommons.lookup_id (E.to_cx env) n in
      let tt = E.find id env in
      e, mk_eq (E.empty, t, tt)
  | Opaque "boolify" ->
      let a = fresh_tyvar (E.to_cx env, e) in
      e, CExists ([a], mk_eq (E.empty, t, Func ("", mk_var a, Bool)))
  | Opaque "bool2u" ->
      let a = fresh_tyvar (E.to_cx env, e) in
      e, CExists ([a], mk_eq (E.empty, t, Func ("",Bool, mk_var a)))
  | Opaque "tla__isAFcn" ->
      let a = fresh_tyvar (E.to_cx env, e) in
      e, mk_eq (E.empty, t, Func ("", mk_var a, Bool))
  | Opaque "tla__fcnapp" ->
      let a1 = fresh_tyvar (E.to_cx env, e) in
      let a2 = fresh_tyvar (E.to_cx env, e) in
      e, mk_eq (E.empty, t, Func ("", mk_var a1, mk_var a2))
  | Opaque s ->
      e, mk_eq (E.empty, t, E.find s env)
  | FcnApp (f, [ex]) ->
(* Util.eprintf "<< %a|- %a : %a >>" E.pp env (E.pp_print_expr (E.to_scx env, Ctx.dot)) e E.ppt (env,t) ; *)
(* Util.eprintf "<< ___ |- %a : %a >>" (E.pp_print_expr (E.to_scx env, Ctx.dot)) e E.ppt (env,t) ; *)
(* Util.eprintf "<< ___ |- %a : %a >>" (E.pp_print_expr (snd scx, Ctx.dot)) (sh_diff ex) E.ppt (env,t) ; *)
      let af = fresh_tyvar (E.to_cx env, f) in
      let ae = fresh_tyvar (E.to_cx env, ex) in
      let f,cf = cg_expr mode env (mk_var af) scx f in
      let ex,cex = cg_expr mode env (mk_var ae) scx ex in
      let x = fresh_tyterm () in
      FcnApp (f, [ex]) @@ e,
      CExists ([af;ae], CConj [ cf ; cex ;
        mk_issub (E.empty, mk_var ae, Tdom (mk_var af)) ;
        mk_eq (E.empty, t, Tcod (TyVar ([x, E.to_cx env, sh_diff ex, mk_var ae], af)))         (** [x] is Ix 2 in [Tcod (mk_var af)] *)
        ])
  | Fcn (bs, ex) ->
      let scx', bs, cbs, a1s, a2s, vs, env', local_env = cg_bounds env scx bs in
      let a2s = List.map Option.get a2s in
      (* let css = map2 (fun a1 a2 -> mk_sub (env, mk_var a2, mk_var a1)) a1s a2s in   (** \a_x <: \a_S *) *)
      let ae = fresh_tyvar (E.to_cx env', ex) in
      let ex,cex = cg_expr mode env' (mk_var ae) scx' ex in
      (* let tt = fold_right2 (fun v a r -> Func (v,mk_var a,r)) vs a2s (mk_var ae) in *)

      (* let z = fresh_tyterm () in *)
      (* let tr = Ref (z,mk_var ae, Ex (add_x_ctx z (mk_var ae) (E.to_cx env), app B.Eq ix1 (sh1 ix1))) in *)
      let tr = mk_var ae in
      let tt = fold_right2 (fun v a r -> Func (v,mk_var a,r)) vs a2s tr in
      Fcn (bs, ex) @@ e,
      CExists (a1s @ a2s @ [ae], CConj (cbs @ [ cex ; mk_eq (local_env, t, tt) ]))
  | Apply ({core = Internal op}, es) ->
      begin match op, es with
      | B.Cup, [e1 ; e2] ->
          let a1 = fresh_tyvar (E.to_cx env, e1) in
          let a2 = fresh_tyvar (E.to_cx env, e2) in
          let e1,ce1 = cg_expr mode env (Set (mk_var a1)) scx e1 in
          let e2,ce2 = cg_expr mode env (Set (mk_var a2)) scx e2 in
          mk_ex op [e1 ; e2],
          CExists ([a1;a2], CConj [ ce1 ; ce2 ;
            mk_eq (E.empty, t, Set (TyPlus [mk_var a1 ; mk_var a2]))
            ])
      | B.Cap, [e1 ; e2] ->
          let a1 = fresh_tyvar (E.to_cx env, e1) in
          let a2 = fresh_tyvar (E.to_cx env, e2) in
          let e1,ce1 = cg_expr mode env (Set (mk_var a1)) scx e1 in
          let e2,ce2 = cg_expr mode env (Set (mk_var a2)) scx e2 in
          mk_ex op [e1 ; e2],
          CExists ([a1;a2], CConj [ ce1 ; ce2 ;
            mk_eq (E.empty, t, Set (TyTimes [mk_var a1 ; mk_var a2]))
            ])
      | B.Setminus, [e1 ; e2] ->
          let a1 = fresh_tyvar (E.to_cx env, e1) in
          let a2 = fresh_tyvar (E.to_cx env, e2) in
          let e1,ce1 = cg_expr mode env (Set (mk_var a1)) scx e1 in
          let e2,ce2 = cg_expr mode env (Set (mk_var a2)) scx e2 in
          let z = fresh_tyterm () in
          let tx = TyPlus [mk_var a1 ; mk_var a2] in
          mk_ex op [e1 ; e2],
          CExists ([a1 ; a2], CConj [ ce1 ; ce2 ;
            mk_eq (E.empty, t, Set (Ref (z, tx,
            Ex (add_x_ctx z tx (E.to_cx env),
              mk_ex B.Notmem [ix1 ; sh_diff (sh1 e2)]
              (* mk_ex B.Conj [
                (* mk_ex B.Mem [ix1 ; sh1 e1] ; *)
                mk_ex B.Notmem [ix1 ; sh1 e2]
                ]  *)
                ))))
            ])
      | B.SUBSET, [s] ->
          let a = fresh_tyvar (E.to_cx env, s) in
          let s,cs = cg_expr mode env (Set (mk_var a)) scx s in
          mk_ex op [s],
          CExists ([a], CConj [ cs ; mk_eq (E.empty, t, Set (Set (mk_var a))) ])
      | B.UNION, [s] ->
          let s,cs = cg_expr mode env (Set t) scx s in
          mk_ex op [s], cs
      | B.DOMAIN, [f] ->
          let af = fresh_tyvar (E.to_cx env, f) in
          let f,cf = cg_expr mode env (mk_var af) scx f in
          mk_ex op [f],
          CExists ([af], CConj [ cf ; mk_eq (E.empty, t, Set (Tdom (mk_var af))) ])
      (** << env |- x..y : t >> ==
           \E a1,a2. /\ <<env |- x : a1 >> /\ env |- a1 <? Int
                     /\ <<env |- y : a2 >> /\ env |- a2 <? Int
                     /\ t == Set {z : Int | x <= z /\ z <= y} *)
      | B.Range, [x ; y] ->
(* Util.eprintf "<< ___ |- %a : %a >>" (E.pp_print_expr (E.to_scx env, Ctx.dot)) e E.ppt (env,t) ; *)
(* Util.eprintf "<< ___ |- %a : %a >>" (E.pp_print_expr (snd scx, Ctx.dot)) (sh_diff e) E.ppt (env,t) ; *)
          let ax = fresh_tyvar (E.to_cx env, x) in
          let ay = fresh_tyvar (E.to_cx env, y) in
          let x,cx = cg_expr mode env (mk_var ax) scx x in
          let y,cy = cg_expr mode env (mk_var ay) scx y in
          let z = fresh_tyterm () in
          mk_ex op [x ; y],
          CExists ([ax ; ay], CConj [
            cx ; mk_issub (E.empty, mk_var ax, Int) ;
            cy ; mk_issub (E.empty, mk_var ax, Int) ;
            mk_eq (E.empty, t, Set (Ref (z, Int,
              Ex (add_x_ctx z Int (E.to_cx env),
                lAnd [mk_ex B.Lteq [sh_diff (sh1 x) ; ix1] ;
                      mk_ex B.Lteq [ix1 ; sh_diff (sh1 y)] ]
              ))))
            ])
      | (B.Conj | B.Disj | B.Implies | B.Equiv), [e1 ; e2] ->
          let e1,ce1 = cg_expr mode env Bool scx e1 in
          let e2,ce2 = cg_expr mode env Bool scx e2 in
          mk_ex op [e1 ; e2],
          CConj [ ce1 ; ce2 ; mk_eq_bool t ]
      | B.Neg, [ex] ->
          let ex,c = cg_expr mode env Bool scx ex in
          mk_ex op [ex],
          CConj [c ; mk_eq_bool t]
      (** << env |- e1 = e2 : t >> ==
            \E a. /\ << env |- e1 : a >>
                  /\ << env |- e2 : a >>
                  /\ |- t == Bool *)
      | B.Eq, [e1 ; e2] when mode = TypHyp ->
          let a = fresh_tyvar (E.to_cx env, e1) in
          let e1,ce1 = cg_expr OnlySafe env (mk_var a) scx e1 in
          let e2,ce2 = cg_expr OnlySafe env (mk_var a) scx e2 in
          mk_ex op [e1 ; e2],
          CExists ([a], CConj [ ce1 ; ce2 ; mk_eq_bool t ])
      (** << env |- e1 = e2 : t >> ==
           \E a1,a2. /\ << env |- e1 : a1 >> /\ env |- a1 <? a1 ++ a2
                     /\ << env |- e2 : a2 >> /\ env |- a2 <? a1 ++ a2
                     /\ |- t == Bool *)
      | (B.Eq | B.Neq), [e1 ; e2] ->
          let a1 = fresh_tyvar (E.to_cx env, e1) in
          let a2 = fresh_tyvar (E.to_cx env, e2) in
          let e1,ce1 = cg_expr mode env (mk_var a1) scx e1 in
          let e2,ce2 = cg_expr mode env (mk_var a2) scx e2 in
          mk_ex op [e1 ; e2],
          CExists ([a1;a2], CConj [
            ce1 ; mk_issub (E.empty, mk_var a1, TyPlus [mk_var a1 ; mk_var a2]) ;
            ce2 ; mk_issub (E.empty, mk_var a2, TyPlus [mk_var a1 ; mk_var a2]) ;
            mk_eq_bool t
            ])
      | B.Mem, [e1 ; e2] when mode = TypHyp ->
          let a1 = fresh_tyvar (E.to_cx env, e1) in
          let a2 = fresh_tyvar (E.to_cx env, e2) in
          let e1,ce1 = cg_expr OnlySafe env (mk_var a1) scx e1 in
          let e2,ce2 = cg_expr OnlySafe env (Set (mk_var a2)) scx e2 in
          mk_ex op [e1 ; e2],
          CExists ([a1;a2], CConj [ ce1 ; ce2 ;
            mk_sub (E.empty, mk_var a1, mk_var a2) ;
            mk_eq_bool t
            ])
      | (B.Mem | B.Notmem), [e1 ; e2] ->
          let a1 = fresh_tyvar (E.to_cx env, e1) in
          let a2 = fresh_tyvar (E.to_cx env, e2) in
          let e1,ce1 = cg_expr mode env (mk_var a1) scx e1 in
          let e2,ce2 = cg_expr mode env (Set (mk_var a2)) scx e2 in
          mk_ex op [e1 ; e2],
          CExists ([a1;a2], CConj [ ce1 ; ce2 ;
            mk_issub (E.empty, mk_var a1, mk_var a2) ;
            mk_eq_bool t
            ])
      | B.Subseteq, [e1 ; e2] ->
          let a1 = fresh_tyvar (E.to_cx env, e1) in
          let a2 = fresh_tyvar (E.to_cx env, e2) in
          let e1,ce1 = cg_expr mode env (Set (mk_var a1)) scx e1 in
          let e2,ce2 = cg_expr mode env (Set (mk_var a2)) scx e2 in
          mk_ex op [e1 ; e2],
          CExists ([a1;a2], CConj [ ce1 ; ce2 ;
            (if mode = TypHyp then mk_sub else mk_issub) (E.empty, mk_var a1, mk_var a2) ;
            mk_eq_bool t
            ])
      | (B.Plus | B.Minus | B.Times | B.Exp |
         B.Ratio | B.Quotient | B.Remainder), [x ; y] ->
          let a1 = fresh_tyvar (E.to_cx env, x) in
          let a2 = fresh_tyvar (E.to_cx env, y) in
          let x,cx = cg_expr mode env (mk_var a1) scx x in
          let y,cy = cg_expr mode env (mk_var a2) scx y in
          let z = fresh_tyterm () in
          mk_ex op [x ; y],
          CExists ([a1;a2], CConj [ cx ; cy ;
            mk_issub (E.empty, mk_var a1, Int) ;
            mk_issub (E.empty, mk_var a2, Int) ;
            mk_eq (E.empty, t, Ref (z, Int,
              Ex (add_x_ctx z Int (E.to_cx env),
                mk_ex B.Eq [ix1 ; mk_ex op [sh_diff (sh1 x) ; sh_diff (sh1 y)]]
              ))) ;
            ])
      | B.Uminus, [{core = Num (n,"")}] ->
          let z = fresh_tyterm () in
          e, mk_eq (E.empty, t, Ref (z, Int,
            Ex (add_x_ctx z Int (E.to_cx env),
              mk_ex B.Eq [ix1 ; Num ("-"^n,"") @@ e ] )))
      | B.Uminus, [x] ->
          let a = fresh_tyvar (E.to_cx env, x) in
          let x,c = cg_expr mode env (mk_var a) scx x in
          let z = fresh_tyterm () in
          mk_ex op [x],
          CExists ([a], CConj [ c ;
            mk_issub (E.empty, mk_var a, Int) ;
            mk_eq (E.empty, t, Ref (z, Int,
              Ex (add_x_ctx z Int (E.to_cx env),
                mk_ex B.Eq [ix1 ; mk_ex op [sh_diff (sh1 x)]]
              )))
            ])
      | (B.Lteq | B.Lt | B.Gteq | B.Gt), [x ; y] ->
          let a1 = fresh_tyvar (E.to_cx env, x) in
          let a2 = fresh_tyvar (E.to_cx env, y) in
          let x,cx = cg_expr mode env (mk_var a1) scx x in
          let y,cy = cg_expr mode env (mk_var a2) scx y in
          mk_ex op [x ; y],
          CExists ([a1;a2], CConj [ cx ; cy ;
            mk_issub (E.empty, mk_var a1, Int) ;
            mk_issub (E.empty, mk_var a2, Int) ;
            mk_eq_bool t
          ])
      | _ ->
          Util.eprintf "!! Constraint generation. Expression not supported: %a"
            (E.pp_print_expr (snd scx, Ctx.dot)) e ;
          assert false
      end
  (* | Apply ({core = Opaque "boolify"} as op, [ex]) ->
      let a = fresh_tyvar (E.to_cx env, ex) in
      let ex,c = cg_expr mode env (mk_var a) scx ex in
      Apply (op, [ex]) @@ e, CExists ([a], c) *)
  | Apply ({core = Opaque "boolify"}, [{core = Ix n}]) ->
      e, mk_eq_bool t
  | Apply ({core = Opaque "boolify"}, [{core = Apply (f, es)}]) ->
      let ar = fresh_tyvar (E.to_cx env, e) in
      let a1s,t1s,es,cs = gen_tyvars mode env scx es in
      let a2s = List.map (fun e -> fresh_tyvar (E.to_cx env, e)) es in
      let t2s = List.map (fun a -> mk_var a) a2s in
      let f,cf = cg_expr mode env (fold_right (fun tv r -> Func ("", tv, r)) t2s (mk_var ar)) scx f in
      Apply (Opaque "boolify" %% [], [Apply (f, es) @@ e]) @@ e,
      CExists (ar::a1s @ a2s,
        CConj (cs @ (List.map2 (fun a b -> mk_issub (E.empty,a,b)) t1s t2s)
                  @ [ cf ; mk_eq_bool t ]))
  | Apply (f, es) ->
      let ar = fresh_tyvar (E.to_cx env, e) in
      let a1s,t1s,es,cs = gen_tyvars mode env scx es in
      let a2s = List.map (fun e -> fresh_tyvar (E.to_cx env, e)) es in
      let t2s = List.map (fun a -> mk_var a) a2s in
      let f,cf = cg_expr mode env (fold_right (fun tv r -> Func ("", tv, r)) t2s (mk_var ar)) scx f in
      Apply (f, es) @@ e,
      CExists (ar::a1s @ a2s,
        CConj (cs @ (List.map2 (fun a b -> mk_issub (E.empty,a,b)) t1s t2s)
                  @ [ cf ; mk_eq (E.empty, t, mk_var ar) ]))
  (** << env |- {} : t >> == \E a. t == {z : a | FALSE} *)
  | SetEnum [] ->
      let a = fresh_tyvar (E.to_cx env, e) in
      let tt = Ref ("", mk_var a, Ex ([], Internal B.FALSE %% [])) in
      e, CExists ([a], mk_eq (E.empty, t, Set tt ))
  (** << env |- {ex} : t >> == \E a. <<env |- ex : a >> /\ t == Set a *)
  | SetEnum [ex] ->
      let a = fresh_tyvar (E.to_cx env, ex) in
      let ex,cex = cg_expr mode env (mk_var a) scx ex in
      SetEnum [ex] @@ e,
      CExists ([a], CConj ([cex ; mk_eq (E.empty, t, Set (mk_var a)) ]))
  (** << env |- es : t >> ==
        \E a{1..n}. /\ <<env |- e_i : a_i >>_{i:1..n}
                    /\ t == Set (a1 ++ ... ++ an) *)
  | SetEnum es ->
      let a1s,t1s,es,cs = gen_tyvars mode env scx es in
      SetEnum es @@ e,
      CExists (a1s, CConj (cs @ [ mk_eq (E.empty, t, Set (TyPlus t1s)) ]))
  (** << env |- {v \in d : ex} : t >> ==
        \E a1,a2. /\ <<env |- d : Set a2 >>
                  /\ <<env, x:a1 |- ex : Bool>>
                  /\ env |- a1 <: a2
                  /\ t == Set {x : a1 | ex} *)
  | SetSt (v,d,ex) ->
      let a = fresh_tyvar (E.to_cx env, d) in
      let d,cd = cg_expr mode env (Set (mk_var a)) scx d in
      let scx' = adj scx (Fresh (v, Shape_expr, Constant, Bounded (d, Visible)) @@ v) in
      let local_env = E.adj empty (v.core, mk_var a) in
      let env' = env $! local_env in
      let ex,cex = cg_expr mode env' Bool scx' ex in
      let v = v <<< mk_var a in
      SetSt (v,d,ex) @@ e,
      CExists ([a], CConj [ cd ; cex ; mk_eq (local_env, t, Set (mk_var a)) ])
  | SetOf (ex, bs) ->
      let scx', bs, cbs, a1s, a2s, vs, env', local_env = cg_bounds env scx bs in
      let a2s = List.map Option.get a2s in
      let ae = fresh_tyvar (E.to_cx env', ex) in
      let ex,cex = cg_expr mode env' (Set (mk_var ae)) scx' ex in
      SetOf (ex, bs) @@ e,
      CExists (a1s @ a2s @ [ae],
        CConj (cbs @ [ cex ; mk_eq (local_env, t, Set (mk_var ae)) ]))
  | String _ ->
      let z = fresh_tyterm () in
      e, mk_eq (E.empty, t,
        Ref (z, Str, Ex (add_x_ctx z Str (E.to_cx env), app B.Eq ix1 e)))
  | Num _ ->
      let z = fresh_tyterm () in
      e, mk_eq (E.empty, t,
        Ref (z, Int, Ex (add_x_ctx z Int (E.to_cx env), app B.Eq ix1 e)))
  | Internal B.Int ->
      e, mk_eq (E.empty, t, Set Int)
  | Internal B.Nat ->
      let z = fresh_tyterm () in
      e, mk_eq (E.empty, t, Set (Ref (z, Int,
        Ex (add_x_ctx z Int (E.to_cx env),
          app B.Lteq (mk_num 0) ix1) )))
  | Internal B.STRING ->
      e, mk_eq (E.empty, t, Set Str)
  | Arrow (x,y) ->
      let a1 = fresh_tyvar (E.to_cx env, x) in
      let a2 = fresh_tyvar (E.to_cx env, y) in
      let x,cx = cg_expr mode env (Set (mk_var a1)) scx x in
      let y,cy = cg_expr mode env (Set (mk_var a2)) scx y in
      Arrow (x,y) @@ e,
      CExists ([a1;a2], CConj [ cx ; cy ;
        mk_eq (E.empty, t, Set (Func ("",mk_var a1,Tbase (mk_var a2))))
      ])
  | If (c,v,u) ->
      let a1 = fresh_tyvar (E.to_cx env, c) in
      let a2 = fresh_tyvar (E.to_cx env, v) in
      let a3 = fresh_tyvar (E.to_cx env, u) in
      let c,cc = cg_expr mode env (mk_var a1) scx c in
      let v,cv = cg_expr mode env (mk_var a2) scx v in
      let u,cu = cg_expr mode env (mk_var a3) scx u in
      If (c,v,u) @@ e,
      CExists ([a1;a2;a3], CConj [ cc ; cv ; cu ;
        mk_iseq (E.empty, mk_var a1, Bool) ;
        mk_iseq (E.empty, mk_var a2, mk_var a3) ;
        mk_eq (E.empty, t, mk_var a2)
      ])
  | Except (f, [([Except_apply a], b)]) ->
(* Util.eprintf "<< %a|- %a : %a >>" E.pp env (E.pp_print_expr (snd scx, Ctx.dot)) e E.pp (env,t) ; *)
      let a1 = fresh_tyvar (E.to_cx env, f) in                                   (** DOMAIN f *)
      let a2 = fresh_tyvar (E.to_cx env, a) in                                   (** f *)
      let a3 = fresh_tyvar (E.to_cx env, b) in                                   (** Codomain f *)
      let x = fresh_tyterm () in
      let z = fresh_tyterm () in
      (* let env' = E.adj env (x, Tdom (mk_var a1)) in *)
      let f,cf = cg_expr mode env (mk_var a1) scx f in
      let a,ca = cg_expr mode env (mk_var a2) scx a in
      let b,cb = cg_expr mode env (mk_var a3) scx b in
      (** [ix1] is [z], [ix2] is [x] *)
      (* let ex =
        let ix2 = Ix 2 %% [] in
        app B.Eq ix1
        ((If ((app B.Eq ix2 (sh1 (sh1 a))),
          (sh1 (sh1 b)),
          FcnApp (sh1 (sh1 f), [ix2]) %% [])) %% [])
      in *)
      (** [ix1] is [z], [ix_last] is [x] *)

      let ix_last = Ix (Deque.size (snd scx) + 2) %% [] in
      let e1 = apps B.Neg [app B.Eq ix_last (sh_diff (sh1 a))] in
      let e2 = app B.Conj (app B.Eq ix_last (sh_diff (sh1 a))) (app B.Eq ix1 (sh_diff (sh1 b))) in

      let tz = Tcod (mk_var a1) in

      (* let scx' = E.to_cx env
        |> add_x_ctx z (Tcod (mk_var a1))
        |> fun cx -> ((), to_scx cx)
      in *)

      (* let scx'' = E.to_cx env'
        |> add_x_ctx x (Tdom (mk_var a1))
        |> fun cx -> ((), to_scx cx)
      in *)
(* let t = Func (x, Tdom (mk_var a1), TyPlus
          [ Ref (z, tz, Ex (add_x_ctx z tz (E.to_cx env), e1)) ;
            Ref (z, Tbase tz, Ex (add_x_ctx z (Tbase tz) (E.to_cx env), e2)) ]) in
Util.eprintf "=== t: %a" E.ppt (env,t) ; *)
(* let t = Func (x, Tdom (mk_var a1),
          Ref (y, Tcod (mk_var a1),
            Ex ((E.to_cx env'), ex))) in *)
(* Util.eprintf "<< %a|- %a : %a >>" E.pp env (E.pp_print_expr (snd scx'', Ctx.dot)) ex E.ppt (env,t) ; *)

      Except (f, [([Except_apply a], b)]) @@ e,
      CExists ([a1;a2;a3], CConj [ cf; ca; cb;
        mk_issub (E.empty, Func (x, mk_var a2, mk_var a3), mk_var a1);
        (* mk_issub (E.empty', mk_var a2, Tdom (mk_var a1)); *)
        (* mk_issub (E.empty', mk_var a3, Tcod (mk_var a1)); *)
        (* mk_eq (E.empty, t, Func (x, Tdom (mk_var a1),
          Ref (z, tz, Ex (add_x_ctx z tz (E.to_cx env), ex))))                  (** Add also [x] to [cx] ? *) *)
        mk_eq (E.empty, t, Func (x, Tdom (mk_var a1), TyPlus
          [ Ref (z, tz, Ex (add_x_ctx z tz (E.to_cx env), e1)) ;
            Ref (z, Tbase tz, Ex (add_x_ctx z (Tbase tz) (E.to_cx env), e2)) ]
          ))
      ])

  | Tuple [] ->
      let tt = Ref ("",Top,Ex ([], Internal B.FALSE %% [])) in
      e, mk_eq (E.empty, t, Func ("", tt, tt))
  | Tuple es ->
      let aas,ats,es,cs = gen_tyvars mode env scx es in
      let i = fresh_tyterm () in
      let n = List.length es in
      let x1 = fresh_tyterm () in
      let cx' = add_x_ctx x1 Int (E.to_cx env) in
      let dom = Ref (x1, Int, Ex (cx', lAnd [
        mk_ex B.Lteq [mk_num 1 ; ix1] ;
        mk_ex B.Lteq [ix1 ; mk_num n] ] ))
      in
      let cod =
        let x2 = fresh_tyterm () in
        mapi begin fun i e ->
          let a = List.nth aas i in
          Ref (x2, mk_var a, Ex (add_x_ctx x2 (mk_var a) cx', lAnd [
            mk_ex B.Eq [sh1 ix1 ; mk_num (i+1)] ;
            mk_ex B.Eq [ix1 ; sh_diff (sh1 e)] ] ))
          end es
      in
      Tuple es @@ e,
      CExists (aas, CConj (cs @ [ mk_eq (E.empty, t, Func (i, dom, TyPlus cod)) ]))
  | Product es ->
      let aas,ats,es,cs = gen_tyvars ~sets:true mode env scx es in
      let i = fresh_tyterm () in
      let n = List.length es in
      let x1 = fresh_tyterm () in
      let x2 = fresh_tyterm () in
      let cx' = add_x_ctx x1 Int (E.to_cx env) in
      let dom = Ref (x1, Int, Ex (cx', lAnd [
        mk_ex B.Lteq [mk_num 1 ; ix1] ;
        mk_ex B.Lteq [ix1 ; mk_num n] ] ))
      in
      let cod = mapi begin fun i e ->
        let a = List.nth aas i in
        Ref (x2, mk_var a, Ex (add_x_ctx x2 (mk_var a) cx', lAnd [
          mk_ex B.Eq [sh1 ix1 ; mk_num (i+1)] ;
          mk_ex B.Eq [ix1 ; sh_diff (sh1 e)] ] ))
        end es
      in
      Tuple es @@ e,
      CExists (aas, CConj
        (cs @ [ mk_eq (E.empty, t, Set (Func (i, dom, TyPlus cod))) ]
      ))

  | Dot (ex,h) ->
      let a = fresh_tyvar (E.to_cx env, ex) in
      let ex,c = cg_expr mode env (mk_var a) scx ex in
      Dot (ex, h) @@ e,
      CExists ([a], CConj [ c ; mk_eq (E.empty, t, Rec_dot (mk_var a, h)) ])
  | Record res ->
      let hs,es = split res in
      let aas,ats,es,cs = gen_tyvars mode env scx es in
      let res = combine hs es in
      Record res @@ e,
      CExists (aas, CConj (cs @ [ mk_eq (E.empty, t, Rec (combine hs ats)) ] ))
  | Rect res ->
      let hs,es = split res in
      let aas,ats,es,cs = gen_tyvars ~sets:true mode env scx es in
      let res = combine hs es in
      Rect res @@ e,
      CExists (aas, CConj (cs @ [ mk_eq (E.empty, t, Set (Rec (combine hs ats))) ] ))

  (** TODO *)
  | Choose _ ->
      e, mk_eq (E.empty, t, Top)

  | Parens (ex,_) ->
      cg_expr mode env t scx ex
  | Internal B.BOOLEAN ->
      e, mk_eq (E.empty, t, Set Bool)

(** Constraint Generation for Boolean expressions [env |- (cx,e) : Bool] *)
  | Internal B.TRUE
  | Internal B.FALSE ->
      e, mk_eq_bool t

  (** Typing hypothesis [\A x \in S : op(x) \in T] *)
  (** << env |- (\A x \in S : op(x) \in T) : t >> ==
        \E a1,a2. /\ << env |- S : Set a1 >>
                  /\ << env |- T : Set a2 >>
									/\ << env |- op : a1 -> a2 >>
                  (* /\ |- env(op) == a1 -> a2  *)
                  /\ t == Bool *)
  | Quant (Forall, [h,k,Domain s1], {core = Apply ({core = Internal B.Mem},
    [{core = Apply ({core = Ix _} as op, [{core = Ix 1}])} ; s2])})
    when mode = TypHyp (* TOFIX: and [x \notin FV(T)] *) ->
      (* let _, bs, cbs, a1s, a2s, vs, _, local_env = cg_bounds env scx bs in *)
      (* let a2s = fold_left (fun r -> function Some a -> a :: r | None -> r) [] a2s in *)
      let a1 = fresh_tyvar (E.to_cx env, s1) in
      let a2 = fresh_tyvar (E.to_cx env, s2) in
      let s1,cs1 = cg_expr mode env (Set (mk_var a1)) scx s1 in
      let s2,cs2 = cg_expr mode env (Set (mk_var a2)) scx s2 in
      let op,cop = cg_expr mode env (Func ("", mk_var a1, mk_var a2)) scx op in
      let bs = [h,k,Domain s1] in
      let ex = app B.Mem (Apply (op, [ix1]) %% []) s2 in
      let ex = Quant (Forall, bs, ex) @@ e in
      ex, CExists ([a1;a2], CConj [ cs1 ; cs2 ; cop ; mk_eq_bool t ])

  (** Typing hypothesis [\A x : p(x) => op(x) \in S] *)
  (** << env |- (\A x : p(x) => op(x) \in S) : t >> ==
        \E a1,a2. /\ << env |- S : Set a2 >>
									/\ env(p) =?= a1 -> Bool
                  /\ env(op) == (_ : {x:a1 | p(x)}) -> a2
									(* /\ << env,x:a1 |- p(x) : Bool >>  *)
                  (* /\ << env,x:a1 |- op(x) : a2 >> *)
                  /\ t == Bool *)
  | Quant (Forall, [h, k, No_domain], {core = Apply ({core = Internal B.Implies}, [
			{core = Apply ({core = Opaque "boolify"}, [
				{core = Apply ({core = Ix n} as p, [{core = Ix 1}])}
				])};
			{core = Apply ({core = Internal B.Mem},
    		[{core = Apply ({core = Ix m} as q, [{core = Ix 1}])}; s])}
			])})
    when mode = TypHyp (* TOFIX: and [x \notin FV(s)] *) ->
			let app1 p = Apply (p, [ix1]) %% [] in
			let boolify e = Apply (Opaque "boolify" %% [], [e]) %% [] in
      let a1 = fresh_tyvar (E.to_cx env, p) in
      let a2 = fresh_tyvar (E.to_cx env, s) in
      let s,cs = cg_expr mode env (Set (mk_var a2)) scx s in
      let ip = Smtcommons.lookup_id (E.to_cx env) (n - 1) in
      let iq = Smtcommons.lookup_id (E.to_cx env) (m - 1) in
      let tp = E.find ip env in
      let tq = E.find iq env in
      let cp = mk_iseq (env, tp, Func ("", mk_var a1, Bool)) in
			let ta = Ref (h.core, mk_var a1, Ex (add_x_ctx h.core (mk_var a1) (E.to_cx env), app1 (sh_diff p))) in
      let cq = mk_eq (env, tq, Func ("", ta, mk_var a2)) in
      let bs = [h, k, No_domain] in
			let ex = app B.Implies (boolify (app1 p)) (app B.Mem (app1 q) s) in
      let ex = Quant (Forall, bs, ex) @@ e in
      ex, CExists ([a1;a2], CConj [ cp ; cs ; cq ; mk_eq_bool t ])

  (* | Quant (Forall, [h,k,No_domain], {core = Apply ({core = Internal B.Implies}, [
			{core = Apply ({core = Ix _}, [{core = Ix 1}])} as px ;
			{core = Apply ({core = Internal B.Mem},
    		[{core = Apply ({core = Ix _}, [{core = Ix 1}])} as opx ; s])}
			])})
    when mode = TypHyp (* TOFIX: and [x \notin FV(s)] *) ->
      let a1 = fresh_tyvar (E.to_cx env, px) in
      let a2 = fresh_tyvar (E.to_cx env, s) in
      let local_env = E.adj empty (h.core, mk_var a1) in
      let env' = env $! local_env in
      let px,cp = cg_expr mode env' Bool scx px in
      let s,cs = cg_expr mode env (Set (mk_var a2)) scx s in
			let opx,cop = cg_expr mode env' (mk_var a2) scx opx in
      let bs = [h,k,No_domain] in
      let ex = Quant (Forall, bs, app B.Implies px (app B.Mem opx s)) @@ e in
      ex, CExists ([a1;a2], CConj [ cp ; cs ; cop ; mk_eq_bool t ]) *)


  | Quant (q, bs, ex) ->
      let scx', bs, cbs, a1s, a2s, vs, env', local_env = cg_bounds env scx bs in
      let a2s = fold_left (fun r -> function Some a -> a :: r | None -> r) [] a2s in

      (** process [ex] to obtain more typing hypotheses *)
      let e,ces = match q, ex.core with
      (** (\A bs : hs => c) *)
      | Forall, Apply ({core = Internal B.Implies}, [{core = Apply ({core = Internal B.Conj}, hs) | List (And, hs)} ; c]) ->
          let ths, rest = List.partition (Smtcommons.is_typhyp (E.to_scx env)) hs in
          let ths, cths = split (List.map (cg_expr TypHyp env' Bool scx') ths) in
          let rest, crest = split (List.map (cg_expr OnlySafe env' Bool scx') rest) in
          let hs = ths @ rest in
          let ex = match hs with
            | [] -> c
            | hs -> app B.Implies (lAnd hs |> Smtcommons.flatten_conj) c
          in
          Quant (q, bs, ex) @@ e, (cths @ crest)
      (** (\E bs : hs) *)
      | Exists, (Apply ({core = Internal B.Conj}, hs) | List (And, hs)) ->
          let ths, rest = List.partition (Smtcommons.is_typhyp (E.to_scx env)) hs in
          let ths, cths = split (List.map (cg_expr TypHyp env' Bool scx') ths) in
          let rest, crest = split (List.map (cg_expr OnlySafe env' Bool scx') rest) in
          let hs = ths @ rest in
          let ex = lAnd hs |> Smtcommons.flatten_conj in
          Quant (q, bs, ex) @@ e, (cths @ crest)
      | _ ->
          let ex,cex = cg_expr OnlySafe env' Bool scx' ex in
          Quant (q, bs, ex) @@ e, [cex]
      in

      (* let ex,cex = cg_expr OnlySafe env' Bool scx' ex in
      Quant (q, bs, ex) @@ e,  *)
      e, CExists (a1s @ a2s, CConj (cbs @ ces @ [ mk_eq (local_env, t, Bool) ]))
  | List (b,es) ->
      let es,ces = split (List.map (cg_expr mode env Bool scx) es) in
      let e = List (b,es) @@ e in
      e, CConj (mk_eq_bool t :: ces)
  | Sequent sq ->
      (* let e,c = cg_expr mode env Bool scx (Smtcommons.unroll_seq sq) in
      e, CConj [mk_eq (E.empty, t, Bool) ; c] *)
      let _, sq, _, cc = cg_sequent env scx sq in
      Sequent sq @@ e, cc
  | _ ->
      Util.eprintf "!! Constraint generation. Expression not supported: %a"
        (E.pp_print_expr (snd scx, Ctx.dot)) e ;
      assert false

(** Given a list of expressions [es], in a context [scx], in a typing
    environment [env], generate:
    [aas] = [ ..., a_i, ... ]           type variable names
    [ats] = [ ..., TyVar a_i, ... ]     type variables for [es]
    [es]  = [ ..., e_i^t, ... ]         annotated expressions
    [cs]  = [ ..., << env |- e_i : a_i >>, ... ]  constraints
   *)
and gen_tyvars ?sets:(s=false) mode env scx es =
  let aas = List.map (fun e -> fresh_tyvar (E.to_cx env, e)) es in
  let ats = List.map (fun a -> mk_var a) aas in
  let es,cs = split (map2 (fun e a -> cg_expr mode env (if s then Set a else a) scx e) es ats) in
  aas, ats, es, cs

(** Given a list of bounds [bs], in a context [scx], in a typing
    environment [env], generate:
    [scx] = updated [scx]
    [bs]  = updated [bs]
    [cbs] = list of constraints in [bs]
    [a1s] = list of new type variable ids (alpha strings) for variables
    [a2s] = list of type variable ids for domains
    [vs]  = list of bound variables
    [env] = updated [env]
    [local_env] = new type assignements
   *)
and cg_bounds env scx bs =
  let bs = Smtcommons.unditto bs in
  let bs, cbs, a1s, a2s, vs =
    List.map begin
      fun (v,k,d) ->
        let a1 = fresh_tyvar ~id:("_"^v.core) (E.to_cx env, Opaque v.core @@ v) in
        match d with
        | Domain s ->
            let a2 = fresh_tyvar (E.to_cx env, s) in
            let s,cs = cg_expr OnlySafe env (Set (mk_var a2)) scx s in
              (v <<< mk_var a1, k, Domain s),
              [cs ; mk_sub (E.empty, mk_var a2, mk_var a1)],
              a1,
              Some a2, v.core
        | _ ->
            (v <<< mk_var a1, k, d), [], a1, None, v.core
            (* assert false *)
      end bs
    |> fold_left (fun (bs,cbs,a1s,a2s,vs) (b,cs,a1,a2,v) ->
         bs@[b], cbs @ cs, a1s@[a1], a2s@[a2], vs@[v])
         ([],[],[],[],[])
  in
  let hs = List.map begin
    fun (v, k, _) -> Fresh (v, Shape_expr, k, Unbounded) @@ v
  end bs in
  (* let env = fold_left2 (fun e v a1 -> E.adj e (v,mk_var a1)) env vs a1s in *)
  let local_env = E.adjs empty (map2 (fun v a -> v, mk_var a) vs a1s) in
  let env' = env $! local_env in
  (adjs scx hs, bs, cbs, a1s, a2s, vs, env', local_env)

and cg_hyp (env:E.t) scx h =
(* let ph cx ff h = ignore (E.pp_print_hyp cx ff h) in *)
  match h.core with
  | Fact (e, Visible, tm) ->
(* Util.eprintf "<< [%d-%d] %a|- %a : Bool >>." (Dq.size env) (Dq.size (snd scx)) E.pp env (ph (E.to_scx env, Ctx.dot)) h ; *)
      let mode = if Smtcommons.is_typhyp (E.to_scx env) e then TypHyp else OnlySafe in
      let e, ce = cg_expr mode env Bool scx e in
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
(* let ph cx ff h = ignore (E.pp_print_hyp cx ff h) in Util.eprintf "++ [%d-%d] %a|- %a : Bool >>" (Dq.size env) (Dq.size (snd scx)) E.pp env (ph (snd scx, Ctx.dot)) h ; *)
(* let ph cx ff h = ignore (E.pp_print_hyp cx ff h) in Util.eprintf "++ [%d-%d] %a|- %a : Bool >>" (Dq.size env) (Dq.size (snd scx)) E.pp env (ph (E.to_scx env, Ctx.dot)) h ; *)
(* let ph cx ff h = ignore (E.pp_print_hyp cx ff h) in Util.eprintf "++ [%d-%d] |- %a : Bool >>" (Dq.size env) (Dq.size (snd scx)) (ph (E.to_scx env, Ctx.dot)) h ; *)
      let _, h, env, v, c = cg_hyp env scx h in
(* Smtcommons.ifprint 2 "cg_hyps tvar: %s" (Option.default "--" v) ; *)
      let _, hs, env, vs, cs = cg_hyps env scx hs in
      let vs = match v with Some v -> v::vs | None -> vs in
      let cs = match c with Some c -> c::cs | None -> cs in
      (scx, Dq.cons h hs, env, vs, cs)

and cg_sequent env scx sq =
  (* let scx = E.to_scx env in *)
(* Smtcommons.ifprint 3 "<< [%d] %a@, |- %a : Bool >>" (Dq.size env) E.pp env Fu.pp_print_minimal (Fu.Big (fun ff -> ignore (E.pp_print_sequent (sq.context, Ctx.dot) ff sq))) ; *)
(* Smtcommons.ifprint 3 "<< [%d] %a@, |- %a : Bool >>" (Dq.size env) E.pp env Fu.pp_print_minimal (Fu.Big (fun ff -> ignore (E.pp_print_sequent (snd scx, Ctx.dot) ff sq))) ; *)
  (* let scx, hs, env, vs, chs = cg_hyps env ((),Dq.empty) sq.context in *)
  let scx, hs, env, vs, chs = cg_hyps env scx sq.context in
(* Smtcommons.ifprint 3 "<< [%d] %a@, |- %a : Bool >>" (Dq.size env) E.pp env Fu.pp_print_minimal (Fu.Big (fun ff -> ignore (E.pp_print_sequent (sq.context, Ctx.dot) ff sq))) ; *)
  let c, cc = cg_expr OnlySafe env Bool scx sq.active in
  let cc = C.mk_ex (vs, chs @ [cc]) in
  (* let cc = C.mk_ex (List.map (fun v -> "a_"^v) fvs, chs @ [cc]) in *)
  (* let cc = C.mk_cs (chs @ [cc]) in *)
  (scx, { context = hs ; active = c }, env, cc)

let cg sq =
  let tx = Sys.time () in
(* Smtcommons.ifprint 3 "sq: %a" Fu.pp_print_minimal (Fu.Big (fun ff -> ignore (E.pp_print_sequent (sq.context, Ctx.dot) ff sq))); *)
  let fvs = Smtcommons.fv ((),sq.context) sq in
  let fvs = Smtcommons.subtract fvs "boolify" in
  (* let env0,tvars = E.mk fvs in *)
  (* let final_env, _ = Dq.fold_lft (fun e h -> e $$ (h,None)) E.empty sq.context in *)
  (* let offset = Dq.size final_env in *)
  let _,sq,env,c = cg_sequent E.empty ((),sq.context) sq in
  let c = C.mk_ex (fvs, [c]) in
  Smtcommons.ifprint 2 "** Constraint generation in %5.3fs.%!" (Sys.time() -. tx) ;
  Smtcommons.ifprint 3 "@[<hov2>C_0 == @[<v>%a@] ||-@ @[<hov>%a@]@]" E.pp env C.pp (env,c) ;
  (* Smtcommons.ifprint 3 "   Constraint length = %d" (C.c_length c) ; *)
(* Smtcommons.ifprint 3 "sq': %a" Fu.pp_print_minimal (Fu.Big (fun ff -> ignore (E.pp_print_sequent (sq.context, Ctx.dot) ff sq))); *)
  (sq, env, c)
