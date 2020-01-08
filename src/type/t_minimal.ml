(*
 * type/minimal.ml --- minimal typing
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

open Ext
open Expr.T
open Property

open T_t

module B = Builtin


(* {3 Utils} *)

let typebad ?at =
  Errors.bug ?at "Typechecking error"

let get_atom = function TAtom a -> a | _ -> invalid_arg "MinRecon.get_atom"

let mk_atom a = TAtom a

(* Make a type from a {!Expr.T.shape} *)
let from_shp = function
  | Shape_expr -> mk_atom TAtSet
  | Shape_op n ->
      let ty1 = TProd (List.init n (fun _ -> mk_atom TAtSet)) in
      let ty2 = mk_atom TAtSet in
      TArrow (ty1, ty2)

let mk_eq e1 e2 =
  Apply (Internal Builtin.Eq %% [], [ e1 ; e2 ]) %% []

(* Make an expression of sort [bool] from anything;
 * Last argument is a {!Type.T.ty_atom} object, representing
 * the sort of the input expression. *)
let mk_formula e = function
  | TBool  -> e
  | TAtSet -> mk_eq e (SetEnum [] %% [])
  | TInt   -> mk_eq e (Num ("0", "") %% [])
  | TReal  -> mk_eq e (Num ("0", "0") %% [])
  | TStr   -> mk_eq e (String "foo" %% [])

(* Make an expression of sort [set] from anything, like {!mk_formula} above
 * This inserts opaque coercion operators *)
let mk_set e = function
  | TAtSet -> e
  | TBool  -> Apply (Opaque "BoolToSet" %% [], [ e ]) @@ e
  | TInt   -> Apply (Opaque "IntToSet" %% [], [ e ]) @@ e
  | TReal  -> Apply (Opaque "RealToSet" %% [], [ e ]) @@ e
  | TStr   -> Apply (Opaque "StrToSet" %% [], [ e ]) @@ e


(* {3 Main} *)

type cx = ty Ctx.t

let adj cx v ty =
  let v = type_annot v ty in
  (v, Ctx.adj cx v.core ty)

let adjs cx vs tys =
  let vs, cx = List.fold_left begin fun (vs, cx) (v, ty) ->
    let v, cx = adj cx v ty in
    (v :: vs, cx)
  end ([], cx) (List.combine vs tys) in
  (List.rev vs, cx)

let bump cx = snd (adj cx ("" %% []) TUnknown)

let lookup_ty cx n =
  let _, ty = Ctx.index cx n in
  Option.default TUnknown ty

(** Annotations are placed here:
      - Bound variables in Quant, Tquant, Choose, SetSt, SetOf, Fcn;
      - Variables of Fresh, Flex;
      - Defined operators in Defn-Operator.
*)
let rec expr scx oe =
  match oe.core with
  | Ix n ->
      let ty = lookup_ty scx n in
      Ix n @@ oe, ty
  | Opaque _ ->
      Errors.bug ~at:oe "Type.MinRecon.expr"
  | Internal (B.TRUE | B.FALSE) as op ->
      op @@ oe, mk_atom TBool
  | Apply ({ core = Internal (B.Implies | B.Equiv | B.Conj | B.Disj) } as op, [ e ; f ]) ->
      let e, ty1 = expr scx e in
      let f, ty2 = expr scx f in
      Apply (op, [ mk_formula e (get_atom ty1) ; mk_formula f (get_atom ty2) ]) @@ oe, mk_atom TBool
  | Apply ({ core = Internal B.Neg } as op, [ e ]) ->
      let e, ty = expr scx e in
      Apply (op, [ mk_formula e (get_atom ty) ]) @@ oe, mk_atom TBool
  | Apply ({ core = Internal (B.Eq | B.Neq) } as op, [ e ; f ]) ->
      let e, ty1 = expr scx e in
      let f, ty2 = expr scx f in
      if ty1 = ty2 then
        Apply (op, [ e ; f ]) @@ oe, ty1
      else
        Apply (op, [ mk_set e (get_atom ty1) ; mk_set e (get_atom ty2) ]) @@ oe, mk_atom TAtSet
  | Internal (B.STRING | B.BOOLEAN | B.Nat | B.Int | B.Real) as op ->
      op @@ oe, mk_atom TAtSet
  | Apply ({ core = Internal (B.SUBSET | B.UNION | B.DOMAIN) } as op, [ e ]) ->
      let e, ty = expr scx e in
      Apply (op, [ mk_set e (get_atom ty) ]) @@ oe, mk_atom TAtSet
  | Apply ({ core = Internal (B.Subseteq | B.Mem | B.Notmem) } as op, [ e ; f ]) ->
      let e, ty1 = expr scx e in
      let f, ty2 = expr scx f in
      Apply (op, [ mk_set e (get_atom ty1) ; mk_set f (get_atom ty2) ]) @@ oe, mk_atom TBool
  | Apply ({ core = Internal (B.Setminus | B.Cap | B.Cup) } as op, [ e ; f ]) ->
      let e, ty1 = expr scx e in
      let f, ty2 = expr scx f in
      Apply (op, [ mk_set e (get_atom ty1) ; mk_set f (get_atom ty2) ]) @@ oe, mk_atom TAtSet
  | Apply ({ core = Internal (B.Plus | B.Minus | B.Times | B.Ratio | B.Quotient | B.Remainder | B.Exp as b) } as op, [ e ; f ]) ->
      let e, ty1 = expr scx e in
      let f, ty2 = expr scx f in
      if ty1 = mk_atom TInt && ty2 = mk_atom TInt then
        Apply (op, [ e ; f ]) @@ oe, mk_atom TInt
      else
        let s =
          match b with
          | B.Plus -> "arith__plus"
          | B.Minus -> "arith__minus"
          | B.Times -> "arith__ratio"
          | B.Quotient -> "arith__quotient"
          | B.Remainder -> "arith__remainder"
          | B.Exp -> "arith__exp"
          | _ -> assert false
        in
        Apply (Opaque s @@ op, [ mk_set e (get_atom ty1) ; mk_set f (get_atom ty2) ]) @@ oe, mk_atom TAtSet
  | Apply ({ core = Internal B.Uminus } as op, [ e ; f ]) ->
      let e, ty = expr scx e in
      if ty = mk_atom TInt then
        Apply (op, [ e ]) @@ oe, mk_atom TInt
      else
        let s = "arith__uminus" in
        Apply (Opaque s @@ op, [ mk_set e (get_atom ty) ]) @@ oe, mk_atom TAtSet
  | Internal B.Infinity as op ->
      op @@ oe, mk_atom TReal
  | Apply ({ core = Internal (B.Lteq | B.Lt | B.Gteq | B.Gt as b) } as op, [ e ; f ]) ->
      let e, ty1 = expr scx e in
      let f, ty2 = expr scx f in
      if ty1 = mk_atom TInt && ty2 = mk_atom TInt then
        Apply (op, [ e ; f ]) @@ oe, mk_atom TBool
      else
        let s =
          match b with
          | B.Lteq -> "arith__lteq"
          | B.Lt -> "arith__lt"
          | B.Gteq -> "arith__gteq"
          | B.Gt -> "arith__gt"
          | _ -> assert false
        in
        Apply (Opaque s @@ op, [ mk_set e (get_atom ty1) ; mk_set f (get_atom ty2) ]) @@ oe, mk_atom TBool
  | Apply ({ core = Internal B.Range } as op, [ e ; f ]) ->
      let e, ty1 = expr scx e in
      let f, ty2 = expr scx f in
      if ty1 = mk_atom TInt && ty2 = mk_atom TInt then
        Apply (op, [ e ; f ]) @@ oe, mk_atom TAtSet
      else
        let s = "arith__range" in
        Apply (Opaque s @@ op, [ mk_set e (get_atom ty1) ; mk_set f (get_atom ty2) ]) @@ oe, mk_atom TAtSet
  | Internal b ->
      Errors.bug ~at:oe "Type.MinRecon.expr"
  | Lambda (vs, e) ->
      let scx, vs, tys1 =
        List.fold_left begin fun (scx, vs, tys) (h, shp) ->
          let ty = from_shp shp in
          let h, scx = adj scx h ty in
          let v = (h, shp) in
          (scx, v :: vs, ty :: tys)
        end (scx, [], []) vs
      in
      let vs = List.rev vs in
      let ty1 = TProd (List.rev tys1) in
      let e, ty2 = expr scx e in
      Lambda (vs, e) @@ oe, TArrow (ty1, ty2)
  | Bang _ ->
      Errors.bug ~at:oe "Type.MinRecon.expr"
  | Sequent sq ->
      let _, sq, ty = sequent scx sq in
      Sequent sq @@ oe, ty
  | Apply (op, args) ->
      let op, ty1 = expr scx op in
      let arg_tys2 =
        List.map (expr scx) args
        (* Do not split before inserting coercions *)
      in
      let args, ty3 =
        match ty1, arg_tys2 with
        | TArrow (TProd tys11, ty12), arg_tys2 ->
            let args = List.map2 begin fun ty1 (arg, ty2) ->
              match ty1 with
              | TAtom TAtSet -> mk_set arg (get_atom ty2)
              | TAtom TBool -> mk_formula arg (get_atom ty2)
              | _ -> typebad ~at:oe
            end tys11 arg_tys2 in
            args, ty12
        | TArrow (ty11, ty12), [ arg, ty2 ] ->
            let f =
              match get_atom ty11 with
              | TAtSet -> mk_set
              | TBool -> mk_formula
              | _ -> typebad ~at:oe
            in
            [ f arg (get_atom ty2) ], ty12
        | ty1, [] ->
            [], ty1
        | _ ->
            typebad ~at:oe
      in
      Apply (op, args) @@ oe, ty3
  | With (e, m) ->
      let e, ty = expr scx e in
      With (e, m) @@ oe, ty
  | If (e, f, g) ->
      let e, ty1 = expr scx e in
      let f, ty2 = expr scx f in
      let g, ty3 = expr scx g in
      begin match ty1 with
      | TAtom TBool -> ()
      | _ -> typebad ~at:oe
      end;
      (* If f and g have the same type, the if-expression has that type;
       * otherwise f and g are coerced to [set]. *)
      let f, g, ty4 =
        if ty2 = ty3 then
          f, g, ty2
        else
          mk_set f (get_atom ty2), mk_set g (get_atom ty3), mk_atom TAtSet
      in
      If (e, f, g) @@ oe, ty4
  | List (bl, es) ->
      let es = List.map begin fun e ->
        let e, ty = expr scx e in
        mk_formula e (get_atom ty)
      end es in
      List (bl, es) @@ oe, mk_atom TBool
  | Let (ds, e) ->
      let scx, ds, _ = defns scx ds in
      let e, ty = expr scx e in
      Let (ds, e) @@ oe, ty
  | Quant (q, bs, e) ->
      let scx, bs, _ = bounds scx bs in
      let e, ty = expr scx e in
      Quant (q, bs, mk_formula e (get_atom ty)) @@ oe, mk_atom TBool
  | Tquant (q, hs, e) ->
      let scx, hs = List.fold_left begin fun (scx, hs) h ->
        let h, scx = adj scx h (mk_atom TAtSet) in
        scx, h :: hs
      end (scx, []) hs in
      let hs = List.rev hs in
      let e, ty = expr scx e in
      Tquant (q, hs, mk_formula e (get_atom ty)) @@ oe, mk_atom TBool
  | Choose (h, hdom, e) ->
      let hdom =
        match hdom with
        | None -> None
        | Some dom ->
            let dom, ty = expr scx dom in
            Some (mk_set dom (get_atom ty))
      in
      let h, scx = adj scx h (mk_atom TAtSet) in
      let e, ty = expr scx e in
      Choose (h, hdom, mk_formula e (get_atom ty)) @@ oe, mk_atom TBool
  | SetSt (h, e1, e2) ->
      let e1, ty1 = expr scx e1 in
      let h, scx = adj scx h (mk_atom TAtSet) in
      let e2, ty2 = expr scx e2 in
      SetSt (h, mk_set e1 (get_atom ty1), mk_formula e2 (get_atom ty2)) @@ oe, mk_atom TAtSet
  | SetOf (e, bs) ->
      let scx, bs, _ = bounds scx bs in
      let e, ty = expr scx e in
      SetOf (mk_set e (get_atom ty), bs) @@ oe, mk_atom TAtSet
  | SetEnum es ->
      let es = List.map begin fun e ->
        let e, ty = expr scx e in
        mk_set e (get_atom ty)
      end es in
      SetEnum es @@ oe, mk_atom TAtSet
  | Product es ->
      let es = List.map begin fun e ->
        let e, ty = expr scx e in
        mk_set e (get_atom ty)
      end es in
      Product es @@ oe, mk_atom TAtSet
  | Tuple es ->
      let es = List.map begin fun e ->
        let e, ty = expr scx e in
        mk_set e (get_atom ty)
      end es in
      Tuple es @@ oe, mk_atom TAtSet
  | Fcn (bs, e) ->
      let scx, bs, _ = bounds scx bs in
      let e, ty = expr scx e in
      Fcn (bs, mk_set e (get_atom ty)) @@ oe, mk_atom TAtSet
  | FcnApp (e, es) ->
      let e, ty = expr scx e in
      let es = List.map begin fun e ->
        let e, ty = expr scx e in
        mk_set e (get_atom ty)
      end es in
      FcnApp (mk_set e (get_atom ty), es) @@ oe, mk_atom TAtSet
  | Arrow (e1, e2) ->
      let e1, ty1 = expr scx e1 in
      let e2, ty2 = expr scx e2 in
      Arrow (mk_set e1 (get_atom ty1), mk_set e2 (get_atom ty2)) @@ oe, mk_atom TAtSet
  | Rect fs ->
      let fs = List.map begin fun (f, e) ->
        let e, ty = expr scx e in
        (f, mk_set e (get_atom ty))
      end fs in
      Rect fs @@ oe, mk_atom TAtSet
  | Record fs ->
      let fs = List.map begin fun (f, e) ->
        let e, ty = expr scx e in
        (f, mk_set e (get_atom ty))
      end fs in
      Record fs @@ oe, mk_atom TAtSet
  | Except (e, exs) ->
      let exs, _ = List.map (exspec scx) exs |> List.split in
      let e, ty = expr scx e in
      Except (mk_set e (get_atom ty), exs) @@ oe, mk_atom TAtSet
  | Dot (e, s) ->
      let e, ty = expr scx e in
      Dot (mk_set e (get_atom ty), s) @@ oe, mk_atom TAtSet
  | Sub (m, e1, e2) ->
      let e1, ty1 = expr scx e1 in
      let e2, ty2 = expr scx e2 in
      Sub (m, mk_set e1 (get_atom ty1), mk_set e2 (get_atom ty2)) @@ oe, mk_atom TBool
  | Tsub (m, e1, e2) ->
      let e1, ty1 = expr scx e1 in
      let e2, ty2 = expr scx e2 in
      Tsub (m, mk_set e1 (get_atom ty1), mk_set e2 (get_atom ty2)) @@ oe, mk_atom TBool
  | Fair (f, e1, e2) ->
      let e1, ty1 = expr scx e1 in
      let e2, ty2 = expr scx e2 in
      Fair (f, mk_set e1 (get_atom ty1), mk_set e2 (get_atom ty2)) @@ oe, mk_atom TBool
  | Case (ps, o) ->
      let ps, tys =
        List.map begin fun (p, e) ->
          let p, ty1 = expr scx p in
          let e, ty2 = expr scx e in
          (mk_formula p (get_atom ty1), e), ty2
        end ps
        |> List.split
      in
      let o, o_ty =
        match o with
        | None -> None, None
        | Some e ->
            let e, ty = expr scx e in
            Some e, Some ty
      in
      (* Like for if-expressions, the branches are coerced to [set]
       * if their types differ. All types must be computed first. *)
      let ps, o, ty =
        let tty = List.hd tys in
        let ttys =
          match o_ty with
          | None -> List.tl tys
          | Some ty -> ty :: List.tl tys
        in
        if List.for_all ((=) tty) ttys then
          ps, o, tty
        else
          let ps = List.map2 begin fun (p, e) ty ->
            (p, mk_set e (get_atom ty))
          end ps tys in
          let o = Option.map begin fun e ->
            let ty = Option.get o_ty in
            mk_set e (get_atom ty)
          end o in
          ps, o, mk_atom TAtSet
      in
      Case (ps, o) @@ oe, ty
  | String s ->
      String s @@ oe, mk_atom TStr
  | Num (m, "") ->
      Num (m, "") @@ oe, mk_atom TInt
  | Num (m, n) ->
      Num (m, n) @@ oe, mk_atom TReal
  | At _ ->
      Errors.bug ~at:oe "Type.MinRecon.expr"
  | Parens (e, pf) ->
      let e, ty = expr scx e in
      Parens (e, pf) @@ oe, ty

(* [sequent scx sq] always return the type [bool], inserting a cast if necessary. *)
and sequent scx sq =
  let scx, hs, _ = hyps scx sq.context in
  let g, _ = expr scx sq.active in
  scx, { context = hs ; active = g }, mk_atom TBool

and exspec scx (exps, e) =
  let exps = List.map begin function
    | Except_dot s -> Except_dot s
    | Except_apply e ->
        let e, ty = expr scx e in
        Except_apply (mk_set e (get_atom ty))
  end exps in
  let e, ty = expr scx e in
  (exps, mk_set e (get_atom ty)), TUnknown

(* [bounds scx bs] return the type [?] but annotates all variables with [set]. *)
and bounds scx bs =
  let scx, bs =
    List.fold_left begin fun (scx', bs) (h, k, dom) ->
      let dom =
        match dom with
        | Domain d ->
            let d, ty = expr scx d in
            Domain (mk_set d (get_atom ty))
        | _ -> dom
      in
      let h, scx' = adj scx' h (mk_atom TAtSet) in
      let b = (h, k, dom) in
      (scx', b :: bs)
    end (scx, []) bs
  in
  let bs = List.rev bs in
  scx, bs, TUnknown

and bound scx b =
  match bounds scx [b] with
  | scx, [b], ty -> scx, b, ty
  | _, _, _ -> assert false

(* [defn scx df] always return the type [?].
 * A defined operator can be typed with [t1 X .. X tn -> s] where each [ti]
 * is of the form [s1 X .. X sn -> s] and [s] ranges over [{ bool, set }]. *)
and defn scx df =
  match df.core with
  | Recursive (h, shp) ->
      let ty = from_shp shp in
      let h, scx = adj scx h ty in
      scx, Recursive (h, shp) @@ df, TUnknown
  | Operator (h, e) ->
      let e, ty = expr scx e in
      let h, scx = adj scx h ty in
      scx, Operator (h, e) @@ df, TUnknown
  | Instance (h, i) ->
      Errors.bug ~at:df "Type.MinRecon.defn"
  | Bpragma (h, e, args) ->
      let e, ty = expr scx e in
      let h, scx = adj scx h ty in
      scx, Bpragma (h, e, args) @@ df, TUnknown

and defns scx dfs =
  match dfs with
  | [] -> scx, [], TUnknown
  | df :: dfs ->
      let scx, df, _ = defn scx df in
      let scx, dfs, _ = defns scx dfs in
      scx, df :: dfs, TUnknown

(* [hyp scx h] always return the type [?].
 * Facts are cast to [bool] if necessary;
 * types are attached to declared operators, constants, variables. *)
and hyp scx h =
  match h.core with
  | Fresh (v, shp, k, hdom) ->
      let hdom =
        match hdom with
        | Unbounded -> Unbounded
        | Bounded (dom, vis) ->
            let dom, ty = expr scx dom in
            Bounded (mk_set dom (get_atom ty), vis)
      in
      let ty =
        match shp with
        | Shape_expr -> ty_aset
        | Shape_op n ->
            if n = 1 then TArrow (ty_aset, ty_aset)
            else TArrow (TProd (List.init n (fun _ -> ty_aset)), ty_aset)
      in
      let v, scx = adj scx v ty in
      let h = Fresh (v, shp, k, hdom) @@ h in
      scx, h, TUnknown
  | Flex v ->
      let ty = ty_aset in
      let v, scx = adj scx v ty in
      let h = Flex v @@ h in
      scx, h, TUnknown
  | Defn (df, wd, vis, ex) ->
      let scx, df, _ = defn scx df in
      let h = Defn (df, wd, vis, ex) @@ h in
      scx, h, TUnknown
  | Fact (e, vis, tm) ->
      let e, ty = expr scx e in
      let e = mk_formula e (get_atom ty) in
      let scx = bump scx in
      let h = Fact (e, vis, tm) @@ h in
      scx, h, TUnknown

(* [hyps scx hs] always return the type [?]. *)
and hyps scx hs =
  match Deque.front hs with
  | None -> scx, Deque.empty, TUnknown
  | Some (h, hs) ->
      let scx, h, _ = hyp scx h in
      let scx, hs, _ = hyps scx hs in
      scx, Deque.cons h hs, TUnknown

let min_reconstruct sq =
  let scx = Ctx.dot in
  let _, sq, _ = sequent scx sq in
  sq
