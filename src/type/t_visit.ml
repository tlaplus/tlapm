(*
 * type/visit.ml --- visitors with syntactic typecheck
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

open Ext
open Property

open Expr.T
open T_t

module B = Builtin


(* {3 Helpers} *)

let error ?at mssg =
  let mssg = "Type.Visit: " ^ mssg in
  Errors.bug ?at mssg


(* {3 Context} *)

type 's scx = 's * hyp Deque.dq

let adj (s, cx) h =
  (s, Deque.snoc cx h)

let rec adjs scx = function
  | [] -> scx
  | h :: hs ->
      adjs (adj scx h) hs


let lookup_hyp (_, hx) n =
  Option.get (Deque.nth ~backwards:true hx (n - 1))

let lookup_ty scx n =
  let h = lookup_hyp scx n in
  let v = hyp_hint h in
  try
    match query v Props.type_prop with
    | Some ty0 -> ty0
    | None ->
        match query v Props.tsch_prop with
        | Some (TSch ([], [], ty0)) -> ty0
        | _ -> failwith ""
  with _ ->
    error ~at:v "Cannot find type0 annotation"

let lookup_ty_arg scx n =
  let h = lookup_hyp scx n in
  let v = hyp_hint h in
  try
    match query v Props.targ_prop with
    | Some ty1 -> ty1
    | None ->
        match query v Props.type_prop with
        | Some ty0 -> TRg ty0
        | None ->
            match query v Props.tsch_prop with
            | Some (TSch ([], [], ty0)) ->
                TRg ty0
            | Some (TSch ([], ty1s, ty0)) ->
                let ty0s = List.map (function TRg ty0 -> ty0 | _ -> failwith "") ty1s in
                TOp (ty0s, ty0)
            | _ -> failwith ""
  with _ ->
    error ~at:v "Cannot find type1 annotation"

let lookup_ty_sch scx n =
  let h = lookup_hyp scx n in
  let v = hyp_hint h in
  try
    match query v Props.tsch_prop with
    | Some ty2 -> ty2
    | None ->
        match query v Props.type_prop with
        | Some ty0 -> TSch ([], [], ty0)
        | None -> failwith ""
  with _ ->
    error ~at:v "Cannot find type2 annotation"


class virtual ['s, 'a] foldmap = object (self : 'self)

  method expr (scx : 's scx) a oe =

    if has oe Props.ucast_prop then
      let oe = remove oe Props.ucast_prop in
      let a, oe, _ = self#expr scx a oe in
      (a, assign oe Props.ucast_prop (), TAtom TU)
    else

    if has oe Props.bproj_prop then
      let oe = remove oe Props.bproj_prop in
      let a, oe, _ = self#expr scx a oe in
      (a, assign oe Props.bproj_prop (), TAtom TBool)
    else

    match oe.core with
    | Ix n ->
        let ty = lookup_ty scx n in
        (a, Ix n @@ oe, ty)
    | Opaque o ->
        let ty = get oe Props.type_prop in
        (a, Opaque o @@ oe, ty)
    | Internal b ->
        let a, oe, tsch = self#eopr scx a oe in
        let ty =
          match tsch with
          | TSch ([], [], ty) -> ty
          | _ -> error "Expected constant builtin"
        in
        (a, Internal b @@ oe, ty)
    | String s ->
        (a, String s @@ oe, TAtom TStr)
    | Num (m, n) ->
        let ty =
          match n with
          | "" -> TAtom TInt
          | _ -> TAtom TReal
        in
        (a, Num (m, n) @@ oe, ty)
    | Apply (op, es) ->
        let a, op, tsch = self#eopr scx a op in
        let a, es, targs = List.fold_left begin fun (a, es, targs) e ->
          let a, e, targ = self#earg scx a e in
          (a, e :: es, targ :: targs)
        end (a, [], []) es in
        let es = List.rev es in
        let targs2 = List.rev targs in
        let ty =
          match tsch with
          | TSch ([], targs1, ty) ->
              List.iter2 check_ty1_eq targs1 targs2;
              ty
          | _ -> error ~at:oe "Polymorphism is not checked" (* FIXME *)
        in
        (a, Apply (op, es) @@ oe, ty)
    | Sequent sq ->
        let _, a, sq = self#sequent scx a sq in
        (a, Sequent sq @@ oe, TAtom TBool)
    | With (e, m) ->
        let a, e, ty = self#expr scx a e in
        (a, With (e, m) @@ oe, ty)
    | Let (ds, e) ->
        let scx, a, ds = self#defns scx a ds in
        let a, e, ty = self#expr scx a e in
        (a, Let (ds, e) @@ oe, ty)
    | If (e, f, g) ->
        let a, e, ty1 = self#expr scx a e in
        let a, f, ty2 = self#expr scx a f in
        let a, g, ty3 = self#expr scx a g in
        check_ty0_eq ty1 (TAtom TBool);
        check_ty0_eq ty3 ty2;
        (a, If (e, f, g) @@ oe, ty2)
    | List (Refs, [e]) ->
        let a, e, ty = self#expr scx a e in
        (a, List (Refs, [e]) @@ oe, ty)
    | List (q, es) ->
        let a, es = List.fold_left begin fun (a, es) e ->
          let a, e, ty = self#expr scx a e in
          check_ty0_eq ty (TAtom TBool);
          (a, e :: es)
        end (a, []) es in
        let es = List.rev es in
        (a, List (q, es) @@ oe, TAtom TBool)
    | Quant (q, bs, e) ->
        let scx, a, bs = self#bounds scx a bs in
        let a, e, ty = self#expr scx a e in
        check_ty0_eq ty (TAtom TBool);
        (a, Quant (q, bs, e) @@ oe, TAtom TBool)
    | Tquant (q, vs, e) ->
        let scx = adjs scx (List.map begin fun v ->
          Flex v @@ v
        end vs) in
        let a, e, ty = self#expr scx a e in
        check_ty0_eq ty (TAtom TBool);
        (a, Tquant (q, vs, e) @@ oe, TAtom TBool)
    | Choose (v, optdom, e) ->
        let a, optdom, h =
          match optdom with
          | None ->
              (a, None, Fresh (v, Shape_expr, Constant, Unbounded) @@ v)
          | Some dom ->
              let ty1 = get v Props.type_prop in
              let a, dom, ty2 = self#expr scx a dom in
              begin match query v Props.targs_prop with
              | None ->
                  check_ty0_eq ty1 (TAtom TU);
                  check_ty0_eq ty2 (TAtom TU);
                  (a, Some dom, Fresh (v, Shape_expr, Constant, Bounded (dom, Visible)) @@ v)
              | Some ([ ty3 ]) ->
                  check_ty0_eq ty1 ty3;
                  check_ty0_eq ty2 (TSet ty3);
                  (a, Some dom, Fresh (v, Shape_expr, Constant, Bounded (dom, Visible)) @@ v)
              | _ ->
                  error ~at:v "Bad type annotation"
              end
        in
        let scx = adj scx h in
        let a, e, ty = self#expr scx a e in
        check_ty0_eq ty (TAtom TBool);
        (a, Choose (v, optdom, e) @@ oe, TAtom TU)
    | SetSt (v, dom, e) ->
        let ty1 = get v Props.type_prop in
        let a, dom, ty2 = self#expr scx a dom in
        let scx = adj scx (Fresh (v, Shape_expr, Constant, Bounded (dom, Visible)) @@ v) in
        let a, e, ty3 = self#expr scx a e in
        check_ty0_eq ty3 (TAtom TBool);
        begin match query oe Props.targs_prop with
        | None ->
            check_ty0_eq ty1 (TAtom TU);
            check_ty0_eq ty2 (TAtom TU);
            (a, SetSt (v, dom, e) @@ oe, TAtom TU)
        | Some ([ ty4 ]) ->
            check_ty0_eq ty1 ty4;
            check_ty0_eq ty2 (TSet ty4);
            (a, SetSt (v, dom, e) @@ oe, TSet ty4)
        | _ ->
            error ~at:oe "Bad type annotation"
        end
    | SetOf (e, bs) ->
        let scx, a, bs = self#bounds scx a bs in
        let a, e, ty = self#expr scx a e in
        check_ty0_eq ty (TAtom TBool);
        begin match query oe Props.targs_prop with
        | None ->
            (a, SetOf (e, bs) @@ oe, TAtom TU)
        | Some (ty :: _) ->
            (a, SetOf (e, bs) @@ oe, TSet ty)
        | _ ->
            error ~at:oe "Bad type annotation"
        end
    | SetEnum es ->
        let a, es, tys = List.fold_left begin fun (a, es, tys) e ->
          let a, e, ty = self#expr scx a e in
          (a, e :: es, ty :: tys)
        end (a, [], []) es in
        let es = List.rev es in
        let ty1s = List.rev tys in
        begin match query oe Props.targs_prop with
        | None ->
            List.iter (fun ty1 -> check_ty0_eq ty1 (TAtom TU)) ty1s;
            (a, SetEnum es @@ oe, TAtom TU)
        | Some ([ ty2 ]) ->
            List.iter (fun ty1 -> check_ty0_eq ty1 ty2) ty1s;
            (a, SetEnum es @@ oe, TSet ty2)
        | _ ->
            error ~at:oe "Bad type annotation"
        end
    | Fcn (bs, e) ->
        let scx, a, bs = self#bounds scx a bs in
        let a, e, ty1 = self#expr scx a e in
        begin match query oe Props.targs_prop with
        | None ->
            check_ty0_eq ty1 (TAtom TU);
            (a, Fcn (bs, e) @@ oe, TAtom TU)
        | Some ([ ty2 ; ty3 ]) ->
            check_ty0_eq ty1 ty3;
            (a, Fcn (bs, e) @@ oe, TArrow (ty2, ty3))
        | _ ->
            error ~at:oe "Bad type annotation"
        end
    | FcnApp (f, es) ->
        let a, f, ty1 = self#expr scx a f in
        let a, es, tys = List.fold_left begin fun (a, es, tys) e ->
          let a, e, ty = self#expr scx a e in
          (a, e :: es, ty :: tys)
        end (a, [], []) es in
        let es = List.rev es in
        let ty2s = List.rev tys in
        begin match query oe Props.targs_prop with
        | None ->
            check_ty0_eq ty1 (TAtom TU);
            List.iter (fun ty2 -> check_ty0_eq ty2 (TAtom TU)) ty2s;
            (a, FcnApp (f, es) @@ oe, TAtom TU)
        | Some ([ ty3 ; ty4 ]) ->
            check_ty0_eq ty1 (TArrow (ty3, ty4));
            (* FIXME ty2s should be a singleton *)
            List.iter (fun ty2 -> check_ty0_eq ty2 ty3) ty2s;
            (a, FcnApp (f, es) @@ oe, ty4)
        | _ ->
            error ~at:oe "Bad type annotation"
        end
    | Arrow (e, f) ->
        let a, e, ty1 = self#expr scx a e in
        let a, f, ty2 = self#expr scx a f in
        begin match query oe Props.targs_prop with
        | None ->
            check_ty0_eq ty1 (TAtom TU);
            check_ty0_eq ty2 (TAtom TU);
            (a, Arrow (e, f) @@ oe, TAtom TU)
        | Some ([ ty3 ; ty4 ]) ->
            check_ty0_eq ty1 (TSet ty3);
            check_ty0_eq ty2 (TSet ty4);
            (a, Arrow (e, f) @@ oe, TSet (TArrow (ty3, ty4)))
        | _ ->
            error ~at:oe "Bad type annotation"
        end
    | Product es ->
        let a, es, tys = List.fold_left begin fun (a, es, tys) e ->
          let a, e, ty = self#expr scx a e in
          (a, e :: es, ty :: tys)
        end (a, [], []) es in
        let es = List.rev es in
        let ty1s = List.rev tys in
        begin match query oe Props.targs_prop with
        | None ->
            List.iter (fun ty1 -> check_ty0_eq ty1 (TAtom TU)) ty1s;
            (a, Product es @@ oe, TAtom TU)
        | Some ty2s ->
            List.iter2 (fun ty1 ty2 -> check_ty0_eq ty1 ty2) ty1s ty2s;
            (a, Product es @@ oe, TSet (TProd ty2s))
        end
    | Tuple es ->
        let a, es, tys = List.fold_left begin fun (a, es, tys) e ->
          let a, e, ty = self#expr scx a e in
          (a, e :: es, ty :: tys)
        end (a, [], []) es in
        let es = List.rev es in
        let ty1s = List.rev tys in
        begin match query oe Props.targs_prop with
        | None ->
            List.iter (fun ty1 -> check_ty0_eq ty1 (TAtom TU)) ty1s;
            (a, Product es @@ oe, TAtom TU)
        | Some ty2s ->
            List.iter2 (fun ty1 ty2 -> check_ty0_eq ty1 ty2) ty1s ty2s;
            (a, Product es @@ oe, TProd ty2s)
        end
    (* FIXME Support? *)
    (*
    | Rect fs ->
        let a, fs = List.fold_left begin fun (a, fs) (s, e) ->
          let a, e = self#expr scx a e in
          (a, (s, e) :: fs)
        end (a, []) fs in
        let fs = List.rev fs in
        (a, Rect fs @@ oe)
    | Record fs ->
        let a, fs = List.fold_left begin fun (a, fs) (s, e) ->
          let a, e = self#expr scx a e in
          (a, (s, e) :: fs)
        end (a, []) fs in
        let fs = List.rev fs in
        (a, Record fs @@ oe)
    | Except (e, xs) ->
        let a, e = self#expr scx a e in
        let a, xs = List.fold_left begin fun (a, xs) x ->
          let a, x = self#exspec scx a x in
          (a, x :: xs)
        end (a, []) xs in
        let xs = List.rev xs in
        (a, Except (e, xs) @@ oe)
    | Dot (e, f) ->
        let a, e = self#expr scx a e in
        (a, Dot (e, f) @@ oe)
    *)
    | Case (arms, oth) ->
        let a, arms, tys = List.fold_left begin fun (a, arms, tys) (e, f) ->
          let a, e, ty1 = self#expr scx a e in
          let a, f, ty2 = self#expr scx a f in
          check_ty0_eq ty1 (TAtom TBool);
          (a, (e, f) :: arms, ty2 :: tys)
        end (a, [], []) arms in
        let arms = List.rev arms in
        let ty1s = List.rev tys in
        let a, oth, oty2 =
          match oth with
          | None ->
              (a, None, None)
          | Some o ->
              let a, o, ty2 = self#expr scx a o in
              (a, Some o, Some ty2)
        in
        begin match query oe Props.targs_prop with
        | None ->
            (a, Case (arms, oth) @@ oe, TAtom TU)
        | Some ([ ty3 ]) ->
            List.iter (fun ty1 -> check_ty0_eq ty1 ty3) ty1s;
            Option.iter (fun ty2 -> check_ty0_eq ty2 ty3) oty2;
            (a, Case (arms, oth) @@ oe, ty3)
        | _ ->
            error ~at:oe "Bad type annotation"
        end
    | Parens (e, pf) ->
        let a, e, ty = self#expr scx a e in
        let a, pf = self#pform scx a pf in
        (a, Parens (e, pf) @@ oe, ty)
    | _ ->
        error ~at:oe "Not supported"

  method earg scx a ea =
    match ea.core with
    | Ix n ->
        let targ = lookup_ty_arg scx n in
        (a, Ix n @@ ea, targ)
    | Lambda (vs, e) ->
        let scx = adjs scx (List.map begin fun (v, shp) ->
          Fresh (v, shp, Unknown, Unbounded) @@ v
        end vs) in
        let a, e, ty = self#expr scx a e in
        let tys =
          let n = List.length vs in
          List.init n (fun i -> lookup_ty scx (n - i))
        in
        (a, Lambda (vs, e) @@ ea, TOp (tys, ty))
    | _ ->
        let a, ea, ty = self#expr scx a ea in
        (a, ea, TRg ty)

  method eopr scx a ep =
    match ep.core with
    | Ix n ->
        let tsch = lookup_ty_sch scx n in
        (a, Ix n @@ ep, tsch)
    | Opaque o ->
        let tsch =
          try get ep Props.tsch_prop
          with _ ->
            error ~at:ep ("No annotation on Opaque '" ^ o ^ "'")
        in
        (a, Opaque o @@ ep, tsch)
    | Lambda (vs, e) ->
        let scx = adjs scx (List.map begin fun (v, shp) ->
          Fresh (v, shp, Unknown, Unbounded) @@ v
        end vs) in
        let a, e, ty = self#expr scx a e in
        let targs =
          let n = List.length vs in
          List.init n (fun i -> lookup_ty_arg scx (n - i - 1))
        in
        (a, Lambda (vs, e) @@ ep, TSch ([], targs, ty))
    | Internal b ->
        let mk_tsch tys ty = TSch ([], List.map (fun ty -> TRg ty) tys, ty) in
        let tsch =
          match b, query ep Props.targs_prop with
          | B.TRUE, _           -> mk_tsch [] (TAtom TBool)
          | B.FALSE, _          -> mk_tsch [] (TAtom TBool)
          | B.Implies, _        -> mk_tsch [TAtom TBool; TAtom TBool] (TAtom TBool)
          | B.Equiv, _          -> mk_tsch [TAtom TBool; TAtom TBool] (TAtom TBool)
          | B.Conj, _           -> mk_tsch [TAtom TBool; TAtom TBool] (TAtom TBool)
          | B.Disj, _           -> mk_tsch [TAtom TBool; TAtom TBool] (TAtom TBool)
          | B.Neg, _            -> mk_tsch [TAtom TBool] (TAtom TBool)
          | B.Eq, None          -> mk_tsch [TAtom TU; TAtom TU] (TAtom TBool)
          | B.Neq, None         -> mk_tsch [TAtom TU; TAtom TU] (TAtom TBool)
          | B.Eq, Some ([ty])           -> mk_tsch [ty; ty] (TAtom TBool)
          | B.Neq, Some ([ty])          -> mk_tsch [ty; ty] (TAtom TBool)

          | B.STRING, None      -> mk_tsch [] (TAtom TU)
          | B.BOOLEAN, None     -> mk_tsch [] (TAtom TU)
          | B.SUBSET, None      -> mk_tsch [TAtom TU] (TAtom TU)
          | B.UNION, None       -> mk_tsch [TAtom TU] (TAtom TU)
          | B.DOMAIN, None      -> mk_tsch [TAtom TU] (TAtom TU)
          | B.Subseteq, None    -> mk_tsch [TAtom TU; TAtom TU] (TAtom TBool)
          | B.Mem, None         -> mk_tsch [TAtom TU; TAtom TU] (TAtom TBool)
          | B.Notmem, None      -> mk_tsch [TAtom TU; TAtom TU] (TAtom TBool)
          | B.Setminus, None    -> mk_tsch [TAtom TU; TAtom TU] (TAtom TU)
          | B.Cap, None         -> mk_tsch [TAtom TU; TAtom TU] (TAtom TU)
          | B.Cup, None         -> mk_tsch [TAtom TU; TAtom TU] (TAtom TU)
          | B.STRING, Some ([])         -> mk_tsch [] (TSet (TAtom TStr))
          | B.BOOLEAN, Some ([])        -> mk_tsch [] (TSet (TAtom TBool))
          | B.SUBSET, Some ([ty])       -> mk_tsch [TSet ty] (TSet (TSet ty))
          | B.UNION, Some ([ty])        -> mk_tsch [TSet (TSet ty)] (TSet ty)
          | B.DOMAIN, Some ([ty1; ty2]) -> mk_tsch [TArrow (ty1, ty2)] (TSet ty1)
          | B.Subseteq, Some ([ty])     -> mk_tsch [TSet ty; TSet ty] (TAtom TBool)
          | B.Mem, Some ([ty])          -> mk_tsch [ty; ty] (TAtom TBool)
          | B.Notmem, Some ([ty])       -> mk_tsch [ty; ty] (TAtom TBool)
          | B.Setminus, Some ([ty])     -> mk_tsch [TSet ty; TSet ty] (TSet ty)
          | B.Cap, Some ([ty])          -> mk_tsch [TSet ty; TSet ty] (TSet ty)
          | B.Cup, Some ([ty])          -> mk_tsch [TSet ty; TSet ty] (TSet ty)

          | B.Nat, None         -> mk_tsch [] (TAtom TU)
          | B.Int, None         -> mk_tsch [] (TAtom TU)
          | B.Real, None        -> mk_tsch [] (TAtom TU)
          | B.Plus, None        -> mk_tsch [TAtom TU; TAtom TU] (TAtom TU)
          | B.Minus, None       -> mk_tsch [TAtom TU; TAtom TU] (TAtom TU)
          | B.Uminus, None      -> mk_tsch [TAtom TU] (TAtom TU)
          | B.Times, None       -> mk_tsch [TAtom TU; TAtom TU] (TAtom TU)
          | B.Ratio, None       -> mk_tsch [TAtom TU; TAtom TU] (TAtom TU)
          | B.Quotient, None    -> mk_tsch [TAtom TU; TAtom TU] (TAtom TU)
          | B.Remainder, None   -> mk_tsch [TAtom TU; TAtom TU] (TAtom TU)
          | B.Exp, None         -> mk_tsch [TAtom TU; TAtom TU] (TAtom TU)
          | B.Infinity, None    -> mk_tsch [] (TAtom TU)
          | B.Lteq, None        -> mk_tsch [TAtom TU; TAtom TU] (TAtom TBool)
          | B.Lt, None          -> mk_tsch [TAtom TU; TAtom TU] (TAtom TBool)
          | B.Gteq, None        -> mk_tsch [TAtom TU; TAtom TU] (TAtom TBool)
          | B.Gt, None          -> mk_tsch [TAtom TU; TAtom TU] (TAtom TBool)
          | B.Range, None       -> mk_tsch [TAtom TU; TAtom TU] (TAtom TU)
          | B.Nat, Some ([])            -> mk_tsch [] (TSet (TAtom TInt))
          | B.Int, Some ([])            -> mk_tsch [] (TSet (TAtom TInt))
          | B.Real, Some ([])           -> mk_tsch [] (TSet (TAtom TReal))
          | B.Plus, Some ([ty])         -> mk_tsch [ty; ty] ty
          | B.Minus, Some ([ty])        -> mk_tsch [ty; ty] ty
          | B.Uminus, Some ([ty])       -> mk_tsch [ty] ty
          | B.Times, Some ([ty])        -> mk_tsch [ty; ty] ty
          | B.Ratio, Some ([ty])        -> mk_tsch [ty; ty] ty
          | B.Quotient, Some ([ty])     -> mk_tsch [ty; ty] ty
          | B.Remainder, Some ([ty])    -> mk_tsch [ty; ty] ty
          | B.Exp, Some ([ty])          -> mk_tsch [ty; ty] ty
          | B.Infinity, Some ([])       -> mk_tsch [] (TAtom TReal)
          | B.Lteq, Some ([ty])         -> mk_tsch [ty; ty] (TAtom TBool)
          | B.Lt, Some ([ty])           -> mk_tsch [ty; ty] (TAtom TBool)
          | B.Gteq, Some ([ty])         -> mk_tsch [ty; ty] (TAtom TBool)
          | B.Gt, Some ([ty])           -> mk_tsch [ty; ty] (TAtom TBool)
          | B.Range, Some ([])          -> mk_tsch [TAtom TInt; TAtom TInt] (TSet (TAtom TInt))

          | _, _ -> error "Builtin not supported"
        in
        (a, Internal b @@ ep, tsch)
    | _ ->
        let a, ep, ty = self#expr scx a ep in
        (a, ep, TSch ([], [], ty))

  method pform scx a pf =
    (a, pf)

  method sel scx a sel =
    match sel with
    | Sel_inst args ->
        let a, e = List.fold_left begin fun (a, args) e ->
          let a, e, _ = self#expr scx a e in
          (a, e :: args)
        end (a, []) args in
        let args = List.rev args in
        (a, Sel_inst args)
    | Sel_lab (l, args) ->
        let a, e = List.fold_left begin fun (a, args) e ->
          let a, e, _ = self#expr scx a e in
          (a, e :: args)
        end (a, []) args in
        let args = List.rev args in
        (a, Sel_lab (l, args))
    | _ ->
        (a, sel)

  method sequent scx a sq =
    let scx, a, hyps = self#hyps scx a sq.context in
    let a, act, ty = self#expr scx a sq.active in
    check_ty0_eq ty (TAtom TBool);
    (scx, a, { context = hyps ; active = act })

  method defn scx a df =
    match df.core with
      | Recursive (nm, shp) ->
          (a, Recursive (nm, shp) @@ df)
      | Operator (nm, e) ->
          let a, e, _ = self#eopr scx a e in
          (a, Operator (nm, e) @@ df)
      | Instance (nm, i) ->
          let a, i = self#instance scx a i in
          (a, Instance (nm, i) @@ df)
      | Bpragma (nm, e, l) ->
          let a, e, _ = self#expr scx a e in
          (a, Bpragma (nm, e, l) @@ df)

  method defns scx a ds =
    match ds with
    | [] -> scx, a, []
    | df :: dfs ->
        let a, df = self#defn scx a df in
        let scx = adj scx (Defn (df, User, Visible, Local) @@ df) in
        let scx, a, dfs = self#defns scx a dfs in
        (scx, a, df :: dfs)

  method bounds scx a bs =
    let a, bs = List.fold_left begin fun (a, bs) (v, k, dom) ->
      match dom with
      | Domain d ->
          let ty1 = get v Props.type_prop in
          let a, d, ty2 = self#expr scx a d in
          begin match query v Props.targs_prop with
          | None ->
              check_ty0_eq ty1 (TAtom TU);
              check_ty0_eq ty2 (TAtom TU);
              (a, (v, k, Domain d) :: bs)
          | Some ([ ty3 ]) ->
              check_ty0_eq ty1 ty3;
              check_ty0_eq ty2 (TSet ty3);
              (a, (v, k, Domain d) :: bs)
          | _ ->
              error ~at:v "Bad type annotation"
          end
      | _ ->
          (a, (v, k, dom) :: bs)
    end (a, []) bs in
    let bs = List.rev bs in
    let hs = List.map begin
      fun (v, k, _) -> Fresh (v, Shape_expr, k, Unbounded) @@ v
    end bs in
    let scx = adjs scx hs in
    (scx, a, bs)

  method bound scx (a : 'a) b =
    match self#bounds scx a [b] with
      | scx, a, [b] -> (scx, a, b)
      | _ -> assert false

  method exspec scx a (trail, res) =
    (* FIXME Support? *)
    let a, trail = List.fold_left begin fun (a, trail) x ->
      match x with
      | Except_dot s ->
          (a, (Except_dot s) :: trail)
      | Except_apply e ->
          let a, e, _ = self#expr scx a e in
          (a, (Except_apply e) :: trail)
    end (a, []) trail in
    let trail = List.rev trail in
    let a, res, _ = self#expr scx a res in
    (a, (trail, res))

  method instance scx a i =
    let scx = List.fold_left begin fun scx v ->
      adj scx (Fresh (v, Shape_expr, Unknown, Unbounded) @@ v)
    end scx i.inst_args in
    let a, sub = List.fold_left begin fun (a, sub) (v, e) ->
      let a, e, _ = self#expr scx a e in
      (a, (v, e) :: sub)
    end (a, []) i.inst_sub in
    let sub = List.rev sub in
    (a, { i with inst_sub = sub })

  method hyp scx a h =
    match h.core with
    | Fresh (nm, shp, lc, dom) ->
        let a, dom =
          match dom with
          | Unbounded ->
              (a, Unbounded)
          | Bounded (r, rvis) ->
              let ty1 = get nm Props.type_prop in
              let a, r, ty2 = self#expr scx a r in
              begin match query nm Props.targs_prop with
              | None ->
                  check_ty0_eq ty1 (TAtom TU);
                  check_ty0_eq ty2 (TAtom TU);
                  (a, Bounded (r, rvis))
              | Some ([ ty3 ]) ->
                  check_ty0_eq ty1 ty3;
                  check_ty0_eq ty2 (TSet ty3);
                  (a, Bounded (r, rvis))
              | _ ->
                  error ~at:nm "Bad type annotation"
              end
        in
        let h = Fresh (nm, shp, lc, dom) @@ h in
        let scx = adj scx h in
        (scx, a, h)
    | Flex s ->
        let h = Flex s @@ h in
        let scx = adj scx h in
        (scx, a, h)
    | Defn (df, wd, vis, ex) ->
        let a, df = self#defn scx a df in
        let h = Defn (df, wd, vis, ex) @@ h in
        let scx = adj scx h in
        (scx, a, h)
    | Fact (e, vis, tm) ->
        let a, e, ty = self#expr scx a e in
        check_ty0_eq ty (TAtom TBool);
        let h = Fact (e, vis, tm) @@ h in
        let scx = adj scx h in
        (scx, a, h)

  method hyps scx a hs =
    match Deque.front hs with
    | None -> scx, a, Deque.empty
    | Some (h, hs) ->
        let scx, a, h = self#hyp scx a h in
        let scx, a, hs = self#hyps scx a hs in
        (scx, a, Deque.cons h hs)
end

