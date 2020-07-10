(*
 * encode/canon.ml --- eliminate primitives and builtins
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

open Ext
open Property
open Expr.T
open Type.T

module B = Builtin
module T = N_table

(* TODO No type-checking is done in the functions bound and bounds
 * to check equality between the annotation and the infered type from
 * a present domain. *)

(* TODO Reduce tuples to functions and products to arrows *)

(* TODO Also reduce all function to one-argument functions *)


(* {3 Contexts} *)

type gtx = ty_kind Ctx.t
type ltx = ty_kind Ctx.t

let ladj lx v =
  let ty =
    if Type.T.has_sort v then
      mk_cstk_ty (mk_atom_ty (Type.T.get_sort v))
    else if Type.T.has_type v then
      mk_cstk_ty (Type.T.get_type v)
    else
      Type.T.get_kind v
  in
  Ctx.adj lx v.core ty

let gadj gx v =
  let k = try
    Type.T.get_kind v
  with Not_found ->
    mk_cstk_ty TUnknown
  in
  Ctx.adj gx v.core k

let get_kind cx n =
  let _, k = Ctx.index cx n in
  Option.get k

let get_type cx n =
  let _, k = Ctx.index cx n in
  Type.T.get_ty (Option.get k)


(* {3 Helpers} *)

let error ?at mssg =
  Errors.bug ?at ("Encode.Canon: " ^ mssg)

(* FIXME Replace with subtype check *)
let checkt_eq ?at ty1 ty2 =
  if (ty1 <> ty2) && (ty1 <> ty_u) then
    let () = Format.fprintf Format.str_formatter "typechecking error: expected %a, found %a"
    pp_print_type ty1 pp_print_type ty2 in
    let mssg = Format.flush_str_formatter () in
    error ?at mssg
  else ()

let checkk_eq ?at k1 k2 =
  if k1 != k2 then
    error ?at "kindchecking error"
  else ()

let mk_opaque smb =
  let c = Opaque (T.get_name smb) %% [] in
  T.set_smb smb c


(* {3 Prepare} *)

let prepare_visitor = object (self : 'self)
  inherit [unit] Expr.Visit.map as super

  (* TODO *)

  method expr scx oe =
    match oe.core with
    | Fcn (bs, e) when List.length bs > 1 ->
        super#expr scx (Fcn (bs, e) @@ oe)

    (* x \notin y -> ~ (x \in y) *)
    | Apply ({ core = Internal B.Notmem } as op, [ e ; f ]) ->
        Apply (Internal B.Neg %% [], [
          Apply (Internal B.Mem @@ op, [ e ; f ]) %% []
        ]) @@ oe
        |> super#expr scx

    | _ -> super#expr scx oe
end


(* {3 Main} *)

let rec expr gx lx oe =
  match oe.core with
  | Ix n ->
      if 1 <= n && n <= Ctx.length lx then
        let ty = get_type lx n in
        (Ix n @@ oe, ty)
      else if Ctx.length lx < n && n - Ctx.length lx <= Ctx.length gx then
        let ty = get_type gx (n - Ctx.length lx) in
        (Ix n @@ oe, ty)
      else
        (Ix n @@ oe, TUnknown)

  | Internal b ->
      begin match b with
      | B.TRUE ->
          (Internal b @@ oe, ty_bool)
      | B.FALSE ->
          (Internal b @@ oe, ty_bool)
      | B.STRING ->
          let smb = T.std_smb T.Strings in
          let ty = get_ty (T.get_kind smb) in
          (mk_opaque smb $$ oe, ty)
      | B.BOOLEAN ->
          let smb = T.std_smb T.Booleans in
          let ty = get_ty (T.get_kind smb) in
          (mk_opaque smb $$ oe, ty)
      | B.Nat ->
          let smb = T.std_smb T.Nats in
          let ty = get_ty (T.get_kind smb) in
          (mk_opaque smb $$ oe, ty)
      | B.Int ->
          let smb = T.std_smb T.Ints in
          let ty = get_ty (T.get_kind smb) in
          (mk_opaque smb $$ oe, ty)
      | B.Real ->
          let smb = T.std_smb T.Reals in
          let ty = get_ty (T.get_kind smb) in
          (mk_opaque smb $$ oe, ty)
      | _ ->
          error "misplaced builtin"
      end

  | Apply (op, es) ->
      let op, TKind (ks, ty) = lexpr gx lx op in
      let es =
        List.map2 begin fun e k ->
          match k with
          | TKind ([], ty1) ->
              let e, ty2 = expr gx lx e in
              checkt_eq ~at:e ty1 ty2;
              e
          | _ ->
              let e, k2 = lexpr gx lx e in
              checkk_eq ~at:e k k2;
              e
        end es ks
      in
      (Apply (op, es) @@ oe, ty)

  | With (e, m) ->
      let e, ty = expr gx lx e in
      (With (e, m) @@ oe, ty)

  | If (e, f, g) ->
      let e, ty1 = expr gx lx e in
      let f, ty2 = expr gx lx f in
      let g, ty3 = expr gx lx g in
      checkt_eq ~at:e ty_bool ty1;
      checkt_eq ~at:g ty2 ty3;
      (If (e, f, g) @@ oe, ty3)

  | List (bl, es) ->
      let es =
        List.map begin fun e ->
          let e, ty = expr gx lx e in
          checkt_eq ~at:e ty_bool ty;
          e
        end es
      in
      (List (bl, es) @@ oe, ty_bool)

  | Let (dfs, e) ->
      let lx, dfs = defns gx lx dfs in
      let e, ty = expr gx lx e in
      (Let (dfs, e) @@ oe, ty)

  | Quant (q, bs, e) ->
      let lx, bs = bounds gx lx bs in
      let e, ty = expr gx lx e in
      checkt_eq ~at:e ty_bool ty;
      (Quant (q, bs, e) @@ oe, ty_bool)

  | Tquant (q, hs, e) ->
      let lx = List.fold_left ladj lx hs in
      let e, ty = expr gx lx e in
      checkt_eq ~at:e ty_bool ty;
      (Tquant (q, hs, e) @@ oe, ty_bool)

  | Choose (v, None, e) ->
      let lx = ladj lx v in
      let ty1 = get_type lx 1 in
      let e, ty2 = expr gx lx e in
      checkt_eq ~at:e ty_bool ty2;
      let smb = T.std_smb (T.Choose ty1) in
      let args = [ Lambda ([ v, Shape_expr ], e) %% [] ] in
      (Apply (mk_opaque smb, args) @@ oe, ty1) (* FIXME ret type safe? *)

  | Choose (v, Some dom, e) ->
      let dom, ty1' = expr gx lx dom in
      let lx = ladj lx v in
      let ty1 = get_type lx 1 in
      (*checkt_eq ~at:dom (TSet ty1) ty1';*) (* FIXME *)
      let e, ty2 = expr gx lx e in
      checkt_eq ~at:e ty_bool ty2;
      let e =
        List ( And, [
          Apply (
            Internal B.Mem %% [],
            [
              Ix 1 %% [] ;
              Expr.Subst.app_expr (Expr.Subst.shift 1) dom
            ]
          ) %% [] ;
          e
        ]) %% []
      in
      let smb = T.std_smb (T.Choose ty1) in
      let args = [ Lambda ([ v, Shape_expr ], e) %% [] ] in
      (Apply (mk_opaque smb, args) @@ oe, ty1) (* FIXME ret type safe? *)

  | SetSt (v, dom, e) ->
      let dom, ty1' = expr gx lx dom in
      let lx = ladj lx v in
      let ty1 = get_type lx 1 in
      (*checkt_eq ~at:dom (TSet ty1) ty1';*) (* FIXME *)
      let e, ty2 = expr gx lx e in
      checkt_eq ~at:e ty_bool ty2;
      let smb = T.std_smb (T.SetSt ty1) in
      let args = [ dom ; Lambda ([ v, Shape_expr ], e) %% [] ] in
      (Apply (mk_opaque smb, args) @@ oe, TSet ty1)

  | SetOf (e, bs) ->
      let lx, bs = bounds gx lx bs in
      let e, ty = expr gx lx e in
      let tys = List.init (List.length bs) begin fun i ->
        get_type lx (i + 1)
      end in
      let smb = T.std_smb (T.SetOf (tys, ty)) in
      let _, xs, bs = List.fold_left begin fun (dom', xs, bs) (v, _, dom) ->
        match dom', dom with
        | _, Domain dom -> (Some dom, (v, Shape_expr) :: xs, dom :: bs)
        | Some dom', Ditto -> (Some dom', (v, Shape_expr) :: xs, dom' :: bs)
        | _ -> error "missing bound domain"
      end (None, [], []) bs in
      let xs, bs = List.rev xs, List.rev bs in
      let args = bs @ [ Lambda (xs, e) %% [] ] in
      (Apply (mk_opaque smb, args) @@ oe, TSet ty)

  | SetEnum es ->
      let es_tys = List.map (expr gx lx) es in
      let ty =
        match es_tys with
        | [] -> ty_u (* FIXME type of empty set? *)
        | (_, ty1) :: es_tys ->
            List.iter (fun (e2, ty2) -> checkt_eq ~at:e2 ty1 ty2) es_tys;
            ty1
      in
      let es = List.map fst es_tys in
      let n = List.length es in
      let smb = T.std_smb (T.SetEnum (n, ty)) in
      let args = es in
      (Apply (mk_opaque smb, args) @@ oe, TSet ty)

  (* NOTE Product and Tuple reduced to functions beforehand *)

  | Fcn ([ v, _, Domain dom ], e) -> (* FIXME prepare (reduce tuples) *)
      let dom, ty11 = expr gx lx dom in
      let lx = ladj lx v in
      let ty12 = get_type lx 1 in
      (*checkt_eq ~at:dom (TSet ty12) ty11;*) (* FIXME *)
      let e, ty2 = expr gx lx e in
      let smb = T.std_smb (T.Fcn (ty12, ty2)) in
      let args = [ dom ; Lambda ([ v, Shape_expr ], e) %% [] ] in
      (Apply (mk_opaque smb, args) @@ oe, TArrow (ty12, ty2))

  | FcnApp (e1, [e2]) -> (* FIXME prepare *)
      let e1, ty1 = expr gx lx e1 in
      let e2, ty2 = expr gx lx e2 in
      let ty11, ty12 =
        match ty1 with
        | TArrow (ty11, ty12) -> ty11, ty12
        | _ -> error ~at:oe "typechecking error: expected arrow type"
      in
      checkt_eq ~at:e2 ty11 ty2;
      let smb = T.std_smb (T.FcnApp (ty11, ty12)) in
      let args = [ e1 ; e2 ] in
      (Apply (mk_opaque smb, args) @@ oe, ty12)

  | Arrow (e1, e2) ->
      let e1, ty1 = expr gx lx e1 in
      let e2, ty2 = expr gx lx e2 in
      let smb = T.std_smb (T.Arrow (ty1, ty2)) in
      let args = [ e1 ; e2 ] in
      (Apply (mk_opaque smb, args) @@ oe, TSet (TArrow (ty1, ty2)))

  (* TODO *)

  | Case (ps, None) ->
      let ps, tys =
        List.map begin fun (p, e) ->
          let p, ty1 = expr gx lx p in
          checkt_eq ~at:p ty_bool ty1;
          let e, ty2 = expr gx lx e in
          (p, e), ty2
        end ps
        |> List.split
      in
      let ty =
        let l = List.combine (List.map snd ps) tys in
        let ty1 = snd (List.hd l) in
        List.iter begin fun (e, ty2) ->
          checkt_eq ~at:e ty1 ty2
        end (List.tl l);
        ty1
      in
      (Case (ps, None) @@ oe, ty) (* FIXME ret type safe? *)

  | Case (ps, Some o) ->
      let ps, tys =
        List.map begin fun (p, e) ->
          let p, ty1 = expr gx lx p in
          checkt_eq ~at:p ty_bool ty1;
          let e, ty2 = expr gx lx e in
          (p, e), ty2
        end ps
        |> List.split
      in
      let o, ty = expr gx lx o in
      let ty =
        let l = List.combine (List.map snd ps) tys in
        let l = l @ [o, ty] in
        let ty1 = snd (List.hd l) in
        List.iter begin fun (e, ty2) ->
          checkt_eq ~at:e ty1 ty2
        end (List.tl l);
        ty1
      in
      (Case (ps, Some o) @@ oe, ty)

  | Parens (e, pf) ->
      let e, ty = expr gx lx e in
      (Parens (e, pf) @@ oe, ty)

  | Sequent sq ->
      (* FIXME This feels very wrong *)
      let gx =
        List.fold_left begin fun gx k ->
          Ctx.adj gx "shadow" k
        end gx (Ctx.to_list lx)
      in
      let sq = snd (sequent gx sq) in
      (Sequent sq @@ oe, ty_bool)

  | _ -> (oe, TUnknown) (* TODO *)

and lexpr gx lx op =
  match op.core with
  | Ix n ->
      (* left operator cannot be found locally *)
      if Ctx.length lx < n && n - Ctx.length lx <= Ctx.length gx then
        let k = get_kind gx (n - Ctx.length lx) in
        (Ix n @@ op, k)
      else
        error ~at:op "unbound variable"

  | Lambda (vs, e) ->
      let lx = List.fold_left ladj lx (List.map fst vs) in
      let e, ty = expr gx lx e in
      let vs_n, _ = List.split_nth (List.length vs) vs in
      let ks = List.rev_map (fun (v, _) -> Type.T.get_kind v) vs_n in
      let k = mk_kind_ty ks ty in
      (Lambda (vs, e) @@ op, k)

  | Internal b ->
      begin match b with
      | B.TRUE | B.FALSE ->
          let k = mk_cstk_ty ty_bool in
          (Internal b @@ op, k)
      | B.Implies
      | B.Equiv
      | B.Conj
      | B.Disj ->
          let k = mk_fstk_ty [ty_bool; ty_bool] ty_bool in
          (Internal b @@ op, k)
      | B.Neg ->
          let k = mk_fstk_ty [ty_bool] ty_bool in
          (Internal b @@ op, k)
      | B.Eq
      | B.Neq ->
          let k = Type.T.get_kind op in
          (Internal b @@ op, k)

      | B.STRING ->
          let smb = T.std_smb T.Strings in
          let k = T.get_kind smb in
          (mk_opaque smb $$ op, k)

      | B.BOOLEAN ->
          let smb = T.std_smb T.Booleans in
          let k = T.get_kind smb in
          (mk_opaque smb $$ op, k)

      | B.SUBSET ->
          let k = Type.T.get_kind op in
          let smb =
            match k with
            | TKind ([ TKind ([], TSet ty1) ], TSet (TSet ty2)) when ty1 = ty2 ->
                T.std_smb (T.Subset ty1)
            | _ ->
                T.std_smb (T.Uver (T.Subset TUnknown))
          in
          let k = T.get_kind smb in
          (mk_opaque smb $$ op, k)

      | B.UNION ->
          let k = Type.T.get_kind op in
          let smb =
            match k with
            | TKind ([ TKind ([], TSet (TSet ty1)) ], TSet ty2) when ty1 = ty2 ->
                T.std_smb (T.Union ty1)
            | _ ->
                T.std_smb (T.Uver (T.Union TUnknown))
          in
          let k = T.get_kind smb in
          (mk_opaque smb $$ op, k)

      | B.DOMAIN ->
          let k = Type.T.get_kind op in
          let smb =
            match k with
            | TKind ([ TKind ([], TArrow (ty1, ty2)) ], TSet ty3) when ty1 = ty3 ->
                T.std_smb (T.Domain (ty1, ty2))
            | _ ->
                T.std_smb (T.Uver (T.Domain (TUnknown, TUnknown)))
          in
          let k = T.get_kind smb in
          (mk_opaque smb $$ op, k)

      | B.Subseteq ->
          let k = Type.T.get_kind op in
          let smb =
            match k with
            | TKind ([ TKind ([], TSet ty1) ; TKind ([], TSet ty2) ], TAtom TBool) when ty1 = ty2 ->
                T.std_smb (T.SubsetEq ty1)
            | _ ->
                T.std_smb (T.Uver (T.SubsetEq TUnknown))
          in
          let k = T.get_kind smb in
          (mk_opaque smb $$ op, k)

      | B.Mem ->
          let k = Type.T.get_kind op in
          let smb =
            match k with
            | TKind ([ TKind ([], ty1) ; TKind ([], TSet ty2) ], TAtom TBool) when ty1 = ty2 ->
                T.std_smb (T.Mem ty1)
            | _ ->
                T.std_smb (T.Uver (T.Mem TUnknown))
          in
          let k = T.get_kind smb in
          (mk_opaque smb $$ op, k)

      | B.Notmem -> error "not implemented builtin: Notmem"

      | B.Setminus ->
          let k = Type.T.get_kind op in
          let smb =
            match k with
            | TKind ([ TKind ([], TSet ty1) ; TKind ([], TSet ty2) ], TSet ty3) when ty1 = ty2 && ty2 = ty3 ->
                T.std_smb (T.SetMinus ty1)
            | _ ->
                T.std_smb (T.Uver (T.SetMinus TUnknown))
          in
          let k = T.get_kind smb in
          (mk_opaque smb $$ op, k)

      | B.Cap ->
          let k = Type.T.get_kind op in
          let smb =
            match k with
            | TKind ([ TKind ([], TSet ty1) ; TKind ([], TSet ty2) ], TSet ty3) when ty1 = ty2 && ty2 = ty3 ->
                T.std_smb (T.Cap ty1)
            | _ ->
                T.std_smb (T.Uver (T.Cap TUnknown))
          in
          let k = T.get_kind smb in
          (mk_opaque smb $$ op, k)

      | B.Cup ->
          let k = Type.T.get_kind op in
          let smb =
            match k with
            | TKind ([ TKind ([], TSet ty1) ; TKind ([], TSet ty2) ], TSet ty3) when ty1 = ty2 && ty2 = ty3 ->
                T.std_smb (T.Cup ty1)
            | _ ->
                T.std_smb (T.Uver (T.Cup TUnknown))
          in
          let k = T.get_kind smb in
          (mk_opaque smb $$ op, k)

      | _ ->
          error "unrecognized builtin"
      end

  | _ -> error "bad form left operator"

and sequent gx sq =
  let gx, hyps = hyps gx sq.context in
  let goal, ty = expr gx Ctx.dot sq.active in
  checkt_eq ~at:sq.active ty_bool ty;
  (gx, { context = hyps ; active = goal })

and defn gx lx df =
  match df.core with
  | Recursive (nm, shp) ->
      df
  | Operator (nm, { core = Lambda (xs, e) }) ->
      error "unsupported second-order let-definition" (* FIXME *)
  | Operator (nm, e) ->
      let e, _ = expr gx lx e in
      Operator (nm, e) @@ df
  | Instance (nm, inst) ->
      df
  | Bpragma (nm, e, args) ->
      df

and defns gx lx dfs =
  match dfs with
  | [] -> (lx, [])
  | df :: dfs ->
      let df = defn gx lx df in
      let v =
        match df.core with
        | Recursive (v, _)
        | Operator (v, _)
        | Instance (v, _)
        | Bpragma (v, _, _) -> v
      in
      let lx = ladj lx v in
      let lx, dfs = defns gx lx dfs in
      (lx, df :: dfs)

and bound gx lx (v, k, dom) =
  let dom =
    match dom with
    | No_domain -> No_domain
    | Domain d -> Domain (fst (expr gx lx d))
    | Ditto -> Ditto
  in
  (v, k, dom)

and bounds gx lx bs =
  (* NOTE domains must be interpreted in the upper local context *)
  let lx, bs =
    List.fold_left begin fun (lx', bs) b ->
      let (v, _, _ as b) = bound gx lx b in
      let lx' = ladj lx' v in
      (lx', b :: bs)
    end (lx, []) bs
  in
  (lx, List.rev bs)

and hyp gx h =
  match h.core with
  | Fresh (v, shp, k, dom) ->
      Fresh (v, shp, k, dom) @@ h
  | Flex v ->
      Flex v @@ h
  | Defn ({ core = Recursive (v, shp) } as df, wd, vis, ex) ->
      Defn (df, wd, vis, ex) @@ h
  | Defn ({ core = Operator (v, e) } as df, wd, vis, ex) ->
      let e, _ = lexpr gx Ctx.dot e in
      let df = Operator (v, e) @@ df in
      Defn (df, wd, vis, ex) @@ h
  | Defn ({ core = Instance (v, inst) } as df, wd, vis, ex) ->
      Defn (df, wd, vis, ex) @@ h
  | Defn ({ core = Bpragma (v, e, args) } as df, wd, vis, ex) ->
      Defn (df, wd, vis, ex) @@ h
  | Fact (e, vis, tm) ->
      let e, ty = expr gx Ctx.dot e in
      checkt_eq ~at:e ty_bool ty;
      Fact (e, vis, tm) @@ h

and hyps gx hs =
  match Deque.front hs with
  | None ->
      (gx, Deque.empty)
  | Some (h, hs) ->
      let h = hyp gx h in
      let v = hyp_hint h in
      let gx = gadj gx v in
      let gx, hs = hyps gx hs in
      (gx, Deque.cons h hs)


let main sq =
  let scx = ((), Deque.empty) in
  let sq = snd (prepare_visitor#sequent scx sq) in

  let gx = Ctx.dot in
  snd (sequent gx sq)
