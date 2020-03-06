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

open N_table

module B = Builtin


(* {3 Contexts} *)

type gtx = ty_kind Ctx.t
type ltx = ty_kind Ctx.t

let ladj lx v =
  let ty =
    if Type.T.has_type v then
      mk_cstk_ty (Type.T.get_type v)
    else
      Type.T.get_kind v
  in
  Ctx.adj lx v.core ty

let gadj gx v =
  let k = Type.T.get_kind v in
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

let checkt_eq ?at ty1 ty2 =
  if ty1 != ty2 then
    error ?at "typechecking error"
  else ()

let checkk_eq ?at k1 k2 =
  if k1 != k2 then
    error ?at "typechecking error"
  else ()


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
      | _ ->
          error "unrecognized builtin"
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
      checkt_eq ty1 ty_bool;
      checkt_eq ty2 ty3;
      (If (e, f, g) @@ oe, ty3)

  | List (bl, es) ->
      let es =
        List.map begin fun e ->
          let e, ty = expr gx lx e in
          checkt_eq ty ty_bool;
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
      checkt_eq ty ty_bool;
      (Quant (q, bs, e) @@ oe, ty_bool)

  | Tquant (q, hs, e) ->
      let lx = List.fold_left ladj lx hs in
      let e, ty = expr gx lx e in
      checkt_eq ty ty_bool;
      (Tquant (q, hs, e) @@ oe, ty_bool)

      (* TODO actual reduction cases *)

  | Case (ps, o) ->
      let ps, tys =
        List.map begin fun (p, e) ->
          let p, ty1 = expr gx lx p in
          let e, ty2 = expr gx lx e in
          checkt_eq ty1 ty_bool;
          (p, e), ty2
        end ps
        |> List.split
      in
      let o, ty =
        match o with
        | None -> None, None
        | Some e ->
            let e, ty = expr gx lx e in
            Some e, Some ty
      in
      let ty =
        let tys =
          match ty with
          | None -> tys
          | Some ty -> ty :: tys
        in
        match tys with
        | ty :: tys ->
            List.iter (checkt_eq ty) tys;
            ty
        | _ ->
            error "empty case construct"
      in
      (Case (ps, o) @@ oe, ty)

  | Parens (e, pf) ->
      let e, ty = expr gx lx e in
      (Parens (e, pf) @@ oe, ty)

  | _ -> (oe, TUnknown) (* TODO *)

and lexpr gx lx op =
  match op.core with
  | Ix n ->
      (* left operator cannot be found locally *)
      if Ctx.length lx < n && n - Ctx.length lx <= Ctx.length gx then
        let k = get_kind gx (n - Ctx.length lx) in
        (Ix n @@ op, k)
      else
        error "unbound variable"

  | Lambda (vs, e) ->
      let lx = List.fold_left ladj lx (List.map fst vs) in
      let e, ty = expr gx lx e in
      let vs_n, _ = List.split_nth (List.length vs) vs in
      let ks = List.rev_map (fun (v, _) -> Type.T.get_kind v) vs_n in
      let k = mk_kind_ty ks ty in
      (Lambda (vs, e) @@ op, k)

  | Internal b ->
      begin match b with
      | _ ->
          error "unrecognized builtin"
      end

  | _ -> error "bad form left operator"

and sequent gx sq =
  let gx, hyps = hyps gx sq.context in
  let goal, ty = expr gx Ctx.dot sq.active in
  checkt_eq ~at:sq.active ty ty_bool;
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
      checkt_eq ~at:e ty ty_bool;
      Fact (e, vis, tm) @@ h

and hyps gx hs =
  match Deque.front hs with
  | None ->
      (gx, Deque.empty)
  | Some (h, hs) ->
      let h = hyp gx h in
      let v = hyp_hint h in
      let gx = gadj gx v in
      (gx, Deque.cons h hs)
