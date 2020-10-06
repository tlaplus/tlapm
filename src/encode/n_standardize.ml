(*
 * encode/standardize.ml
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

open Ext
open Property
open Expr.T
open Type.T

open N_table
open N_smb

module B = Builtin


let error ?at mssg =
  let mssg = "Encode.Standardize: " ^ mssg in
  Errors.bug ?at mssg


(* {3 Context} *)

type cx = ty2 Ctx.t

let adj cx v =
  let ty2 =
    if has v Props.ty2_prop then
      get v Props.ty2_prop
    else if has v Props.ty1_prop then
      upcast_ty2 (get v Props.ty1_prop)
    else if has v Props.ty0_prop then
      upcast_ty2 (upcast_ty1 (get v Props.ty0_prop))
    else
      error ~at:v "Missing type annotation"
  in
  Ctx.adj cx v.core ty2

let bump cx =
  Ctx.bump cx

let lookup_ty2 cx n =
  Option.get (snd (Ctx.index cx n))

let lookup_ty1 cx n =
  downcast_ty1 (lookup_ty2 cx n)

let lookup_ty0 cx n =
  downcast_ty0 (downcast_ty1 (lookup_ty2 cx n))


(* {3 Helpers} *)

let mk_opq smb =
  let op = Opaque (get_name smb) %% [] in
  let op = assign op smb_prop smb in
  op

let t_bol = TAtm TABol

let typecheck ?at ty01 ty02 =
  try
    typecheck ~expected:ty01 ~actual:ty02
  with Typechecking_error (ty01, ty02) ->
    let mssg = typecheck_error_mssg ~expected:ty01 ~actual:ty02 in
    error ?at mssg

let typecheck1 ?at ty01 ty02 =
  match ty01, ty02 with
  | Ty1 (ty01s, ty01), Ty1 (ty02s, ty02) ->
      List.iter2 (typecheck ?at) ty01s ty02s;
      typecheck ?at ty01 ty02

let typecheck2 ?at ty21 ty22 =
  match ty21, ty22 with
  | Ty2 (ty11s, ty01), Ty2 (ty12s, ty02) ->
      List.iter2 (typecheck1 ?at) ty11s ty12s;
      typecheck ?at ty01 ty02


(* {3 Main} *)

let rec expr cx oe =
  match oe.core with
  | Ix n ->
      let ty0 = lookup_ty0 cx n in
      (Ix n @@ oe, ty0)

  | _ ->
      error ~at:oe "Not implemented"

and eopr cx op =
  match op.core with
  | Ix n ->
      let ty2 = lookup_ty2 cx n in
      (Ix n @@ op, ty2)

  | Lambda (xs, e) ->
      let cx, ty1s =
        List.fold_left begin fun (cx, rty1s) (v, shp) ->
          let cx = adj cx v in
          let ty1 = lookup_ty1 cx 1 in
          (cx, ty1 :: rty1s)
        end (cx, []) xs
        |> fun (cx, rty1s) ->
            (cx, List.rev rty1s)
      in
      let e, ty0 = expr cx e in
      let ty2 = Ty2 (ty1s, ty0) in
      (Lambda (xs, e) @@ op, ty2)

  | _ ->
      error ~at:op "Not implemented"

and earg cx oa =
  match oa.core with
  | Ix n ->
      let ty1 = lookup_ty1 cx n in
      (Ix n @@ oa, ty1)

  | Lambda (xs, e) ->
      let cx, ty0s =
        List.fold_left begin fun (cx, rty0s) (v, shp) ->
          let cx = adj cx v in
          let ty0 = lookup_ty0 cx 1 in
          (cx, ty0 :: rty0s)
        end (cx, []) xs
        |> fun (cx, rty0s) ->
            (cx, List.rev rty0s)
      in
      let e, ty0 = expr cx e in
      let ty1 = Ty1 (ty0s, ty0) in
      (Lambda (xs, e) @@ oa, ty1)

  | _ ->
      let e, ty0 = expr cx oa in
      (e, upcast_ty1 ty0)

and bound cx (v, k, d) =
  (* FIXME Ditto? *)
  let d =
    match d with
    | Domain d ->
        let ty01 = get v Props.ty0_prop in
        let d, ty02 = expr cx d in
        begin match ty02 with
        | TSet ty02' ->
            typecheck ~at:v ty01 ty02'
        | _ ->
            typecheck ~at:v ty01 ty02
        end;
        Domain d
    | _ -> d
  in
  (v, k, d)

and bounds cx bs =
  List.fold_left begin fun (cx, rbs) b ->
    let (v, _, _ as b) = bound cx b in
    let cx = adj cx v in
    (cx, b :: rbs)
  end (cx, []) bs
  |> fun (cx, rbs) ->
      (cx, List.rev rbs)

and defn cx df =
  match df.core with
  | Operator (v, e) ->
      let ty01 = get v Props.ty2_prop in
      let e, ty02 = eopr cx e in
      typecheck2 ~at:v ty01 ty02;
      let cx = adj cx v in
      (cx, Operator (v, e) @@ df)

  | _ ->
      error ~at:df "Not implemented"

and defns cx dfs =
  List.fold_left begin fun (cx, rdfs) df ->
    let cx, df = defn cx df in
    (cx, df :: rdfs)
  end (cx, []) dfs
  |> fun (cx, rdfs) ->
      (cx, List.rev rdfs)

and hyp cx h =
  match h.core with
  | _ ->
      error ~at:h "Not implemented"

and hyps cx hs =
  match Deque.front hs with
  | None ->
      (cx, Deque.empty)
  | Some (h, hs) ->
      let cx, h = hyp cx h in
      let cx, hs = hyps cx hs in
      (cx, Deque.cons h hs)

and sequent cx sq =
  let cx, hs = hyps cx sq.context in
  let e, ty = expr cx sq.active in
  typecheck ~at:e t_bol ty;
  { context = hs; active = e }


let main sq =
  let cx = Ctx.dot in
  sequent cx sq

