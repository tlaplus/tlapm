(*
 * type/visit.ml --- visitors with syntactic typecheck
 *
 *
 * Copyright (C) 2022  INRIA and Microsoft Corporation
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

let check0 ?at ty01 ty02 =
  try typecheck ~expected:ty01 ~actual:ty01
  with Typechecking_error (ty01, ty02) ->
    let mssg = typecheck_error_mssg ~expected:ty01 ~actual:ty02 in
    error ?at mssg

let check2 ?at ty21 ty22 =
  try typecheck_op ~expected:ty21 ~actual:ty21
  with Typechecking_op_error (ty21, ty22) ->
    let mssg = typecheck_op_error_mssg ~expected:ty21 ~actual:ty22 in
    error ?at mssg

let check1 ?at ty11 ty12 =
  match safe_downcast_ty0 ty11, safe_downcast_ty0 ty12 with
  | Some ty01, Some ty02 ->
      check0 ?at ty01 ty02
  | _, _ ->
      check2 ?at (upcast_ty2 ty11) (upcast_ty2 ty12)

let iter3 f l1 l2 l3 =
  List.iter2 (fun a (b, c) -> f a b c)
  l1 (List.combine l2 l3)


(* {3 Context} *)

type 's scx = 's * hyp Deque.dq

let adj (s, cx) h =
  (s, Deque.snoc cx h)

let rec adjs scx = function
  | [] -> scx
  | h :: hs ->
      adjs (adj scx h) hs


let lookup_hint (_, hx) n =
  let h = Option.get (Deque.nth ~backwards:true hx (n - 1)) in
  hyp_hint h

let lookup_ty0 scx n =
  let v = lookup_hint scx n in
  if has v Props.ty0_prop then
    get v Props.ty0_prop
  else if has v Props.ty1_prop then
    downcast_ty0 (get v Props.ty1_prop)
  else if has v Props.ty2_prop then
    downcast_ty0 (downcast_ty1 (get v Props.ty2_prop))
  else
    error ~at:v "Cannot find type0 annotation"

(* Get the n last ty0s *)
let lookup_ty0_mult scx n =
  List.init n (lookup_ty0 scx)

let lookup_ty1 scx n =
  let v = lookup_hint scx n in
  if has v Props.ty1_prop then
    get v Props.ty1_prop
  else if has v Props.ty0_prop then
    upcast_ty1 (get v Props.ty0_prop)
  else if has v Props.ty2_prop then
    downcast_ty1 (get v Props.ty2_prop)
  else
    error ~at:v "Cannot find type1 annotation"

let lookup_ty2 scx n =
  let v = lookup_hint scx n in
  if has v Props.ty2_prop then
    get v Props.ty2_prop
  else if has v Props.ty0_prop then
    upcast_ty2 (upcast_ty1 (get v Props.ty0_prop))
  else if has v Props.ty1_prop then
    upcast_ty2 (get v Props.ty1_prop)
  else
    error ~at:v "Cannot find type2 annotation"


class virtual ['s, 'a] foldmap = object (self : 'self)

  method expr (scx : 's scx) a oe =

    if has oe Props.icast_prop then
      let ty01 = get oe Props.icast_prop in
      let oe = remove oe Props.icast_prop in
      let a, oe, ty02 = self#expr scx a oe in
      check0 ~at:oe ty01 ty02;
      (a, assign oe Props.icast_prop ty02, TAtm TAIdv)
    else

    if has oe Props.bproj_prop then
      let ty01 = get oe Props.bproj_prop in
      let oe = remove oe Props.bproj_prop in
      let a, oe, ty02 = self#expr scx a oe in
      check0 ~at:oe ty01 ty02;
      (a, assign oe Props.bproj_prop ty02, TAtm TABol)
    else

    match oe.core with
    | Ix n ->
        let ty0 = lookup_ty0 scx n in
        (a, Ix n @@ oe, ty0)
    | Opaque o ->
        let ty0 =
          if has oe Props.ty0_prop then
            get oe Props.ty0_prop
          else if has oe Props.ty2_prop then try
            get oe Props.ty2_prop |>
            downcast_ty1 |>
            downcast_ty0
          with Invalid_type_downcast ->
            let mssg = "Expected constant opaque opaque '" ^ o ^ "'" in
            error ~at:oe mssg
          else
            let mssg = "Missing annotation on opaque '" ^ o ^ "'" in
            error ~at:oe mssg
        in
        (a, Opaque o @@ oe, ty0)
    | Internal b ->
        let a, oe, ty2 = self#eopr scx a oe in
        let ty0 =
          try downcast_ty0 (downcast_ty1 ty2)
          with Invalid_type_downcast ->
            error ~at:oe "Expected constant builtin"
        in
        (a, Internal b @@ oe, ty0)
    | String s ->
        (a, String s @@ oe, TAtm TAStr)
    | Num (m, "") ->
        (a, Num (m, "") @@ oe, TAtm TAInt)
    | Num (m, n) ->
        (a, Num (m, n) @@ oe, TAtm TARel)
    | Apply (op, es) ->
        let a, op, Ty2 (ty11s, ty0) = self#eopr scx a op in
        let a, es, ty12s =
          List.fold_left begin fun (a, r_es, r_ty1s) e ->
            let a, e, ty1 = self#earg scx a e in
            (a, e :: r_es, ty1 :: r_ty1s)
          end (a, [], []) es |>
          fun (a, r_es, r_ty1s) -> (a, List.rev r_es, List.rev r_ty1s)
        in
        iter3 (fun e -> check1 ~at:e) es ty11s ty12s;
        (a, Apply (op, es) @@ oe, ty0)
    | Sequent sq ->
        let _, a, sq = self#sequent scx a sq in
        (a, Sequent sq @@ oe, TAtm TABol)
    | With (e, m) ->
        let a, e, ty0 = self#expr scx a e in
        (a, With (e, m) @@ oe, ty0)
    | Let (ds, e) ->
        let scx, a, ds = self#defns scx a ds in
        let a, e, ty0 = self#expr scx a e in
        (a, Let (ds, e) @@ oe, ty0)
    | If (e, f, g) ->
        let a, e, ty01 = self#expr scx a e in
        let a, f, ty02 = self#expr scx a f in
        let a, g, ty03 = self#expr scx a g in
        begin match query oe Props.tpars_prop with
        | None ->
            check0 ~at:e (TAtm TABol) ty01;
            check0 ~at:g ty02 ty03;
            (a, If (e, f, g) @@ oe, ty02)
        | Some ([ ty04 ]) ->
            check0 ~at:e (TAtm TABol) ty01;
            check0 ~at:f ty04 ty02;
            check0 ~at:g ty04 ty03;
            (a, If (e, f, g) @@ oe, ty04)
        | _ ->
            error ~at:oe "Bad type annotation"
        end
    | List (Refs, [e]) ->
        let a, e, ty0 = self#expr scx a e in
        (a, List (Refs, [e]) @@ oe, ty0)
    | List (q, es) ->
        let a, es =
          List.fold_left begin fun (a, r_es) e ->
            let a, e, ty0 = self#expr scx a e in
            check0 ~at:e (TAtm TABol) ty0;
            (a, e :: r_es)
          end (a, []) es |>
          fun (a, r_es) -> (a, List.rev r_es)
        in
        (a, List (q, es) @@ oe, TAtm TABol)
    | Quant (q, bs, e) ->
        let scx, a, bs = self#bounds scx a bs in
        let a, e, ty0 = self#expr scx a e in
        check0 ~at:e (TAtm TABol) ty0;
        (a, Quant (q, bs, e) @@ oe, TAtm TABol)
    | Tquant (q, vs, e) ->
        let scx = adjs scx (List.map begin fun v ->
          Flex v @@ v
        end vs) in
        let a, e, ty0 = self#expr scx a e in
        check0 ~at:e (TAtm TABol) ty0;
        (a, Tquant (q, vs, e) @@ oe, TAtm TABol)
    | Choose (v, optdom, e) ->
        let a, optdom, h =
          match optdom with
          | None ->
              (a, None, Fresh (v, Shape_expr, Constant, Unbounded) @@ v)
          | Some dom ->
              let ty01 = get v Props.ty0_prop in
              let a, dom, ty02 = self#expr scx a dom in
              begin match query v Props.mpars_prop with
              | None ->
                  check0 ~at:v (TAtm TAIdv) ty01;
                  check0 ~at:dom (TAtm TAIdv) ty02;
                  (a, Some dom, Fresh (v, Shape_expr, Constant, Bounded (dom, Visible)) @@ v)
              | Some ty03 ->
                  check0 ~at:v ty03 ty01;
                  check0 ~at:dom (TSet ty03) ty02;
                  (a, Some dom, Fresh (v, Shape_expr, Constant, Bounded (dom, Visible)) @@ v)
              end
        in
        let scx = adj scx h in
        let a, e, ty0 = self#expr scx a e in
        check0 ~at:e (TAtm TABol) ty0;
        (a, Choose (v, optdom, e) @@ oe, TAtm TAIdv)
    | SetSt (v, dom, e) ->
        let ty01 = get v Props.ty0_prop in
        let a, dom, ty02 = self#expr scx a dom in
        let scx = adj scx (Fresh (v, Shape_expr, Constant, Bounded (dom, Visible)) @@ v) in
        let a, e, ty03 = self#expr scx a e in
        begin match query oe Props.tpars_prop with
        | None ->
            check0 ~at:v (TAtm TAIdv) ty01;
            check0 ~at:dom (TAtm TAIdv) ty02;
            check0 ~at:e (TAtm TABol) ty03;
            (a, SetSt (v, dom, e) @@ oe, TAtm TAIdv)
        | Some ([ ty04 ]) ->
            check0 ~at:v ty04 ty01;
            check0 ~at:dom (TSet ty04) ty02;
            check0 ~at:e (TAtm TABol) ty03;
            (a, SetSt (v, dom, e) @@ oe, TSet ty04)
        | _ ->
            error ~at:oe "Bad type annotation"
        end
    | SetOf (e, bs) ->
        let scx, a, bs = self#bounds scx a bs in
        let n = List.length bs in
        let ty01s = lookup_ty0_mult scx n in
        (* /!\ Check bound types BEFORE the body *)
        begin match query oe Props.tpars_prop with
        | None ->
            List.iter2 (fun v -> check0 ~at:v (TAtm TAIdv)) (List.map (fun (v, _, _) -> v) bs) ty01s;
            let a, e, ty02 = self#expr scx a e in
            check0 ~at:e (TAtm TAIdv) ty02;
            (a, SetOf (e, bs) @@ oe, TAtm TAIdv)
        | Some (ty04 :: ty03s) ->
            iter3 (fun (v, _, _) -> check0 ~at:v) bs ty03s ty01s;
            let a, e, ty02 = self#expr scx a e in
            check0 ~at:e ty04 ty02;
            (a, SetOf (e, bs) @@ oe, TSet ty04)
        | _ ->
            error ~at:oe "Bad type annotation"
        end
    | SetEnum es ->
        let a, es, ty01s =
          List.fold_left begin fun (a, r_es, r_ty0s) e ->
            let a, e, ty0 = self#expr scx a e in
            (a, e :: r_es, ty0 :: r_ty0s)
          end (a, [], []) es |>
          fun (a, r_es, r_ty0s) -> (a, List.rev r_es, List.rev r_ty0s)
        in
        begin match query oe Props.tpars_prop with
        | None ->
            List.iter2 (fun e -> check0 ~at:e (TAtm TAIdv)) es ty01s;
            (a, SetEnum es @@ oe, TAtm TAIdv)
        | Some ([ ty02 ]) ->
            List.iter2 (fun e -> check0 ~at:e ty02) es ty01s;
            (a, SetEnum es @@ oe, TSet ty02)
        | _ ->
            error ~at:oe "Bad type annotation"
        end
    | Fcn (bs, e) ->
        let scx, a, bs = self#bounds scx a bs in
        let n = List.length bs in
        let ty01s = lookup_ty0_mult scx n in
        (* /!\ Check bound types BEFORE the body *)
        begin match query oe Props.tpars_prop with
        | None ->
            List.iter2 (fun (v, _, _) -> check0 ~at:v (TAtm TAIdv)) bs ty01s;
            let a, e, ty02 = self#expr scx a e in
            check0 (TAtm TAIdv) ty02;
            (a, Fcn (bs, e) @@ oe, TAtm TAIdv)
        | Some ([ ty03 ; ty04 ]) when n = 1 ->
            let v, _, _ = List.hd bs in
            check0 ~at:v ty03 (List.hd ty01s);
            let a, e, ty02 = self#expr scx a e in
            check0 ty04 ty02;
            (a, Fcn (bs, e) @@ oe, TFun (ty03, ty04))
        | Some (ty03s) when List.length ty03s = n+1 && n > 1 ->
            let ty04s, ty05 =
              match List.rev ty03s with
              | ty05 :: r_ty04s -> List.rev r_ty04s, ty05
              | _ -> error ~at:oe "Bat type annotation"
            in
            iter3 (fun (v, _, _) -> check0 ~at:v) bs ty04s ty01s;
            let a, e, ty02 = self#expr scx a e in
            check0 ty05 ty02;
            (a, Fcn (bs, e) @@ oe, TFun (TPrd ty04s, ty05))
        | _ ->
            error ~at:oe "Bad type annotation"
        end
    | FcnApp (f, es) ->
        let a, f, ty01 = self#expr scx a f in
        let a, es, ty02s =
          List.fold_left begin fun (a, r_es, r_ty0s) e ->
            let a, e, ty0 = self#expr scx a e in
            (a, e :: r_es, ty0 :: r_ty0s)
          end (a, [], []) es |>
          fun (a, r_es, r_ty0s) -> (a, List.rev r_es, List.rev r_ty0s)
        in
        let n = List.length es in
        begin match query oe Props.tpars_prop with
        | None ->
            check0 (TAtm TAIdv) ty01;
            List.iter2 (fun e -> check0 ~at:e (TAtm TAIdv)) es ty02s;
            (a, FcnApp (f, es) @@ oe, TAtm TAIdv)
        | Some ([ ty03 ; ty04 ]) when n = 1 ->
            check0 (TFun (ty03, ty04)) ty01;
            List.iter2 (fun e -> check0 ~at:e ty03) es ty02s;
            (a, FcnApp (f, es) @@ oe, ty04)
        | Some (ty03s) when List.length ty03s = n+1 && n > 1 ->
            let ty04s, ty05 =
              match List.rev ty03s with
              | ty05 :: r_ty04s -> List.rev r_ty04s, ty05
              | _ -> error ~at:oe "Bad type annotation"
            in
            check0 (TFun (TPrd ty04s, ty05)) ty01;
            iter3 (fun e -> check0 ~at:e) es ty04s ty02s;
            (a, FcnApp (f, es) @@ oe, ty05)
        | _ ->
            error ~at:oe "Bad type annotation"
        end
    | Arrow (e, f) ->
        let a, e, ty01 = self#expr scx a e in
        let a, f, ty02 = self#expr scx a f in
        begin match query oe Props.tpars_prop with
        | None ->
            check0 (TAtm TAIdv) ty01;
            check0 (TAtm TAIdv) ty02;
            (a, Arrow (e, f) @@ oe, TAtm TAIdv)
        | Some ([ ty03 ; ty04 ]) ->
            check0 (TSet ty03) ty01;
            check0 (TSet ty04) ty02;
            (a, Arrow (e, f) @@ oe, TSet (TFun (ty03, ty04)))
        | _ ->
            error ~at:oe "Bad type annotation"
        end
    | Product es ->
        let a, es, ty01s =
          List.fold_left begin fun (a, r_es, r_ty0s) e ->
            let a, e, ty0 = self#expr scx a e in
            (a, e :: r_es, ty0 :: r_ty0s)
          end (a, [], []) es |>
          fun (a, r_es, r_ty0s) -> (a, List.rev r_es, List.rev r_ty0s)
        in
        begin match query oe Props.tpars_prop with
        | None ->
            List.iter2 (fun e -> check0 ~at:e (TAtm TAIdv)) es ty01s;
            (a, Product es @@ oe, TAtm TAIdv)
        | Some ty02s ->
            iter3 (fun e -> check0 ~at:e) es ty02s ty01s;
            (a, Product es @@ oe, TSet (TPrd ty02s))
        end
    | Tuple es ->
        let a, es, ty01s =
          List.fold_left begin fun (a, r_es, r_ty0s) e ->
            let a, e, ty0 = self#expr scx a e in
            (a, e :: r_es, ty0 :: r_ty0s)
          end (a, [], []) es |>
          fun (a, r_es, r_ty0s) -> (a, List.rev r_es, List.rev r_ty0s)
        in
        begin match query oe Props.tpars_prop with
        | None ->
            List.iter2 (fun e -> check0 ~at:e (TAtm TAIdv)) es ty01s;
            (a, Product es @@ oe, TAtm TAIdv)
        | Some ty02s ->
            iter3 (fun e -> check0 ~at:e) es ty02s ty01s;
            (a, Product es @@ oe, TPrd ty02s)
        end
    | Except (e, xs) ->
        let a, e, ty01 = self#expr scx a e in
        let a, xs, exty02ss =
          List.fold_left begin fun (a, r_xs, r_exty02ss) x ->
            let a, x, exty02s = self#exspec scx a x in
            (a, x :: r_xs, exty02s :: r_exty02ss)
          end (a, [], []) xs |>
          fun (a, r_xs, r_exty02s) ->
            (a, List.rev r_xs, List.rev r_exty02s)
        in
        begin match query oe Props.tpars_prop with
        | None ->
            (a, Except (e, xs) @@ oe, TAtm TAIdv)
        | Some ty03s when List.length ty03s > 0 ->
            let mk_fcn_ty = List.fold_right (fun ty01 ty02 -> TFun (ty01, ty02)) in
            let split_last l =
              match List.rev l with
              | a :: r_l -> List.rev r_l, a
              | _ -> failwith ""
            in
            let ty04s, ty05 = split_last ty03s in
            check0 (mk_fcn_ty ty04s ty05) ty01;
            List.iter begin fun ty02s ->
              let ty06s, ty07 = split_last ty02s in
              let rec spin = function
                | [], ty04s -> ty04s
                | ty06 :: ty06s, ty04 :: ty04s ->
                    check0 ty04 ty06;
                    spin (ty06s, ty04s)
                | _ ->
                    failwith ""
              in
              let ty08s = spin (ty06s, ty04s) in
              check0 (mk_fcn_ty ty08s ty05) ty07
            end exty02ss;
            (a, Except (e, xs) @@ oe, ty01)
        | _ ->
            error ~at:oe "Bad type annotation"
        end
    | Dot (e, f) ->
        let a, e, ty01 = self#expr scx a e in
        begin match query oe Props.tpars_prop with
        | None ->
            (a, Dot (e, f) @@ oe, TAtm TAIdv)
        | Some [ ty02 ] ->
            check0 (TFun (TAtm TAStr, ty02)) ty01;
            (a, Dot (e, f) @@ oe, ty02)
        | _ ->
            error ~at:oe "Bad type annotation"
        end
    | Case (arms, oth) ->
        let a, arms, ty01s =
          List.fold_left begin fun (a, r_arms, r_ty0s) (e, f) ->
            let a, e, ty01 = self#expr scx a e in
            let a, f, ty02 = self#expr scx a f in
            check0 (TAtm TABol) ty01;
            (a, (e, f) :: r_arms, ty02 :: r_ty0s)
          end (a, [], []) arms |>
          fun (a, r_arms, r_ty0s) -> (a, List.rev r_arms, List.rev r_ty0s)
        in
        let a, oth, oty02 =
          match oth with
          | None ->
              (a, None, None)
          | Some o ->
              let a, o, ty02 = self#expr scx a o in
              (a, Some o, Some ty02)
        in
        begin match query oe Props.tpars_prop with
        | None ->
            (a, Case (arms, oth) @@ oe, TAtm TAIdv)
        | Some ([ ty03 ]) ->
            List.iter2 (fun (_, e) -> check0 ~at:e ty03) arms ty01s;
            (* if a type is present then oth is some expression *)
            Option.iter (check0 ~at:(Option.get oth) ty03) oty02;
            (a, Case (arms, oth) @@ oe, ty03)
        | _ ->
            error ~at:oe "Bad type annotation"
        end
    | Parens (e, pf) ->
        let a, e, ty0 = self#expr scx a e in
        let a, pf = self#pform scx a pf in
        (a, Parens (e, pf) @@ oe, ty0)
    | _ ->
        error ~at:oe "Not supported"

  method earg scx a ea =
    match ea.core with
    | Ix n ->
        let ty1 = lookup_ty1 scx n in
        (a, Ix n @@ ea, ty1)
    | Lambda (vs, e) ->
        let scx = adjs scx (List.map begin fun (v, shp) ->
          Fresh (v, shp, Unknown, Unbounded) @@ v
        end vs) in
        let ty01s =
          let n = List.length vs in
          List.init n (fun i -> lookup_ty0 scx (n - i))
        in
        let a, e, ty02 = self#expr scx a e in
        (a, Lambda (vs, e) @@ ea, Ty1 (ty01s, ty02))
    | _ ->
        let a, ea, ty0 = self#expr scx a ea in
        (a, ea, upcast_ty1 ty0)

  method eopr scx a ep =
    match ep.core with
    | Ix n ->
        let ty2 = lookup_ty2 scx n in
        (a, Ix n @@ ep, ty2)
    | Opaque o ->
        let ty2 =
          if has ep Props.ty2_prop then
            get ep Props.ty2_prop
          else
            let mssg = "Missing annotation on opaque '" ^ o ^ "'" in
            error ~at:ep mssg
        in
        (a, Opaque o @@ ep, ty2)
    | Lambda (vs, e) ->
        let scx = adjs scx (List.map begin fun (v, shp) ->
          Fresh (v, shp, Unknown, Unbounded) @@ v
        end vs) in
        let ty1s =
          let n = List.length vs in
          List.init n (fun i -> lookup_ty1 scx (n - i - 1))
        in
        let a, e, ty0 = self#expr scx a e in
        (a, Lambda (vs, e) @@ ep, Ty2 (ty1s, ty0))
    | Internal b ->
        (* all builtins are first-order *)
        let mk_ty2 ty0s ty0 = Ty1 (ty0s, ty0) |> upcast_ty2 in
        let ty2 =
          match b, query ep Props.tpars_prop with
          | B.TRUE, _           -> mk_ty2 [] (TAtm TABol)
          | B.FALSE, _          -> mk_ty2 [] (TAtm TABol)
          | B.Implies, _        -> mk_ty2 [TAtm TABol; TAtm TABol] (TAtm TABol)
          | B.Equiv, _          -> mk_ty2 [TAtm TABol; TAtm TABol] (TAtm TABol)
          | B.Conj, _           -> mk_ty2 [TAtm TABol; TAtm TABol] (TAtm TABol)
          | B.Disj, _           -> mk_ty2 [TAtm TABol; TAtm TABol] (TAtm TABol)
          | B.Neg, _            -> mk_ty2 [TAtm TABol] (TAtm TABol)
          | B.Eq, None          -> mk_ty2 [TAtm TAIdv; TAtm TAIdv] (TAtm TABol)
          | B.Neq, None         -> mk_ty2 [TAtm TAIdv; TAtm TAIdv] (TAtm TABol)
          | B.Eq, Some ([ty0])  -> mk_ty2 [ty0; ty0] (TAtm TABol)
          | B.Neq, Some ([ty0]) -> mk_ty2 [ty0; ty0] (TAtm TABol)

          | B.STRING, None      -> mk_ty2 [] (TAtm TAIdv)
          | B.BOOLEAN, None     -> mk_ty2 [] (TAtm TAIdv)
          | B.SUBSET, None      -> mk_ty2 [TAtm TAIdv] (TAtm TAIdv)
          | B.UNION, None       -> mk_ty2 [TAtm TAIdv] (TAtm TAIdv)
          | B.DOMAIN, None      -> mk_ty2 [TAtm TAIdv] (TAtm TAIdv)
          | B.Subseteq, None    -> mk_ty2 [TAtm TAIdv; TAtm TAIdv] (TAtm TABol)
          | B.Mem, None         -> mk_ty2 [TAtm TAIdv; TAtm TAIdv] (TAtm TABol)
          | B.Notmem, None      -> mk_ty2 [TAtm TAIdv; TAtm TAIdv] (TAtm TABol)
          | B.Setminus, None    -> mk_ty2 [TAtm TAIdv; TAtm TAIdv] (TAtm TAIdv)
          | B.Cap, None         -> mk_ty2 [TAtm TAIdv; TAtm TAIdv] (TAtm TAIdv)
          | B.Cup, None         -> mk_ty2 [TAtm TAIdv; TAtm TAIdv] (TAtm TAIdv)
          | B.STRING, Some ([])           -> mk_ty2 [] (TSet (TAtm TAStr))
          | B.BOOLEAN, Some ([])          -> mk_ty2 [] (TSet (TAtm TABol))
          | B.SUBSET, Some ([ty0])        -> mk_ty2 [TSet ty0] (TSet (TSet ty0))
          | B.UNION, Some ([ty0])         -> mk_ty2 [TSet (TSet ty0)] (TSet ty0)
          | B.DOMAIN, Some ([ty01; ty02]) -> mk_ty2 [TFun (ty01, ty02)] (TSet ty01)
          | B.Subseteq, Some ([ty0])     -> mk_ty2 [TSet ty0; TSet ty0] (TAtm TABol)
          | B.Mem, Some ([ty0])          -> mk_ty2 [ty0; ty0] (TAtm TABol)
          | B.Notmem, Some ([ty0])       -> mk_ty2 [ty0; ty0] (TAtm TABol)
          | B.Setminus, Some ([ty0])     -> mk_ty2 [TSet ty0; TSet ty0] (TSet ty0)
          | B.Cap, Some ([ty0])          -> mk_ty2 [TSet ty0; TSet ty0] (TSet ty0)
          | B.Cup, Some ([ty0])          -> mk_ty2 [TSet ty0; TSet ty0] (TSet ty0)

          | B.Nat, None         -> mk_ty2 [] (TAtm TAIdv)
          | B.Int, None         -> mk_ty2 [] (TAtm TAIdv)
          | B.Real, None        -> mk_ty2 [] (TAtm TAIdv)
          | B.Plus, None        -> mk_ty2 [TAtm TAIdv; TAtm TAIdv] (TAtm TAIdv)
          | B.Minus, None       -> mk_ty2 [TAtm TAIdv; TAtm TAIdv] (TAtm TAIdv)
          | B.Uminus, None      -> mk_ty2 [TAtm TAIdv] (TAtm TAIdv)
          | B.Times, None       -> mk_ty2 [TAtm TAIdv; TAtm TAIdv] (TAtm TAIdv)
          | B.Ratio, None       -> mk_ty2 [TAtm TAIdv; TAtm TAIdv] (TAtm TAIdv)
          | B.Quotient, None    -> mk_ty2 [TAtm TAIdv; TAtm TAIdv] (TAtm TAIdv)
          | B.Remainder, None   -> mk_ty2 [TAtm TAIdv; TAtm TAIdv] (TAtm TAIdv)
          | B.Exp, None         -> mk_ty2 [TAtm TAIdv; TAtm TAIdv] (TAtm TAIdv)
          | B.Infinity, None    -> mk_ty2 [] (TAtm TAIdv)
          | B.Lteq, None        -> mk_ty2 [TAtm TAIdv; TAtm TAIdv] (TAtm TABol)
          | B.Lt, None          -> mk_ty2 [TAtm TAIdv; TAtm TAIdv] (TAtm TABol)
          | B.Gteq, None        -> mk_ty2 [TAtm TAIdv; TAtm TAIdv] (TAtm TABol)
          | B.Gt, None          -> mk_ty2 [TAtm TAIdv; TAtm TAIdv] (TAtm TABol)
          | B.Range, None       -> mk_ty2 [TAtm TAIdv; TAtm TAIdv] (TAtm TAIdv)
          | B.Nat, Some ([])            -> mk_ty2 [] (TSet (TAtm TAInt))
          | B.Int, Some ([])            -> mk_ty2 [] (TSet (TAtm TAInt))
          | B.Real, Some ([])           -> mk_ty2 [] (TSet (TAtm TARel))
          | B.Plus, Some ([ty0])        -> mk_ty2 [ty0; ty0] ty0
          | B.Minus, Some ([ty0])       -> mk_ty2 [ty0; ty0] ty0
          | B.Uminus, Some ([ty0])      -> mk_ty2 [ty0] ty0
          | B.Times, Some ([ty0])       -> mk_ty2 [ty0; ty0] ty0
          | B.Ratio, Some ([ty0])       -> mk_ty2 [ty0; ty0] ty0
          | B.Quotient, Some ([ty0])    -> mk_ty2 [ty0; ty0] ty0
          | B.Remainder, Some ([ty0])   -> mk_ty2 [ty0; ty0] ty0
          | B.Exp, Some ([ty0])         -> mk_ty2 [ty0; ty0] ty0
          | B.Infinity, Some ([])       -> mk_ty2 [] (TAtm TARel)
          | B.Lteq, Some ([ty0])        -> mk_ty2 [ty0; ty0] (TAtm TABol)
          | B.Lt, Some ([ty0])          -> mk_ty2 [ty0; ty0] (TAtm TABol)
          | B.Gteq, Some ([ty0])        -> mk_ty2 [ty0; ty0] (TAtm TABol)
          | B.Gt, Some ([ty0])          -> mk_ty2 [ty0; ty0] (TAtm TABol)
          | B.Range, Some ([])          -> mk_ty2 [TAtm TAInt; TAtm TAInt] (TSet (TAtm TAInt))

          | _, _ -> error "Builtin not supported"
        in
        (a, Internal b @@ ep, ty2)
    | _ ->
        let a, ep, ty0 = self#expr scx a ep in
        (a, ep, Ty2 ([], ty0))

  method pform scx a pf =
    (a, pf)

  method sel scx a sel =
    match sel with
    | Sel_inst args ->
        let a, args =
          List.fold_left begin fun (a, r_args) e ->
            let a, e, _ = self#expr scx a e in
            (a, e :: r_args)
          end (a, []) args |>
          fun (a, r_args) -> (a, List.rev r_args)
        in
        (a, Sel_inst args)
    | Sel_lab (l, args) ->
        let a, e =
          List.fold_left begin fun (a, r_args) e ->
            let a, e, _ = self#expr scx a e in
            (a, e :: r_args)
          end (a, []) args |>
          fun (a, r_args) -> (a, List.rev r_args)
        in
        (a, Sel_lab (l, args))
    | _ ->
        (a, sel)

  method sequent scx a sq =
    let scx, a, hyps = self#hyps scx a sq.context in
    let a, act, ty0 = self#expr scx a sq.active in
    check0 (TAtm TABol) ty0;
    (scx, a, { context = hyps ; active = act })

  method defn scx a df =
    match df.core with
      | Recursive (v, shp) ->
          (a, Recursive (v, shp) @@ df)
      | Operator (v, e) ->
          let ty21 = get v Props.ty2_prop in
          let a, e, ty22 = self#eopr scx a e in
          check2 ~at:df ty21 ty22;
          (a, Operator (v, e) @@ df)
      | Instance (v, i) ->
          let a, i = self#instance scx a i in
          (a, Instance (v, i) @@ df)
      | Bpragma (v, e, l) ->
          let a, e, _ = self#expr scx a e in
          (a, Bpragma (v, e, l) @@ df)

  method defns scx a ds =
    match ds with
    | [] -> scx, a, []
    | df :: dfs ->
        let a, df = self#defn scx a df in
        let scx = adj scx (Defn (df, User, Visible, Local) @@ df) in
        let scx, a, dfs = self#defns scx a dfs in
        (scx, a, df :: dfs)

  method bounds scx a bs =
    let a, bs =
      List.fold_left begin fun (a, r_bs) (v, k, dom) ->
        match dom with
        | Domain d ->
            let ty01 = get v Props.ty0_prop in
            let a, d, ty02 = self#expr scx a d in
            begin match query d Props.mpars_prop with
            | None ->
                check0 (TAtm TAIdv) ty01;
                check0 (TAtm TAIdv) ty02;
                (a, (v, k, Domain d) :: r_bs)
            | Some ty03 ->
                check0 ty03 ty01;
                check0 (TSet ty03) ty02;
                (a, (v, k, Domain d) :: r_bs)
            end
        | _ ->
            (a, (v, k, dom) :: r_bs)
      end (a, []) bs |>
      fun (a, r_bs) -> (a, List.rev r_bs)
    in
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
    let a, trail, ty01s =
      List.fold_left begin fun (a, r_trail, r_ty0s) x ->
        match x with
        | Except_dot s ->
            (a, (Except_dot s) :: r_trail, TAtm TAStr :: r_ty0s)
        | Except_apply e ->
            let a, e, ty0 = self#expr scx a e in
            (a, (Except_apply e) :: r_trail, ty0 :: r_ty0s)
      end (a, [], []) trail |>
      fun (a, r_trail, r_ty0s) ->
        (a, List.rev r_trail, List.rev r_ty0s)
    in
    let a, res, ty02 = self#expr scx a res in
    (a, (trail, res), ty01s @ [ ty02 ])

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
    | Fresh (v, shp, lc, dom) ->
        let a, dom =
          match dom with
          | Unbounded ->
              (a, Unbounded)
          | Bounded (e, rvis) ->
              let ty01 = get v Props.ty0_prop in
              let a, e, ty02 = self#expr scx a e in
              begin match query e Props.mpars_prop with
              | None ->
                  check0 (TAtm TAIdv) ty01;
                  check0 (TAtm TAIdv) ty02;
                  (a, Bounded (e, rvis))
              | Some ty03 ->
                  check0 ty03 ty01;
                  check0 (TSet ty03) ty02;
                  (a, Bounded (e, rvis))
              end
        in
        let h = Fresh (v, shp, lc, dom) @@ h in
        let scx = adj scx h in
        (scx, a, h)
    | Flex s ->
        let h = Flex s @@ h in
        let scx = adj scx h in
        (scx, a, h)
    | Defn (_, _, Hidden, _)
    | Fact (_, Hidden, _) ->
        let scx = adj scx h in
        (scx, a, h)
    | Defn (df, wd, vis, ex) ->
        let a, df = self#defn scx a df in
        let h = Defn (df, wd, vis, ex) @@ h in
        let scx = adj scx h in
        (scx, a, h)
    | Fact (e, vis, tm) ->
        let a, e, ty0 = self#expr scx a e in
        check0 (TAtm TABol) ty0;
        let h = Fact (e, vis, tm) @@ h in
        let scx = adj scx h in
        (scx, a, h)
    | FreshTuply _ ->
        failwith "unexpected case"

  method hyps scx a hs =
    match Deque.front hs with
    | None -> scx, a, Deque.empty
    | Some (h, hs) ->
        let scx, a, h = self#hyp scx a h in
        let scx, a, hs = self#hyps scx a hs in
        (scx, a, Deque.cons h hs)
end

