(*
 * type/bool.ml --- sort formulas and non-formulas
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

open Expr.T
open T_t

open Ext
open Property
open Util

module B = Builtin

let error ?at mssg =
  let mssg = "Type.Bool: " ^ mssg in
  Errors.bug ?at mssg


(* {3 Types and Conversions} *)

type srt = Idv | Bool
type ty1 = Ty1 of srt list * srt
type ty2 = Ty2 of ty1 list * srt

let from_ty0 = function
  | TAtm TAIdv -> Idv
  | TAtm TABol -> Bool
  | _ -> error "Invalid conversion from ty0"

let from_ty1 = function
  | T_t.Ty1 (ty0s, ty) -> Ty1 (List.map from_ty0 ty0s, from_ty0 ty)

let from_ty2 = function
  | T_t.Ty2 (ty1s, ty) -> Ty2 (List.map from_ty1 ty1s, from_ty0 ty)

let to_ty0 = function
  | Idv -> TAtm TAIdv
  | Bool -> TAtm TABol

let to_ty1 = function
  | Ty1 (srts, srt) -> T_t.Ty1 (List.map to_ty0 srts, to_ty0 srt)

let to_ty2 = function
  | Ty2 (ty1s, srt) -> T_t.Ty2 (List.map to_ty1 ty1s, to_ty0 srt)

let shp_to_ty1 = function
  | Shape_expr -> Ty1 ([], Idv)
  | Shape_op n -> Ty1 (List.init n (fun _ -> Idv), Idv)


(* {3 Context} *)

type ty = TySrt of srt | TyTy1 of ty1 | TyTy2 of ty2
type scx = ty Ctx.t

let init = Ctx.dot

let adj_srt scx v srt =
  let scx = Ctx.adj scx v.core (TySrt srt) in
  let v = assign v Props.ty0_prop (to_ty0 srt) in
  (v, scx)

let adj_ty1 scx v ty1 =
  let scx = Ctx.adj scx v.core (TyTy1 ty1) in
  let v = assign v Props.ty1_prop (to_ty1 ty1) in
  (v, scx)

let adj_ty2 scx v ty2 =
  let scx = Ctx.adj scx v.core (TyTy2 ty2) in
  let v = assign v Props.ty2_prop (to_ty2 ty2) in
  (v, scx)

let bump scx = Ctx.bump scx

let lookup_srt scx n =
  match snd (Ctx.index scx n) with
  | None -> error "Missing annotation"
  | Some (TySrt srt) -> srt
  | Some (TyTy1 (Ty1 ([], srt))) -> srt
  | Some (TyTy2 (Ty2 ([], srt))) -> srt
  | Some _ -> error "Cannot convert annotation to a sort"

let lookup_ty1 scx n =
  match snd (Ctx.index scx n) with
  | None -> error "Missing annotation"
  | Some (TySrt srt) -> Ty1 ([], srt)
  | Some (TyTy1 ty1) -> ty1
  | Some (TyTy2 (Ty2 (ty1s, srt))) ->
      Ty1 (List.map begin function
        | Ty1 ([], srt) -> srt
        | _ -> error "Cannot convert annotation to a sort"
      end ty1s, srt)

let lookup_ty2 scx n =
  match snd (Ctx.index scx n) with
  | None -> error "Missing annotation"
  | Some (TySrt srt) -> Ty2 ([], srt)
  | Some (TyTy1 (Ty1 (srts, srt))) ->
      Ty2 (List.map (fun srt -> Ty1 ([], srt)) srts, srt)
  | Some (TyTy2 ty2) -> ty2


(* {3 Main} *)

(* Options defined globally but not visible outside the module
 * for convenience.  Default values set in {!main}. *)
let opt_hidden = ref false
let opt_bunify = ref false
let opt_ccast = ref false
let opt_tpred = ref false

let mk_idv srt e =
  match srt with
  | Idv -> e
  | Bool -> assign e Props.icast_prop (TAtm TABol)

let mk_bool srt e =
  match srt with
  | Idv -> assign e Props.bproj_prop (TAtm TAIdv)
  | Bool -> e

(* Convert first-order operators;
 * [ty11] is the expected type, [ty12] the actual type. *)
let mk_ty1 ty11 ty12 op =
  match ty11, ty12 with
  | Ty1 ([], srt1),  Ty1 ([], srt2) ->
      let mk =
        match srt1 with Idv -> mk_idv | Bool -> mk_bool
      in
      mk srt2 op
  | Ty1 (srt1s, srt1), Ty1 (srt2s, srt2)
    when List.for_all2 (=) srt1s srt2s && srt1 = srt2 -> op
  | Ty1 (srt1s, srt1),  Ty1 (srt2s, srt2)
    when List.for_all2 (=) srt1s srt2s && !opt_tpred ->
      (* NOTE I am pretty sure this case will always occur
       * when a predicate must be converted to a non-predicate,
       * and never the converse. *)
      let mk =
        match srt1 with Idv -> mk_idv | Bool -> mk_bool
      in
      let xs =
        List.mapi begin fun i srt ->
          let v = ("x" ^ string_of_int i) %% [] in
          let v = assign v Props.ty0_prop (to_ty0 srt) in
          (v, Shape_expr)
        end srt1s
      in
      let n = List.length srt1s in
      let op = Expr.Subst.app_expr (Expr.Subst.shift n) op in
      let op = Apply (op, List.init n (fun i -> Ix (n - i + 1) %% [])) %% [] in
      Lambda (xs, mk srt2 op) %% []
  | _, _ -> raise (Invalid_argument "in mk_ty1")


let rec expr scx oe =
  let oe, srt = nopats_expr scx oe in
  let oe = map_patterns oe (List.map (fun e -> expr scx e |> fst)) in
  (oe, srt)

and nopats_expr scx oe =
  match oe.core with
  | Ix n ->
      let srt = lookup_srt scx n in
      (Ix n @@ oe, srt)

  | Opaque s ->
      (* This case is for primed variables *)
      (Opaque s @@ oe, Idv)

  | Internal _ ->
      let op, Ty2 (ty1s, srt) = eopr scx oe in
      begin match ty1s with
      | [] -> ()
      | _ -> error ~at:oe "Unexpected non-constant builtin"
      end;
      (op $$ oe, srt)

  | String s ->
      if !opt_ccast then
        let oe = String s @@ oe in
        (assign oe Props.icast_prop (TAtm TAStr), Idv)
      else
        (String s @@ oe, Idv)

  | Num (s1, s2) ->
      if !opt_ccast then
        let oe = Num (s1, s2) @@ oe in
        (assign oe Props.icast_prop (TAtm TAIdv), Idv)
      else
        (Num (s1, s2) @@ oe, Idv)

  | Apply ({ core = Internal (B.Eq | B.Neq) } as op, [ e ; f ]) ->
      let e, srt1 = expr scx e in
      let f, srt2 = expr scx f in
      if !opt_bunify && srt1 = Bool && srt2 = Bool then
        let op = assign op Props.tpars_prop [ TAtm TABol ] in
        (Apply (op, [ e ; f ]) @@ oe, Bool)
      else
        let op = assign op Props.tpars_prop [ TAtm TAIdv ] in
        (Apply (op, [ mk_idv srt1 e ; mk_idv srt2 f ]) @@ oe, Bool)

  | Apply (op, []) ->
      let op, srt = expr scx op in
      (op $$ oe, srt)

  | Apply (op, es) ->
      let op, Ty2 (ty11s, srt) = eopr scx op in
      let es =
        List.fold_left begin fun r_es (e, ty11) ->
          let e, ty12 = earg scx e in
          (mk_ty1 ty11 ty12 e :: r_es)
        end [] (List.combine es ty11s)
        |> fun r_es ->
            List.rev r_es
      in
      (Apply (op, es) @@ oe, srt)

  | If (e, f, g) ->
      let e, srt1 = expr scx e in
      let f, srt2 = expr scx f in
      let g, srt3 = expr scx g in
      if !opt_bunify && srt2 = Bool && srt3 = Bool then
        let oe = If (mk_bool srt1 e, f, g) @@ oe in
        (assign oe Props.tpars_prop [ TAtm TABol ], Bool)
      else
        let oe = If (mk_bool srt1 e, mk_idv srt2 f, mk_idv srt3 g) @@ oe in
        (assign oe Props.tpars_prop [ TAtm TAIdv ], Idv)

  | Case (ps, Some o) ->
      let ps, srts =
        List.map begin fun (p, e) ->
          let p, srt1 = expr scx p in
          let e, srt2 = expr scx e in
          ((mk_bool srt1 p, e), srt2)
        end ps
        |> List.split
      in
      let o, srt = expr scx o in
      if !opt_bunify && List.for_all ((=) srt) srts then
        let oe = Case (ps, Some o) @@ oe in
        (assign oe Props.tpars_prop [ TAtm TABol ], Bool)
      else
        let ps =
          List.map2 begin fun (p, e) srt ->
            (p, mk_idv srt e)
          end ps srts
        in
        let oe = Case (ps, Some (mk_idv srt o)) @@ oe in
        (assign oe Props.tpars_prop [ TAtm TAIdv ], Idv)

  | Case (ps, None) ->
      let ps =
        List.map begin fun (p, e) ->
          let p, srt1 = expr scx p in
          let e, srt2 = expr scx e in
          (mk_bool srt1 p, mk_idv srt2 e)
        end ps
      in
      let oe = Case (ps, None) @@ oe in
      (assign oe Props.tpars_prop [ TAtm TAIdv ], Idv)

  | List (bl, es) ->
      let es =
        List.map begin fun e ->
          let e, srt = expr scx e in
          mk_bool srt e
        end es
      in
      (List (bl, es) @@ oe, Bool)

  | Let (dfs, e) ->
      let scx, dfs = defns scx dfs in
      let e, srt = expr scx e in
      (Let (dfs, e) @@ oe, srt)

  | Sequent sq ->
      let _, sq = sequent scx sq in
      (Sequent sq @@ oe, Bool)

  | Quant (q, bs, e) ->
      let scx, bs = bounds scx bs in
      let e, srt = expr scx e in
      (Quant (q, bs, mk_bool srt e) @@ oe, Bool)

  | Tquant (q, vs, e) ->
      let scx, vs =
        List.fold_left begin fun (scx, r_vs) v ->
          let v, scx = adj_srt scx v Idv in
          (scx, v :: r_vs)
        end (scx, []) vs
        |> fun (scx, r_vs) ->
            (scx, List.rev r_vs)
      in
      let e, srt = expr scx e in
      (Tquant (q, vs, mk_bool srt e) @@ oe, Bool)

  | Choose (v, b, e) ->
      let b =
        Option.map begin fun e ->
          let e, srt = expr scx e in
          mk_idv srt e
        end b
      in
      let v, scx = adj_srt scx v Idv in
      let e, srt = expr scx e in
      (Choose (v, b, mk_bool srt e) @@ oe, Idv)

  | SetSt (v, b, e) ->
      let b, srt1 = expr scx b in
      let v, scx = adj_srt scx v Idv in
      let e, srt2 = expr scx e in
      (SetSt (v, mk_idv srt1 b, mk_bool srt2 e) @@ oe, Idv)

  | SetOf (e, bs) ->
      let scx, bs = bounds scx bs in
      let e, srt = expr scx e in
      (SetOf (mk_idv srt e, bs) @@ oe, Idv)

  | SetEnum es ->
      let es =
        List.map begin fun e ->
          let e, srt = expr scx e in
          mk_idv srt e
        end es
      in
      (SetEnum es @@ oe, Idv)

  | Product es ->
      let es =
        List.map begin fun e ->
          let e, srt = expr scx e in
          mk_idv srt e
        end es
      in
      (Product es @@ oe, Idv)

  | Tuple es ->
      let es =
        List.map begin fun e ->
          let e, srt = expr scx e in
          mk_idv srt e
        end es
      in
      (Tuple es @@ oe, Idv)

  | Fcn (bs, e) ->
      let scx, bs = bounds scx bs in
      let e, srt = expr scx e in
      (Fcn (bs, mk_idv srt e) @@ oe, Idv)

  | FcnApp (e, es) ->
      let e, srt = expr scx e in
      let es =
        List.map begin fun e ->
          let e, srt = expr scx e in
          mk_idv srt e
        end es
      in
      (FcnApp (mk_idv srt e, es) @@ oe, Idv)

  | Arrow (e, f) ->
      let e, srt1 = expr scx e in
      let f, srt2 = expr scx f in
      (Arrow (mk_idv srt1 e, mk_idv srt2 f) @@ oe, Idv)

  | Rect fs ->
      let fs =
        List.map begin fun (f, e) ->
          let e, srt = expr scx e in
          (f, mk_idv srt e)
        end fs
      in
      (Rect fs @@ oe, Idv)

  | Record fs ->
      let fs =
        List.map begin fun (f, e) ->
          let e, srt = expr scx e in
          (f, mk_idv srt e)
        end fs
      in
      (Record fs @@ oe, Idv)

  | Except (e, exs) ->
      let e, srt = expr scx e in
      let exs =
        List.map begin fun (exps, e) ->
          let exps =
            List.map begin function
              | Except_dot s -> Except_dot s
              | Except_apply e ->
                  let e, srt = expr scx e in
                  Except_apply (mk_idv srt e)
            end exps
          in
          let e, srt = expr scx e in
          (exps, mk_idv srt e)
        end exs
      in
      (Except (e, exs) @@ oe, Idv)

  | Dot (e, f) ->
      let e, srt = expr scx e in
      (Dot (mk_idv srt e, f) @@ oe, Idv)

  | With (e, m) ->
      let e, srt = expr scx e in
      (With (e, m) @@ oe, srt)

  | Parens (e, pf) ->
      let e, srt = expr scx e in
      (Parens (e, pf) @@ oe, srt)

  | Lambda _ ->
      error ~at:oe "Unexpected LAMBDA in expr"

  | Bang _ ->
      error ~at:oe "Unsupported constructor Bang"
  | Sub _ ->
      error ~at:oe "Unsupported constructor Sub"
  | Tsub _ ->
      error ~at:oe "Unsupported constructor Tsub"
  | Fair _ ->
      error ~at:oe "Unsupported constructor Fair"
  | At _ ->
      error ~at:oe "Unsupported constructor At"

and earg scx oa =
  match oa.core with
  | Ix n ->
      let (Ty1 (srts, srt) as ty1) = lookup_ty1 scx n in
      if !opt_tpred || srt = Idv then
        (Ix n @@ oa, ty1)
      else
        let xs =
          List.mapi begin fun i srt ->
            let v = ("x" ^ string_of_int i) %% [] in
            let v = assign v Props.ty0_prop (to_ty0 srt) in
            (v, Shape_expr)
          end srts
        in
        let m = List.length srts in
        let e =
          Apply (
            Ix (m + n) @@ oa,
            List.init m (fun i -> Ix (m - i) %% [])
          ) %% []
        in
        (Lambda (xs, mk_idv srt e) %% [], Ty1 (srts, Idv))

  | Lambda (xs, e) ->
      let scx, xs, srts =
        List.fold_left begin fun (scx, r_xs, r_srts) (v, shp) ->
          let srt =
            match shp with
            | Shape_expr -> Idv
            | Shape_op _ -> error ~at:v "Expected constant argument"
          in
          let v, scx = adj_srt scx v srt in
          let x = (v, shp) in
          (scx, x :: r_xs, srt :: r_srts)
        end (scx, [], []) xs
        |> fun (scx, r_xs, r_srts) ->
            (scx, List.rev r_xs, List.rev r_srts)
      in
      let e, srt = expr scx e in
      if !opt_tpred then
        let ty1 = Ty1 (srts, srt) in
        (Lambda (xs, e) @@ oa, ty1)
      else
        let ty1 = Ty1 (srts, Idv) in
        (Lambda (xs, mk_idv srt e) @@ oa, ty1)

  | _ ->
      (* The argument to application can be a constant expression *)
      let e, srt = expr scx oa in
      (e $$ oa, Ty1 ([], srt))

and eopr scx op =
  match op.core with
  | Ix n ->
      let ty2 = lookup_ty2 scx n in
      (Ix n @@ op, ty2)

  | Internal (B.STRING | B.BOOLEAN | B.Nat | B.Int | B.Real | B.Infinity as b)
    when !opt_ccast ->
      (* Optionally cast non-boolean constants to Idv to prevent
       * type inconsistencies.  Eg: 'Nat' may be view as of
       * type 'Idv' or 'set(int)'. *)
      (mk_idv Bool (Internal b @@ op), Ty2 ([], Idv))

  | Internal b ->
      (* NOTE All builtins have a first-order type;
       * that simplifies the presentation. *)
      let srts, srt =
        match b with
        | B.TRUE      -> [],              Bool
        | B.FALSE     -> [],              Bool
        | B.Implies   -> [ Bool ; Bool ], Bool
        | B.Equiv     -> [ Bool ; Bool ], Bool
        | B.Conj      -> [ Bool ; Bool ], Bool
        | B.Disj      -> [ Bool ; Bool ], Bool
        | B.Neg       -> [ Bool ],        Bool
        (* Eq and Neq treated in expr *)

        | B.STRING    -> [],              Idv
        | B.BOOLEAN   -> [],              Idv
        | B.SUBSET    -> [ Idv ],         Idv
        | B.UNION     -> [ Idv ],         Idv
        | B.DOMAIN    -> [ Idv ],         Idv
        | B.Subseteq  -> [ Idv ; Idv ],   Bool
        | B.Mem       -> [ Idv ; Idv ],   Bool
        | B.Notmem    -> [ Idv ; Idv ],   Bool
        | B.Setminus  -> [ Idv ; Idv ],   Idv
        | B.Cap       -> [ Idv ; Idv ],   Idv
        | B.Cup       -> [ Idv ; Idv ],   Idv

        | B.Nat       -> [],              Idv
        | B.Int       -> [],              Idv
        | B.Real      -> [],              Idv
        | B.Plus      -> [ Idv ; Idv ],   Idv
        | B.Minus     -> [ Idv ; Idv ],   Idv
        | B.Uminus    -> [ Idv ],         Idv
        | B.Times     -> [ Idv ; Idv ],   Idv
        | B.Ratio     -> [ Idv ; Idv ],   Idv
        | B.Quotient  -> [ Idv ; Idv ],   Idv
        | B.Remainder -> [ Idv ; Idv ],   Idv
        | B.Exp       -> [ Idv ; Idv ],   Idv
        | B.Infinity  -> [],              Idv
        | B.Lteq      -> [ Idv ; Idv ],   Bool
        | B.Lt        -> [ Idv ; Idv ],   Bool
        | B.Gteq      -> [ Idv ; Idv ],   Bool
        | B.Gt        -> [ Idv ; Idv ],   Bool
        | B.Divides   -> [ Idv ; Idv ],   Idv
        | B.Range     -> [ Idv ; Idv ],   Idv

        | _ -> error ~at:op "Unupported or unexpected builtin"
      in
      let ty2 = Ty2 (List.map (fun srt -> Ty1 ([], srt)) srts, srt) in
      (Internal b @@ op, ty2)

  | _ -> error ~at:op "Unexpected operator"

(* No decoration added; the context must be updated by [bounds] *)
and bound scx (v, k, dom) =
  let dom =
    match dom with
    | No_domain -> No_domain
    | Domain e ->
        let e, srt = expr scx e in
        Domain (mk_idv srt e)
    | Ditto -> Ditto
  in
  (v, k, dom)

and bounds scx bs =
  let scx, bs =
    List.fold_left begin fun (scx', r_bs) b ->
      let (v, k, dom) = bound scx b in
      let v, scx' = adj_srt scx' v Idv in
      (scx', (v, k, dom) :: r_bs)
    end (scx, []) bs
    |> fun (scx, r_bs) ->
        (scx, List.rev r_bs)
  in
  (scx, bs)

(* Called on hidden defns; just give a generic
 * type to the new ident *)
and hdefn scx df =
  match df.core with
  | Recursive (v, shp) ->
      let ty1 = shp_to_ty1 shp in
      let v, scx = adj_ty1 scx v ty1 in
      (scx, Recursive (v, shp) @@ df)

  | Operator (v, ({ core = Lambda (xs, e) } as oe)) ->
      let xs, ty1s =
        List.map begin fun (v, shp) ->
          let ty1 = shp_to_ty1 shp in
          let v, _ = adj_ty1 scx v ty1 in (* ctx doesn't matter *)
          (v, shp), ty1
        end xs
        |> List.split
      in
      let ty2 = Ty2 (ty1s, Idv) in
      let v, scx = adj_ty2 scx v ty2 in
      (scx, Operator (v, (Lambda (xs, e) @@ oe)) @@ df)

  | Operator (v, e) ->
      let srt = Idv in
      let v, scx = adj_srt scx v srt in
      (scx, Operator (v, e) @@ df)

  | Instance _ ->
      error ~at:df "Unsupported constructor Instance"

  | Bpragma _ ->
      error ~at:df "Unsupported constructor Bpragma"

and defn scx df =
  match df.core with
  | Recursive (v, shp) ->
      let ty1 = shp_to_ty1 shp in
      let v, scx = adj_ty1 scx v ty1 in
      (scx, Recursive (v, shp) @@ df)

  | Operator (v, ({ core = Lambda (xs, e) } as oe)) ->
      let scx', xs, ty1s =
        List.fold_left begin fun (scx', r_xs, r_ty1s) (v, shp) ->
          let ty1 = shp_to_ty1 shp in
          let v, scx' = adj_ty1 scx' v ty1 in
          let x = (v, shp) in
          (scx', x :: r_xs, ty1 :: r_ty1s)
        end (scx, [], []) xs
        |> fun (scx', r_xs, r_ty1s) ->
            (scx', List.rev r_xs, List.rev r_ty1s)
      in
      let e, srt = expr scx' e in
      let e, ty2 =
        if !opt_tpred then
          (e, Ty2 (ty1s, srt))
        else
          (mk_idv srt e, Ty2 (ty1s, Idv))
      in
      let v, scx = adj_ty2 scx v ty2 in
      (scx, Operator (v, (Lambda (xs, e) @@ oe)) @@ df)

  | Operator (v, e) ->
      let e, srt = expr scx e in
      let e, srt =
        if !opt_tpred then
          (e, srt)
        else
          (mk_idv srt e, Idv)
      in
      let v, scx = adj_srt scx v srt in
      (scx, Operator (v, e) @@ df)

  | Instance _ ->
      error ~at:df "Unsupported constructor Instance"

  | Bpragma _ ->
      error ~at:df "Unsupported constructor Bpragma"

and defns scx dfs =
  match dfs with
  | [] -> (scx, [])
  | df :: dfs ->
      let scx, df = defn scx df in
      let scx, dfs = defns scx dfs in
      (scx, df :: dfs)

and hyp scx h =
  match h.core with
  | Fresh (v, Shape_expr, k, Bounded (e, vis))
    when vis = Visible || !opt_hidden ->
      let e, srt = expr scx e in
      let v, scx = adj_srt scx v Idv in
      (scx, Fresh (v, Shape_expr, k, Bounded (mk_idv srt e, vis)) @@ h)

  | Fresh (v, Shape_expr, k, Bounded (e, vis)) ->
      let v, scx = adj_srt scx v Idv in
      (scx, Fresh (v, Shape_expr, k, Bounded (e, vis)) @@ h)

  | Fresh (v, shp, k, Unbounded) ->
      let ty1 = shp_to_ty1 shp in
      let v, scx = adj_ty1 scx v ty1 in
      (scx, Fresh (v, shp, k, Unbounded) @@ h)

  | Fresh (_, Shape_op n, _, Bounded _) ->
      error ~at:h "Fresh operator cannot be bounded"

  | Flex v ->
      let v, scx = adj_srt scx v Idv in
      (scx, Flex v @@ h)

  | Defn (df, wd, vis, ex) when vis = Visible || !opt_hidden ->
      let scx, df = defn scx df in
      (scx, Defn (df, wd, vis, ex) @@ h)

  | Defn (df, wd, vis, ex) ->
      let scx, df = hdefn scx df in
      (scx, Defn (df, wd, vis, ex) @@ h)

  | Fact (e, vis, tm) when vis = Visible || !opt_hidden ->
      let e, srt = expr scx e in
      let scx = bump scx in
      (scx, Fact (mk_bool srt e, vis, tm) @@ h)

  | Fact (e, vis, tm) ->
      let scx = bump scx in
      (scx, Fact (e, vis, tm) @@ h)

and hyps scx hs =
  match Deque.front hs with
  | None -> (scx, Deque.empty)
  | Some (h, hs) ->
      let scx, h = hyp scx h in
      let scx, hs = hyps scx hs in
      (scx, Deque.cons h hs)

and sequent scx sq =
  let scx, hs = hyps scx sq.context in
  let e, srt = expr scx sq.active in
  (scx, { context = hs ; active = mk_bool srt e })


let main ?(hidden=false) ?(bunify=true) ?(ccast=true) ?(tpred=false) sq =
  opt_hidden := hidden;
  opt_bunify := bunify;
  opt_ccast  := ccast;
  opt_tpred  := tpred;
  snd (sequent init sq)

