(*
 * type/recon.ml --- decorate TLA+ expressions with types
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

open Expr.T
open Util
open Property
open Ext

open T_t

module B = Builtin

let error ?at mssg =
  let mssg = "Type.Reconstruct: " ^ mssg in
  Errors.bug ?at mssg


(* {3 Context} *)

type tty = TTy0 of ty0 | TTy1 of ty1 | TTy2 of ty2
type scx = tty Ctx.t

let init = Ctx.dot

let adj_ty0 scx v ty0 =
  let scx = Ctx.adj scx v.core (TTy0 ty0) in
  let v = assign v Props.ty0_prop ty0 in
  (v, scx)

let adj_ty1 scx v ty1 =
  let scx = Ctx.adj scx v.core (TTy1 ty1) in
  let v = assign v Props.ty1_prop ty1 in
  (v, scx)

let adj_ty2 scx v ty2 =
  let scx = Ctx.adj scx v.core (TTy2 ty2) in
  let v = assign v Props.ty2_prop ty2 in
  (v, scx)

let bump scx = Ctx.bump scx

let lookup_tty scx n =
  let idt, otty = Ctx.index scx n in
  match otty with
  | None ->
      let mssg = "Missing annotation on ident \
                  '" ^ Ctx.string_of_ident idt ^ "'"
      in
      error mssg
  | Some tty -> tty

let lookup_ty0 scx n =
  match lookup_tty scx n with
  | TTy0 ty0 -> ty0
  | TTy1 ty1 -> downcast_ty0 ty1
  | TTy2 ty2 -> downcast_ty0 (downcast_ty1 ty2)

let lookup_ty1 scx n =
  match lookup_tty scx n with
  | TTy0 ty0 -> upcast_ty1 ty0
  | TTy1 ty1 -> ty1
  | TTy2 ty2 -> downcast_ty1 ty2

let lookup_ty2 scx n =
  match lookup_tty scx n with
  | TTy0 ty0 -> upcast_ty2 (upcast_ty1 ty0)
  | TTy1 ty1 -> upcast_ty2 ty1
  | TTy2 ty2 -> ty2


(* {3 Helpers} *)

let force_idv ty0 e =
  match ty0 with
  | TAtm TAIdv -> e
  | _ -> assign e Props.icast_prop ty0

let force_bool ty0 e =
  match ty0 with
  | TAtm TABol -> e
  | _ -> assign e Props.bproj_prop ty0

let shp_to_ty1 = function
  | Shape_expr -> Ty1 ([], TAtm TAIdv)
  | Shape_op n -> Ty1 (List.init n (fun _ -> TAtm TAIdv), TAtm TAIdv)

let map3 f l1 l2 l3 =
  List.map2 f l1 l2 |>
  List.map2 (|>) l3

let rec fold_left3 f a l1 l2 l3 =
  match l1, l2, l3 with
  | [], [], [] -> a
  | b :: l1, c :: l2, d :: l3 ->
      fold_left3 f (f a b c d) l1 l2 l3
  | _, _, _ ->
      failwith "fold_left3"

let is_prime s =
  let rgx = Str.regexp "#prime$" in
  Str.string_match rgx s 0

let remove_prime s =
  let rgx = Str.regexp "#prime$" in
  Str.replace_first rgx "" s


(* {3 Main} *)

let rec expr scx oe =
  let oe, ty0 = expr_aux scx oe in
  let oe = map_patterns oe (List.map (fun e -> expr scx e |> fst)) in
  (oe, ty0)

and expr_aux scx oe =
  match oe.core with
  | Ix n ->
      let ty0 = lookup_ty0 scx n in
      (Ix n @@ oe, ty0)

  | Opaque s when is_prime s ->
      let s = remove_prime s in
      let ty0 =
        match Ctx.find scx s with
        | Some (TTy0 ty0) -> ty0
        | _ -> (* fail *) TAtm TAIdv
      in
      (Opaque s @@ oe, ty0)

  | Opaque s ->
      (Opaque s @@ oe, TAtm TAIdv)

  | Internal (B.TRUE | B.FALSE as b) ->
      (Internal b @@ oe, TAtm TABol)

  | Apply ({ core = Internal (B.Implies | B.Equiv | B.Conj | B.Disj) } as op, [ e ; f ]) ->
      let e, ty01 = expr scx e in
      let f, ty02 = expr scx f in
      let ret = Apply (op, [ force_bool ty01 e ; force_bool ty02 f ]) @@ oe in
      (ret, TAtm TABol)

  | Apply ({ core = Internal B.Neg } as op, [ e ]) ->
      let e, ty0 = expr scx e in
      let ret = Apply (op, [ force_bool ty0 e ]) @@ oe in
      (ret, TAtm TABol)

  | Apply ({ core = Internal (B.Eq | B.Neq) } as op, [ e ; f ]) ->
      let e, ty01 = expr scx e in
      let f, ty02 = expr scx f in
      if ty01 = ty02 then
        let op = assign op Props.tpars_prop [ ty01 ] in
        let ret = Apply (op, [ e ; f ]) @@ oe in
        (ret, TAtm TABol)
      else
        let op = assign op Props.tpars_prop [ TAtm TAIdv ] in
        let ret = Apply (op, [ force_idv ty01 e ; force_idv ty02 f ]) @@ oe in
        (ret, TAtm TABol)

  | List (Refs, [ e ]) ->
      let e, ty0 = expr scx e in
      let ret = List (Refs, [ e ]) @@ oe in
      (ret, ty0)

  | List (bl, es) ->
      let es, ty0s = List.map (expr scx) es |> List.split in
      let ret = List (bl, List.map2 force_bool ty0s es) @@ oe in
      (ret, TAtm TABol)

  | If (e, f, g) ->
      let e, ty01 = expr scx e in
      let f, ty02 = expr scx f in
      let g, ty03 = expr scx g in
      if ty02 = ty03 then
        let ret = If (force_bool ty01 e, f, g) @@ oe in
        (assign ret Props.tpars_prop [ ty02 ], ty02)
      else
        let ret = If (force_bool ty01 e, force_idv ty02 f, force_idv ty03 g) @@ oe in
        (assign ret Props.tpars_prop [ TAtm TAIdv ], TAtm TAIdv)

  | Case (ps, Some o) ->
      let ps, ty01s =
        List.map begin fun (p, e) ->
          let p, ty01 = expr scx p in
          let e, ty02 = expr scx e in
          ((force_bool ty01 p, e), ty02)
        end ps |>
        List.split
      in
      let o, ty02 = expr scx o in
      if List.for_all ((=) ty02) ty01s then
        let ret = Case (ps, Some o) @@ oe in
        (assign ret Props.tpars_prop [ ty02 ], ty02)
      else
        let ps =
          List.map2 begin fun (p, e) ty0 ->
            (p, force_idv ty0 e)
          end ps ty01s
        in
        let o = force_idv ty02 o in
        let ret = Case (ps, Some o) @@ oe in
        (assign ret Props.tpars_prop [ TAtm TAIdv ], TAtm TAIdv)

  | Case (ps, None) ->
      let ps =
        List.map begin fun (p, e) ->
          let p, ty01 = expr scx p in
          let e, ty02 = expr scx e in
          (force_bool ty01 p, force_idv ty02 e)
        end ps
      in
      let ret = Case (ps, None) @@ oe in
      (assign ret Props.tpars_prop [ TAtm TAIdv ], TAtm TAIdv)

  | Quant (q, bs, e) ->
      let scx, bs, _ =
        List.fold_left begin fun (scx', r_bs, last_ty0) (v, k, dom) ->
          match dom, last_ty0 with
          | Domain e, _ ->
              let e, ty01 = expr scx e in (* eval in top context *)
              begin match ty01 with
              | TSet ty02 when !Params.enc_typelvl <> 0 ->
                  let v, scx' = adj_ty0 scx' v ty02 in
                  let dom = Domain (assign e Props.tpars_prop [ ty02 ]) in
                  (scx', (v, k, dom) :: r_bs, Some ty02)
              | _ ->
                  let v, scx' = adj_ty0 scx' v (TAtm TAIdv) in
                  let dom = Domain (force_idv ty01 e) in
                  (scx', (v, k, dom) :: r_bs, None)
              end
          | Ditto, Some ty0 ->
              let v, scx' = adj_ty0 scx' v ty0 in
              (scx', (v, k, Ditto) :: r_bs, Some ty0)
          | Ditto, None
          | No_domain, _ ->
              let v, scx' = adj_ty0 scx' v (TAtm TAIdv) in
              (scx', (v, k, dom) :: r_bs, None)
        end (scx, [], None) bs |>
        fun (scx, r_bs, last_ty0) -> (scx, List.rev r_bs, last_ty0)
      in
      let e, ty0 = expr scx e in
      (Quant (q, bs, force_bool ty0 e) @@ oe, TAtm TABol)

  | Sequent sq ->
      let _, sq = sequent scx sq in
      (Sequent sq @@ oe, TAtm TABol)

  | Let (dfs, e) ->
      let scx, dfs = defns scx dfs in
      let e, ty0 = expr scx e in
      (Let (dfs, e) @@ oe, ty0)

  | Choose (v, Some d, e) ->
      let d, ty01 = expr scx d in
      begin match ty01 with
      | TSet ty02 when !Params.enc_typelvl <> 0 ->
          let v, scx = adj_ty0 scx v ty02 in
          let e, ty03 = expr scx e in
          let ret = Choose (v, Some d, force_bool ty03 e) @@ oe in
          (assign ret Props.tpars_prop [ ty02 ], TAtm TAIdv)
      | _ ->
          let v, scx = adj_ty0 scx v (TAtm TAIdv) in
          let e, ty03 = expr scx e in
          let force = if !Params.enc_nobool then force_idv else force_bool in
          let ret = Choose (v, Some (force_idv ty01 d), force ty03 e) @@ oe in
          (ret, TAtm TAIdv)
      end

  | Choose (v, None, e) ->
      let v, scx = adj_ty0 scx v (TAtm TAIdv) in
      let e, ty0 = expr scx e in
      let force = if !Params.enc_nobool then force_idv else force_bool in
      let ret = Choose (v, None, force ty0 e) @@ oe in
      (ret, TAtm TAIdv)

  | Apply ({ core = Internal (B.Mem | B.Notmem) } as op, [ e ; f ]) ->
      let e, ty01 = expr scx e in
      let f, ty02 = expr scx f in
      begin match ty01, ty02 with
      | ty03, TSet ty04 when !Params.enc_typelvl <> 0 && ty03 = ty04->
          let op = assign op Props.tpars_prop [ ty03 ] in
          let ret = Apply (op, [ e ; f ]) @@ oe in
          (ret, TAtm TABol)
      | _, _ ->
          let ret = Apply (op, [ force_idv ty01 e ; force_idv ty02 f ]) @@ oe in
          let ty05 = if !Params.enc_nobool then TAtm TAIdv else TAtm TABol in
          (ret, ty05)
      end

  | Apply ({ core = Internal B.Subseteq } as op, [ e ; f ]) ->
      let e, ty01 = expr scx e in
      let f, ty02 = expr scx f in
      begin match ty01, ty02 with
      | TSet ty03, TSet ty04 when !Params.enc_typelvl <> 0 && ty03 = ty04 ->
          let op = assign op Props.tpars_prop [ ty03 ] in
          let ret = Apply (op, [ e ; f ]) @@ oe in
          (ret, TAtm TABol)
      | _, _ ->
          let ret = Apply (op, [ force_idv ty01 e ; force_idv ty02 f ]) @@ oe in
          let ty05 = if !Params.enc_nobool then TAtm TAIdv else TAtm TABol in
          (ret, ty05)
      end

  | SetEnum es ->
      let es, ty01s = List.map (expr scx) es |> List.split in
      let oty02 =
        match ty01s with
        | [] when !Params.enc_typelvl <> 0 ->
            (* NOTE {} : set(idv) *)
            Some (TAtm TAIdv)
        | ty03 :: ty04s when !Params.enc_typelvl <> 0 && List.for_all ((=) ty03) ty04s ->
            Some ty03
        | _ ->
            None
      in
      begin match oty02 with
      | Some ty03 ->
          let ret = SetEnum es @@ oe in
          (assign ret Props.tpars_prop [ ty03 ], TSet ty03)
      | None ->
          let ret = SetEnum es @@ oe in
          (ret, TAtm TAIdv)
      end

  | Apply ({ core = Internal B.UNION } as op, [ e ]) ->
      let e, ty01 = expr scx e in
      begin match ty01 with
      | TSet (TSet ty02) when !Params.enc_typelvl <> 0 ->
          let op = assign op Props.tpars_prop [ ty02 ] in
          let ret = Apply (op, [ e ]) @@ oe in
          (ret, TSet ty02)
      | _ ->
          let ret = Apply (op, [ force_idv ty01 e ]) @@ oe in
          (ret, TAtm TAIdv)
      end

  | Apply ({ core = Internal B.SUBSET } as op, [ e ]) ->
      let e, ty01 = expr scx e in
      begin match ty01 with
      | TSet ty02 when !Params.enc_typelvl <> 0 ->
          let op = assign op Props.tpars_prop [ ty02 ] in
          let ret = Apply (op, [ e ]) @@ oe in
          (ret, TSet (TSet ty02))
      | _ ->
          let ret = Apply (op, [ force_idv ty01 e ]) @@ oe in
          (ret, TAtm TAIdv)
      end

  | SetSt (v, e, f) ->
      let e, ty01 = expr scx e in
      begin match ty01 with
      | TSet ty02 when !Params.enc_typelvl <> 0 ->
          let v, scx = adj_ty0 scx v ty02 in
          let f, ty03 = expr scx f in
          let ret = SetSt (v, e, force_bool ty03 f) @@ oe in
          (assign ret Props.tpars_prop [ ty02 ], TSet ty02)
      | _ ->
          let v, scx = adj_ty0 scx v (TAtm TAIdv) in
          let f, ty03 = expr scx f in
          let force = if !Params.enc_nobool then force_idv else force_bool in
          let ret = SetSt (v, force_idv ty01 e, force ty03 f) @@ oe in
          (ret, TAtm TAIdv)
      end

  | SetOf (e, bs) ->
      (* Either all domains are sets and none is converted, or one is not a set
       * and all are converted. *)
      let doms, ty01s, _ =
        List.fold_left begin fun (r_doms, r_ty01s, last_ty0) (v, _, dom) ->
          match dom, last_ty0 with
          | Domain e, _ ->
              let e, ty0 = expr scx e in
              (Domain e :: r_doms, ty0 :: r_ty01s, Some ty0)
          | Ditto, Some ty0 ->
              (Ditto :: r_doms, ty0 :: r_ty01s, Some ty0)
          | No_domain, _
          | Ditto, None ->
              error ~at:v "Missing domain (constructor SetOf)"
        end ([], [], None) bs |>
        fun (r_doms, r_ty01s, last_ty0) -> (List.rev r_doms, List.rev r_ty01s, last_ty0)
      in
      let oty02s =
        if !Params.enc_typelvl <> 0 then try
          Some (List.map (function TSet ty0 -> ty0 | _ -> failwith "") ty01s)
        with _ -> None
        else None
      in
      begin match oty02s with
      | Some ty03s ->
          let scx, bs =
            fold_left3 begin fun (scx, r_bs) (v, k, _) dom ty03 ->
              let v, scx = adj_ty0 scx v ty03 in
              let dom =
                match dom with
                | Domain e -> Domain (assign e Props.tpars_prop [ ty03 ])
                | _ -> dom
              in
              (scx, (v, k, dom) :: r_bs)
            end (scx, []) bs doms ty03s |>
            fun (scx, r_bs) -> (scx, List.rev r_bs)
          in
          let e, ty04 = expr scx e in
          let ret = SetOf (e, bs) @@ oe in
          (assign ret Props.tpars_prop (ty04 :: ty03s), TSet ty04)
      | None ->
          let scx, bs =
            fold_left3 begin fun (scx, r_bs) (v, k, _) dom ty03 ->
              let v, scx = adj_ty0 scx v (TAtm TAIdv) in
              let dom =
                match dom with
                | Domain e -> Domain (force_idv ty03 e)
                | _ -> dom
              in
              (scx, (v, k, dom) :: r_bs)
            end (scx, []) bs doms ty01s |>
            fun (scx, r_bs) -> (scx, List.rev r_bs)
          in
          let e, ty04 = expr scx e in
          let ret = SetOf (force_idv ty04 e, bs) @@ oe in
          (ret, TAtm TAIdv)
      end

  | Apply ({ core = Internal (B.Cap | B.Cup | B.Setminus) } as op, [ e ; f ]) ->
      let e, ty01 = expr scx e in
      let f, ty02 = expr scx f in
      begin match ty01, ty02 with
      | TSet ty03, TSet ty04 when !Params.enc_typelvl <> 0 && ty03 = ty04 ->
          let op = assign op Props.tpars_prop [ ty03 ] in
          let ret = Apply (op, [ e ; f ]) @@ oe in
          (ret, TSet ty03)
      | _, _ ->
          let ret = Apply (op, [ force_idv ty01 e ; force_idv ty02 f ]) @@ oe in
          (ret, TAtm TAIdv)
      end

  | Internal B.BOOLEAN ->
      if !Params.enc_typelvl <> 0 then
        let ret = Internal B.BOOLEAN @@ oe in
        (assign ret Props.tpars_prop [ ], TSet (TAtm TABol))
      else
        let ret = Internal B.BOOLEAN @@ oe in
        (ret, TAtm TAIdv)

  | Internal B.STRING ->
      if !Params.enc_typelvl <> 0 then
        let ret = Internal B.STRING @@ oe in
        (assign ret Props.tpars_prop [ ], TSet (TAtm TAStr))
      else
        let ret = Internal B.STRING @@ oe in
        (ret, TAtm TAIdv)

  | String s ->
      if !Params.enc_typelvl <> 0 then
        let ret = String s @@ oe in
        (assign ret Props.tpars_prop [ ], TAtm TAStr)
      else
        let ret = String s @@ oe in
        (ret, TAtm TAIdv)

  | Fcn (bs, e) ->
      (* copypasted from SetOf case; same principle *)
      let doms, ty01s, _ =
        List.fold_left begin fun (r_doms, r_ty01s, last_ty0) (v, _, dom) ->
          match dom, last_ty0 with
          | Domain e, _ ->
              let e, ty0 = expr scx e in
              (Domain e :: r_doms, ty0 :: r_ty01s, Some ty0)
          | Ditto, Some ty0 ->
              (Ditto :: r_doms, ty0 :: r_ty01s, Some ty0)
          | No_domain, _
          | Ditto, None ->
              error ~at:v "Missing domain (constructor Fcn)"
        end ([], [], None) bs |>
        fun (r_doms, r_ty01s, last_ty0) -> (List.rev r_doms, List.rev r_ty01s, last_ty0)
      in
      let oty02s =
        if !Params.enc_typelvl <> 0 then try
          Some (List.map (function TSet ty0 -> ty0 | _ -> failwith "") ty01s)
        with _ -> None
        else None
      in
      begin match oty02s with
      | Some ty03s ->
          let scx, bs =
            fold_left3 begin fun (scx, r_bs) (v, k, _) dom ty03 ->
              let v, scx = adj_ty0 scx v ty03 in
              let dom =
                match dom with
                | Domain e -> Domain (assign e Props.tpars_prop [ ty03 ])
                | _ -> dom
              in
              (scx, (v, k, dom) :: r_bs)
            end (scx, []) bs doms ty03s |>
            fun (scx, r_bs) -> (scx, List.rev r_bs)
          in
          let e, ty04 = expr scx e in
          let ret = Fcn (bs, e) @@ oe in
          let ty0 =
            match ty03s with
            | [ ty05 ] -> TFun (ty05, ty04)
            | _ -> TFun (TPrd ty03s, ty04)
          in
          (assign ret Props.tpars_prop (ty03s @ [ ty04 ]), ty0)
      | None ->
          let scx, bs =
            fold_left3 begin fun (scx, r_bs) (v, k, _) dom ty03 ->
              let v, scx = adj_ty0 scx v (TAtm TAIdv) in
              let dom =
                match dom with
                | Domain e -> Domain (force_idv ty03 e)
                | _ -> dom
              in
              (scx, (v, k, dom) :: r_bs)
            end (scx, []) bs doms ty01s |>
            fun (scx, r_bs) -> (scx, List.rev r_bs)
          in
          let e, ty04 = expr scx e in
          let ret = Fcn (bs, force_idv ty04 e) @@ oe in
          (ret, TAtm TAIdv)
      end

  | Apply ({ core = Internal B.DOMAIN } as op, [ e ]) ->
      let e, ty01 = expr scx e in
      begin match ty01 with
      | TFun (ty02, ty03) when !Params.enc_typelvl <> 0 ->
          let op = assign op Props.tpars_prop [ ty02 ; ty03 ] in
          let ret = Apply (op, [ e ]) @@ oe in
          (ret, TSet ty02)
      | _ ->
          let ret = Apply (op, [ force_idv ty01 e ]) @@ oe in
          (ret, TAtm TAIdv)
      end

  | FcnApp (e, es) ->
      let e, ty01 = expr scx e in
      let es, ty02s = List.map (expr scx) es |> List.split in
      begin match ty01 with
      | TFun (TPrd ty03s, ty04) when !Params.enc_typelvl <> 0 && List.for_all2 (=) ty02s ty03s ->
          let ret = FcnApp (e, es) @@ oe in
          (assign ret Props.tpars_prop (ty03s @ [ ty04 ]), ty04)
      | TFun (ty03, ty04) when !Params.enc_typelvl <> 0 && List.length es = 1 && List.hd ty02s = ty03 ->
          let ret = FcnApp (e, es) @@ oe in
          (assign ret Props.tpars_prop [ ty03 ; ty04 ], ty04)
      | _ ->
          let ret = FcnApp (force_idv ty01 e, List.map2 force_idv ty02s es) @@ oe in
          (ret, TAtm TAIdv)
      end

  | Dot (e, s) ->
      let e, ty01 = expr scx e in
      begin match ty01 with
      | TFun (TAtm TAStr, ty02) when !Params.enc_typelvl <> 0 ->
          let ret = Dot (e, s) @@ oe in
          (assign ret Props.tpars_prop [ ty02 ], ty02)
      | _ ->
          let ret = Dot (force_idv ty01 e, s) @@ oe in
          (ret, TAtm TAIdv)
      end

  | Product es ->
      let es, ty01s = List.map (expr scx) es |> List.split in
      let oty02s =
        if !Params.enc_typelvl <> 0 then try
          Some (List.map (function TSet ty0 -> ty0 | _ -> failwith "") ty01s)
        with _ -> None
        else None
      in
      begin match oty02s with
      | Some ty02s ->
          let ret = Product es @@ oe in
          (assign ret Props.tpars_prop ty02s, TSet (TPrd ty02s))
      | None ->
          let ret = Product (List.map2 force_idv ty01s es) @@ oe in
          (ret, TAtm TAIdv)
      end

  | Tuple es ->
      let es, ty0s = List.map (expr scx) es |> List.split in
      if !Params.enc_typelvl <> 0 then
        let ret = Tuple es @@ oe in
        (assign ret Props.tpars_prop ty0s, TPrd ty0s)
      else
        let ret = Tuple (List.map2 force_idv ty0s es) @@ oe in
        (ret, TAtm TAIdv)

  | Arrow (e, f) ->
      let e, ty01 = expr scx e in
      let f, ty02 = expr scx f in
      begin match ty01, ty02 with
      | TSet ty03, TSet ty04 when !Params.enc_typelvl <> 0 ->
          let ret = Arrow (e, f) @@ oe in
          (assign ret Props.tpars_prop [ ty03 ; ty04 ], TSet (TFun (ty03, ty04)))
      | _, _ ->
          let ret = Arrow (force_idv ty01 e, force_idv ty02 f) @@ oe in
          (ret, TAtm TAIdv)
      end

  | Rect _ ->
      error ~at:oe "Not implemented: constructor Rect"
  | Record _ ->
      error ~at:oe "Not implemented: constructor Record"

  | Except (e, exps) ->
      let e, ty01 = expr scx e in
      let exps, exp_ty0s =
        List.map begin fun (expts, a) ->
          let expts, ty02s =
            List.map begin function
              | Except_dot s ->
                  (Except_dot s, TAtm TAStr)
              | Except_apply u ->
                  let u, ty02 = expr scx u in
                  (Except_apply u, ty02)
            end expts |>
            List.split
          in
          let a, ty03 = expr scx a in
          (expts, a), (ty02s, ty03)
        end exps |>
        List.split
      in
      let oty04s =
        if !Params.enc_typelvl <> 0 then begin
          (* In `[ f EXCEPT ![d1]..[dn] = a, .. ]` the function `f`
           * is expected to be a currified function, `d1` to have the
           * type of the first argument, `d2` the second etc.
           * The longest chain of expoints contains all the relevant types;
           * all other chains are verified in comparison with those types. *)
          let mk_fcn_ty ty0s ty0 =
            List.fold_right (fun ty01 ty02 -> TFun (ty01, ty02)) ty0s ty0
          in
          let ty04s, ty05 =
            List.fold_left begin fun (max, ty0s, ty0 as last) (ty02s, ty03) ->
              let n = List.length ty02s in
              if n > max then (n, ty02s, ty03) else last
            end (0, [], TAtm TAIdv) exp_ty0s |>
            fun (_, ty02s, ty03) ->
              (ty02s, ty03)
          in
          if ty01 <> mk_fcn_ty ty04s ty05 then None
          else
            let check_exp (ty02s, ty03) =
              let rec spin = function
                | [], ty04s ->
                    Some ty04s
                | ty02 :: ty02s, ty04 :: ty04s ->
                    if ty02 = ty04 then
                      spin (ty02s, ty04s)
                    else
                      None
                | _, [] ->
                    failwith ""
              in
              match spin (ty02s, ty04s) with
              | Some ty06s -> ty05 = mk_fcn_ty ty06s ty03
              | None -> false
            in
            if List.for_all check_exp exp_ty0s then
              Some (ty04s @ [ ty05 ])
            else None
        end else None
      in
      begin match oty04s with
      | Some ty04s ->
          let ret = Except (e, exps) @@ oe in
          (assign ret Props.tpars_prop ty04s, ty01)
      | None ->
          let e = force_idv ty01 e in
          let exps =
            List.map2 begin fun (expts, a) (ty02s, ty03) ->
              let expts =
                List.map2 begin fun expt ty02 ->
                  match expt with
                  | Except_dot s -> Except_dot s
                  | Except_apply u -> Except_apply (force_idv ty02 u)
                end expts ty02s
              in
              let a = force_idv ty03 a in
              (expts, a)
            end exps exp_ty0s
          in
          let ret = Except (e, exps) @@ oe in
          (ret, TAtm TAIdv)
      end

  | Internal B.Nat ->
      if !Params.enc_typelvl <> 0 && not !Params.enc_noarith then
        let ret = Internal B.Nat @@ oe in
        (assign ret Props.tpars_prop [ ], TSet (TAtm TAInt))
      else
        let ret = Internal B.Nat @@ oe in
        (ret, TAtm TAIdv)

  | Internal B.Int ->
      if !Params.enc_typelvl <> 0 && not !Params.enc_noarith then
        let ret = Internal B.Int @@ oe in
        (assign ret Props.tpars_prop [ ], TSet (TAtm TAInt))
      else
        let ret = Internal B.Int @@ oe in
        (ret, TAtm TAIdv)

  | Internal B.Real ->
      if !Params.enc_typelvl <> 0 && !Params.enc_noarith then
        let ret = Internal B.Real @@ oe in
        (assign ret Props.tpars_prop [ ], TSet (TAtm TARel))
      else
        let ret = Internal B.Real @@ oe in
        (ret, TAtm TAIdv)

  (* NOTE It suffices to put the 'noarith' guard on constants and variables.
   * All arithmetic operators will be interpreted as untyped because their
   * arguments will never be int or reat.
   * Variables will not be int as long as no expressions can be set(int). *)

  | Num (s, "") ->
      if not !Params.enc_noarith then
        let ret = Num (s, "") @@ oe in
        (assign ret Props.tpars_prop [ ], TAtm TAInt)
      else
        let ret = Num (s, "") @@ oe in
        (ret, TAtm TAIdv)

  | Num (s1, s2) ->
      if not !Params.enc_noarith then
        let ret = Num (s1, s2) @@ oe in
        (assign ret Props.tpars_prop [ ], TAtm TARel)
      else
        let ret = Num (s1, s2) @@ oe in
        (ret, TAtm TAIdv)

  | Internal B.Infinity ->
      if not !Params.enc_noarith then
        let ret = Internal B.Infinity @@ oe in
        (assign ret Props.tpars_prop [ ], TAtm TARel)
      else
        let ret = Internal B.Infinity @@ oe in
        (ret, TAtm TAIdv)

  | Apply ({ core = Internal (B.Plus | B.Minus | B.Times | B.Exp) } as op, [ e ; f ]) ->
      let e, ty01 = expr scx e in
      let f, ty02 = expr scx f in
      begin match ty01, ty02 with
      | TAtm TAInt, TAtm TAInt when !Params.enc_typelvl <> 0 ->
          let op = assign op Props.tpars_prop [ TAtm TAInt ] in
          let ret = Apply (op, [ e ; f ]) @@ oe in
          (ret, TAtm TAInt)
      | TAtm TARel, TAtm TARel when !Params.enc_typelvl <> 0 ->
          let op = assign op Props.tpars_prop [ TAtm TARel ] in
          let ret = Apply (op, [ e ; f ]) @@ oe in
          (ret, TAtm TARel)
      | _, _ ->
          let ret = Apply (op, [ force_idv ty01 e ; force_idv ty02 f ]) @@ oe in
          (ret, TAtm TAIdv)
      end

  | Apply ({ core = Internal B.Uminus } as op, [ e ]) ->
      let e, ty01 = expr scx e in
      begin match ty01 with
      | TAtm TAInt when !Params.enc_typelvl <> 0 ->
          let op = assign op Props.tpars_prop [ TAtm TAInt ] in
          let ret = Apply (op, [ e ]) @@ oe in
          (ret, TAtm TAInt)
      | TAtm TARel when !Params.enc_typelvl <> 0 ->
          let op = assign op Props.tpars_prop [ TAtm TARel ] in
          let ret = Apply (op, [ e ]) @@ oe in
          (ret, TAtm TARel)
      | _ ->
          let ret = Apply (op, [ force_idv ty01 e ]) @@ oe in
          (ret, TAtm TAIdv)
      end

  | Apply ({ core = Internal (B.Quotient | B.Remainder) } as op, [ e ; f ]) ->
      let e, ty01 = expr scx e in
      let f, ty02 = expr scx f in
      begin match ty01, ty02 with
      | TAtm TAInt, TAtm TAInt when !Params.enc_typelvl <> 0 ->
          let op = assign op Props.tpars_prop [ ] in
          let ret = Apply (op, [ e ; f ]) @@ oe in
          (ret, TAtm TAInt)
      | _, _ ->
          let ret = Apply (op, [ force_idv ty01 e ; force_idv ty02 f ]) @@ oe in
          (ret, TAtm TAIdv)
      end

  | Apply ({ core = Internal B.Range } as op, [ e ; f ]) ->
      let e, ty01 = expr scx e in
      let f, ty02 = expr scx f in
      begin match ty01, ty02 with
      | TAtm TAInt, TAtm TAInt when !Params.enc_typelvl <> 0 ->
          let op = assign op Props.tpars_prop [ ] in
          let ret = Apply (op, [ e ; f ]) @@ oe in
          (ret, TSet (TAtm TAInt))
      | _, _ ->
          let ret = Apply (op, [ force_idv ty01 e ; force_idv ty02 f ]) @@ oe in
          (ret, TAtm TAIdv)
      end

  | Apply ({ core = Internal (B.Lteq | B.Lt | B.Gteq | B.Gt) } as op, [ e ; f ]) ->
      let e, ty01 = expr scx e in
      let f, ty02 = expr scx f in
      begin match ty01, ty02 with
      | TAtm TAInt, TAtm TAInt when !Params.enc_typelvl <> 0 ->
          let op = assign op Props.tpars_prop [ ] in
          let ret = Apply (op, [ e ; f ]) @@ oe in
          (ret, TAtm TABol)
      | _, _ ->
          let ret = Apply (op, [ force_idv ty01 e ; force_idv ty02 f ]) @@ oe in
          let ty03 = if !Params.enc_nobool then TAtm TAIdv else TAtm TABol in
          (ret, ty03)
      end

  | Apply (op, es) ->
      (* no reconstruction in this case, only typechecking *)
      let op, Ty2 (ty11s, ty01) = eopr scx op in
      let es, ty12s = List.map (earg scx) es |> List.split in
      let es =
        map3 begin fun e ty11 ty12 ->
          if ty11 = ty12 then
            e
          else
            begin match ty11, ty12 with
            | Ty1 ([], TAtm TAIdv), Ty1 ([], ty02) ->
                force_idv ty02 e
            | Ty1 ([], TAtm TABol), Ty1 ([], ty02) ->
                force_bool ty02 e
            (* NOTE There may be more complex conversions I need to implement *)
            | _, _ ->
                error ~at:oe "Impossible operator conversion"
            end
        end es ty11s ty12s
      in
      (Apply (op, es) @@ oe, ty01)

  | With (e, m) ->
      let e, ty0 = expr scx e in
      (With (e, m) @@ oe, ty0)

  | Parens (e, pf) ->
      let e, ty0 = expr scx e in
      (Parens (e, pf) @@ oe, ty0)

  | Tquant (q, vs, e) ->
      let scx, vs =
        List.fold_left begin fun (scx, r_vs) v ->
          let v, scx = adj_ty0 scx v (TAtm TAIdv) in
          (scx, v :: r_vs)
        end (scx, []) vs |>
        fun (scx, r_vs) -> (scx, List.rev r_vs)
      in
      let e, ty0 = expr scx e in
      (Tquant (q, vs, force_bool ty0 e) @@ oe, TAtm TABol)

  | Sub (m, e, f) ->
      let e, ty0 = expr scx e in
      let f, _ = expr scx f in
      (Sub (m, force_bool ty0 e, f) @@ oe, TAtm TABol)

  | Tsub (m, e, f) ->
      let e, ty0 = expr scx e in
      let f, _ = expr scx f in
      (Tsub (m, force_bool ty0 e, f) @@ oe, TAtm TABol)

  | Fair (m, e, f) ->
      let e, ty0 = expr scx e in
      let f, _ = expr scx f in
      (Fair (m, force_bool ty0 e, f) @@ oe, TAtm TABol)

  | Lambda _ ->
      error ~at:oe "Unexpected Lambda constructor"
  | Bang _ ->
      error ~at:oe "Unexpected Bang constructor"
  | At _ ->
      error ~at:oe "Unexpected At constructor"

  | Internal _ ->
      error ~at:oe "Unexpected builtin"

and earg scx oa =
  match oa.core with
  | Ix n ->
      let ty1 = lookup_ty1 scx n in
      (Ix n @@ oa, ty1)

  | Lambda (xs, e) ->
      let scx, xs, ty0s =
        List.fold_left begin fun (scx, r_xs, r_ty0s) (v, shp) ->
          begin match shp with
          | Shape_expr -> ()
          | Shape_op _ -> error ~at:oa "Expected a first-order operator"
          end;
          let ty0 = TAtm TAIdv in
          let v, scx = adj_ty0 scx v ty0 in
          let x = (v, shp) in
          (scx, x :: r_xs, ty0 :: r_ty0s)
        end (scx, [], []) xs |>
        fun (scx, r_xs, r_ty0s) -> (scx, List.rev r_xs, List.rev r_ty0s)
      in
      let e, ty0 = expr scx e in
      let ty1 = Ty1 (ty0s, ty0) in
      (Lambda (xs, e) @@ oa, ty1)

  | _ ->
      let e, ty0 = expr scx oa in
      (e $$ oa, upcast_ty1 ty0)

and eopr scx op =
  match op.core with
  | Ix n ->
      let ty2 = lookup_ty2 scx n in
      (Ix n @@ op, ty2)

  | Lambda (xs, e) ->
      let scx, xs, ty1s =
        List.fold_left begin fun (scx, r_xs, r_ty1s) (v, shp) ->
          let ty1 = shp_to_ty1 shp in
          let v, scx = adj_ty1 scx v ty1 in
          let x = (v, shp) in
          (scx, x :: r_xs, ty1 :: r_ty1s)
        end (scx, [], []) xs |>
        fun (scx, r_xs, r_ty1s) -> (scx, List.rev r_xs, List.rev r_ty1s)
      in
      let e, ty0 = expr scx e in
      let ty2 = Ty2 (ty1s, ty0) in
      (Lambda (xs, e) @@ op, ty2)

  | Internal B.Prime ->
      error ~at:op "Unsupported builtin Prime"
  | Internal B.StrongPrime ->
      error ~at:op "Unsupported builtin StrongPrime"
  | Internal B.Leadsto ->
      error ~at:op "Unsupported builtin Leadsto"
  | Internal B.ENABLED ->
      error ~at:op "Unsupported builtin ENABLED"
  | Internal B.UNCHANGED ->
      error ~at:op "Unsupported builtin UNCHANGED"
  | Internal B.Cdot ->
      error ~at:op "Unsupported builtin Cdot"
  | Internal B.Actplus ->
      error ~at:op "Unsupported builtin Actplus"
  | Internal (B.Box _)->
      error ~at:op "Unsupported builtin Box"
  | Internal B.Diamond ->
      error ~at:op "Unsupported builtin Diamond"

  | Internal B.Divides ->
      error ~at:op "Unsupported builtin Divides"

  | Internal B.Seq ->
      error ~at:op "Unsupported builtin Seq"
  | Internal B.Len ->
      error ~at:op "Unsupported builtin Len"
  | Internal B.BSeq ->
      error ~at:op "Unsupported builtin BSeq"
  | Internal B.Cat ->
      error ~at:op "Unsupported builtin Cat"
  | Internal B.Append ->
      error ~at:op "Unsupported builtin Append"
  | Internal B.Head ->
      error ~at:op "Unsupported builtin Head"
  | Internal B.Tail ->
      error ~at:op "Unsupported builtin Tail"
  | Internal B.SubSeq ->
      error ~at:op "Unsupported builtin SubSeq"
  | Internal B.SelectSeq ->
      error ~at:op "Unsupported builtin SelectSeq"

  | Internal B.Unprimable ->
      error ~at:op "Unsupported builtin Unprimable"
  | Internal B.Irregular ->
      error ~at:op "Unsupported builtin Irregular"

  | _ ->
      error ~at:op "Unexpected left operand"

and defn ?(ignore=false) scx df =
  match df.core with
  | Recursive (v, shp) ->
      let ty1 = shp_to_ty1 shp in
      let v, scx = adj_ty1 scx v ty1 in
      (scx, Recursive (v, shp) @@ df)

  | Operator (v, ({ core = Lambda (xs, e) } as oe)) when ignore ->
      let xs, ty1s =
        List.map begin fun (v, shp) ->
          let ty1 = shp_to_ty1 shp in
          let v, _ = adj_ty1 scx v ty1 in (* ctx doesn't matter *)
          (v, shp), ty1
        end xs |>
        List.split
      in
      let ty2 = Ty2 (ty1s, TAtm TAIdv) in
      let v, scx = adj_ty2 scx v ty2 in
      (scx, Operator (v, (Lambda (xs, e) @@ oe)) @@ df)

  | Operator (v, e) when ignore ->
      let ty0 = TAtm TAIdv in
      let v, scx = adj_ty0 scx v ty0 in
      (scx, Operator (v, e) @@ df)

  | Operator (v, ({ core = Lambda (xs, e) } as oe)) (*when not ignore*) ->
      let scx', xs, ty1s =
        List.fold_left begin fun (scx', r_xs, r_ty1s) (v, shp) ->
          let ty1 = shp_to_ty1 shp in
          let v, scx' = adj_ty1 scx' v ty1 in
          let x = (v, shp) in
          (scx', x :: r_xs, ty1 :: r_ty1s)
        end (scx, [], []) xs |>
        fun (scx', r_xs, r_ty1s) -> (scx', List.rev r_xs, List.rev r_ty1s)
      in
      let e, ty0 = expr scx' e in
      let ty2 = Ty2 (ty1s, ty0) in
      let v, scx = adj_ty2 scx v ty2 in
      (scx, Operator (v, (Lambda (xs, e) @@ oe)) @@ df)

  | Operator (v, e) (*when not ignore*) ->
      let e, ty0 = expr scx e in
      let v, scx = adj_ty0 scx v ty0 in
      (scx, Operator (v, e) @@ df)

  | Instance _
  | Bpragma _ when ignore ->
      let scx = bump scx in
      (scx, df)

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
  | Fresh (v, Shape_expr, k, b) ->
      let b, oty0 =
        match b with
        | Bounded (e, Visible) ->
            let e, ty0 = expr scx e in
            begin match ty0 with
            | TSet ty01 when !Params.enc_typelvl <> 0 ->
                Bounded (assign e Props.tpars_prop [ ty01 ], Visible), Some ty0
            | _ ->
                Bounded (force_idv ty0 e, Visible), None
            end
        | _ -> b, None
      in
      let ty0 = Option.default (TAtm TAIdv) oty0 in
      let v, scx = adj_ty0 scx v ty0 in
      (scx, Fresh (v, Shape_expr, k, b) @@ h)

  | Fresh (v, shp, k, Unbounded) ->
      let ty1 = shp_to_ty1 shp in
      let v, scx = adj_ty1 scx v ty1 in
      (scx, Fresh (v, shp, k, Unbounded) @@ h)

  | Fresh (_, Shape_op n, _, Bounded _) ->
      error ~at:h "Fresh operator cannot be bounded"

  | Flex v ->
      let ty0 = TAtm TAIdv in
      let v, scx = adj_ty0 scx v ty0 in
      (scx, Flex v @@ h)

  | Defn (df, wd, vis, ex) ->
      let ignore = match vis with Hidden -> true | _ -> false in
      let scx, df = defn ~ignore scx df in
      (scx, Defn (df, wd, vis, ex) @@ h)

  | Fact (e, Visible, tm) ->
      let e, ty0 = expr scx e in
      let scx = bump scx in
      (scx, Fact (force_bool ty0 e, Visible, tm) @@ h)

  | Fact (e, Hidden, tm) ->
      let scx = bump scx in
      (scx, Fact (e, Hidden, tm) @@ h)


and hyps scx hs =
  match Deque.front hs with
  | None -> (scx, Deque.empty)
  | Some (h, hs) ->
      let scx, h = hyp scx h in
      let scx, hs = hyps scx hs in
      (scx, Deque.cons h hs)

and sequent scx sq =
  let scx, hs = hyps scx sq.context in
  let e, ty0 = expr scx sq.active in
  (scx, { context = hs ; active = force_bool ty0 e })


let main sq =
  snd (sequent init sq)

