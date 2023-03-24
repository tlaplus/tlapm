(*
 * type/synth.ml --- decorate TLA+ expressions with types
 *
 *
 * Copyright (C) 2022  INRIA and Microsoft Corporation
 *)

open Expr.T
open Util
open Property
open Ext

open T_t

module B = Builtin

let error ?at mssg =
  let mssg = "Type.Synthesize: " ^ mssg in
  (*Errors.bug ?at mssg*)
  failwith mssg


(* {3 Context} *)

type options =
  { typelvl : int
  }

type scx = options * hyp Deque.dq

let init = { typelvl = 0 }, Deque.empty

let typelvl (ops, _ : scx) = ops.typelvl

let adj_ty0 (ops, hx : scx) v ty0 =
  let v = assign v Props.ty0_prop ty0 in
  let h = Fresh (v, Shape_expr, Constant, Unbounded) %% [] in
  let hx = Deque.snoc hx h in
  (v, (ops, hx))

let adj_ty1 (ops, hx : scx) v ty1 =
  let v = assign v Props.ty1_prop ty1 in
  let h = Fresh (v, Shape_op 0, Constant, Unbounded) %% [] in
  let hx = Deque.snoc hx h in
  (v, (ops, hx))

let adj_ty2 (ops, hx : scx) v ty2 =
  let v = assign v Props.ty2_prop ty2 in
  let h = Fresh (v, Shape_op 0, Constant, Unbounded) %% [] in
  let hx = Deque.snoc hx h in
  (v, (ops, hx))

let bump (ops, hx : scx) =
  let h = Fact (Internal B.TRUE %% [], Hidden, NotSet) %% [] in
  let hx = Deque.snoc hx h in
  (ops, hx)

let lookup (_, hx : scx) n =
  let h = Option.get (Deque.nth ~backwards:true hx (n - 1)) in
  let v = hyp_hint h in
  v

let lookup_ty0 scx n =
  let v = lookup scx n in
  match query v Props.ty0_prop with
  | Some ty0 -> ty0
  | None -> begin
    match query v Props.ty1_prop with
    | Some ty1 -> downcast_ty0 ty1
    | None -> begin
      match query v Props.ty2_prop with
      | Some ty2 -> downcast_ty0 (downcast_ty1 ty2)
      | None -> error ~at:v ("Missing type (ord 0) on \
                              '" ^ v.core ^ "'")
    end
  end

let lookup_ty1 scx n =
  let v = lookup scx n in
  match query v Props.ty0_prop with
  | Some ty0 -> upcast_ty1 ty0
  | None -> begin
    match query v Props.ty1_prop with
    | Some ty1 -> ty1
    | None -> begin
      match query v Props.ty2_prop with
      | Some ty2 -> downcast_ty1 ty2
      | None -> error ~at:v ("Missing type (ord 1) on \
                              '" ^ v.core ^ "'")
    end
  end

let lookup_ty2 scx n =
  let v = lookup scx n in
  match query v Props.ty0_prop with
  | Some ty0 -> upcast_ty2 (upcast_ty1 ty0)
  | None -> begin
    match query v Props.ty1_prop with
    | Some ty1 -> upcast_ty2 ty1
    | None -> begin
      match query v Props.ty2_prop with
      | Some ty2 -> ty2
      | None -> error ~at:v ("Missing type (ord 2) on \
                              '" ^ v.core ^ "'")
    end
  end


(* {3 Helpers} *)

let force_idv ~typelvl ty0 e =
  if typelvl = 2 then
    match ty0, query e Props.sproj_prop with
    | TAtm TAIdv, _ -> e
    | TAtm (TAInt | TABol), Some ty0' when ty0 = ty0' ->
        remove e Props.sproj_prop
    | TAtm (TAInt | TABol), _ ->
        assign e Props.icast_prop ty0
    | _ -> e
  else
    match ty0, query e Props.sproj_prop with
    | TAtm TAIdv, _ -> e
    | _, Some ty0' when ty0 = ty0' ->
        remove e Props.sproj_prop
    | _ ->
        assign e Props.icast_prop ty0

let force_bool ty0 e =
  match ty0 with
  | TAtm TABol -> e
  | _ -> assign e Props.bproj_prop ty0

let force ~typelvl = function
  | TAtm TAIdv -> force_idv ~typelvl
  | TAtm TABol -> force_bool
  | _ -> failwith "Bad argument to force"

let idv_or_bol = function TAtm (TAIdv | TABol) -> true | _ -> false

let force_arg ~typelvl ty11 ty12 ea =
  match ty11, ty12 with
  | Ty1 ([], ty01), Ty1 ([], ty02)
    when idv_or_bol ty01 ->
      force ~typelvl ty01 ty02 ea
  | Ty1 (ty01s, ty02), Ty1 (ty03s, ty04)
    when List.length ty01s = List.length ty03s
      && List.for_all idv_or_bol ty03s && idv_or_bol ty02 ->
      let n = List.length ty01s in
      let vs =
        List.mapi begin fun i ty01 ->
          let v = ("x" ^ string_of_int (i + 1)) %% [] in
          (assign v Props.ty0_prop ty01, Shape_expr)
        end ty01s
      in
      let ea =
        Apply (
          Expr.Subst.app_expr (Expr.Subst.shift n) ea,
          List.mapi begin fun i (ty01, ty03) ->
            force ~typelvl ty03 ty01 (Ix (n - i) %% [])
          end (List.combine ty01s ty03s)
        ) %% [] |>
        Expr.Subst.app_expr (Expr.Subst.shift 0) (* force normalize *)
      in
      Lambda (vs, force ~typelvl ty02 ty04 ea) %% []
  | _ ->
      error ~at:ea "Impossible operator conversion"

(* Expressions for which a sort was infered but that cannot be encoded
 * into an expression of that sort (for some reason) need to be marked
 * as 'projected' into that sort. *)
let proj ~typelvl ty0 e =
  if typelvl = 2 then
    match ty0 with
    | TAtm (TAInt) ->
        assign e Props.sproj_prop ty0
    | _ -> e
  else
    assign e Props.sproj_prop ty0


let shp_to_ty1 = function
  | Shape_expr -> Ty1 ([], TAtm TAIdv)
  | Shape_op n -> Ty1 (List.init n (fun _ -> TAtm TAIdv), TAtm TAIdv)

let is_lambda = function
  | Lambda _ -> true
  | _ -> false

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


(* {3 Main} *)

let rec expr scx oe =
  let oe, ty0 = expr_aux scx oe in
  let oe = map_pats (List.map (fun e -> expr scx e |> fst)) oe in
  (oe, ty0)

and expr_aux scx oe =
  let force_idv ty x = force_idv ~typelvl:(typelvl scx) ty x in
  let force_arg ty x = force_arg ~typelvl:(typelvl scx) ty x in
  let proj ty x = proj ~typelvl:(typelvl scx) ty x in
  match oe.core with
  | Ix n ->
      let ty0 = lookup_ty0 scx n in
      (Ix n @@ oe, ty0)

  | Opaque s ->
      (Opaque s @@ oe, TAtm TAIdv)

  | Apply ({ core = Opaque s } as op, es) ->
      let es, ty0s = List.map (expr scx) es |> List.split in
      let es =
        List.map2 begin fun e ty0 ->
          force_idv ty0 e
        end es ty0s
      in
      (Apply (op, es) @@ oe, TAtm TAIdv)

  | Apply ({ core = Internal B.Unprimable } as op, [ e ]) ->
      let e, ty0 = expr scx e in
      let ret = Apply (op, [ e ]) @@ oe in
      (ret, ty0)

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
      if ty01 = ty02 && typelvl scx > 1 then
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
        let ret = assign ret Props.tpars_prop [ ty02 ] in
        (ret, ty02)
      else
        let ret = If (force_bool ty01 e, force_idv ty02 f, force_idv ty03 g) @@ oe in
        let ret = assign ret Props.tpars_prop [ TAtm TAIdv ] in
        (ret, TAtm TAIdv)

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
        let ret = assign ret Props.tpars_prop [ ty02 ] in
        (ret, ty02)
      else
        let ps =
          List.map2 begin fun (p, e) ty0 ->
            (p, force_idv ty0 e)
          end ps ty01s
        in
        let o = force_idv ty02 o in
        let ret = Case (ps, Some o) @@ oe in
        let ret = assign ret Props.tpars_prop [ TAtm TAIdv ] in
        (ret, TAtm TAIdv)

  | Case (ps, None) ->
      let ps =
        List.map begin fun (p, e) ->
          let p, ty01 = expr scx p in
          let e, ty02 = expr scx e in
          (force_bool ty01 p, force_idv ty02 e)
        end ps
      in
      let ret = Case (ps, None) @@ oe in
      let ret = assign ret Props.tpars_prop [ TAtm TAIdv ] in
      (ret, TAtm TAIdv)

  | Quant (q, bs, e) ->
      let scx, bs, _ =
        List.fold_left begin fun (scx', r_bs, last_ty0) (v, k, dom) ->
          match dom, last_ty0 with
          | Domain e, _ ->
              let e, ty01 = expr scx e in (* eval in top context *)
              begin match ty01 with
              | TSet ty02 when typelvl scx = 3 ->
                  let v, scx' = adj_ty0 scx' v ty02 in
                  let dom = Domain (assign e Props.mpars_prop ty02) in
                  (scx', (v, k, dom) :: r_bs, Some ty02)
              | TSet (TAtm _ as ty02) when typelvl scx = 2 ->
                  let v, scx' = adj_ty0 scx' v ty02 in
                  let dom = Domain (force_idv ty01 e) in
                  let v = force_idv ty02 v in
                  (scx', (v, k, dom) :: r_bs, Some ty02)
              | TSet ty02 when typelvl scx = 2 ->
                  let _, scx' = adj_ty0 scx' v ty02 in
                  let v = assign v Props.ty0_prop (TAtm TAIdv) in
                  let dom = Domain (force_idv ty01 e) in
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
          | No_domain, _ when typelvl scx = 2 ->
              let pol =
                match q with
                | Forall -> true
                | Exists -> false
              in
              let e' =
                let n = List.length r_bs + 1 in
                if n = List.length bs then e
                else
                  let bs' = snd (List.split_nth (List.length r_bs + 1) bs) in
                  Quant (q, bs', e) %% []
              in
              let inferer = fun hx e -> snd (expr (fst scx, hx) e) in
              begin match T_hyps.search_type_hyp ~inferer ~pol:pol (snd scx') e' with
              | Some (TAtm _ as ty02) ->
                  let v, scx' = adj_ty0 scx' v ty02 in
                  let v = force_idv ty02 v in
                  (scx', (v, k, dom) :: r_bs, Some ty02)
              | Some ty02 ->
                  let _, scx' = adj_ty0 scx' v ty02 in
                  let v = assign v Props.ty0_prop (TAtm TAIdv) in
                  (scx', (v, k, dom) :: r_bs, Some ty02)
              | None ->
                  let v, scx' = adj_ty0 scx' v (TAtm TAIdv) in
                  (scx', (v, k, dom) :: r_bs, None)
              end
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
      | TSet ty02 when typelvl scx = 3 ->
          let v, scx = adj_ty0 scx v ty02 in
          let e, ty03 = expr scx e in
          let ret = Choose (v, Some d, force_bool ty03 e) @@ oe in
          let ret = assign ret Props.mpars_prop ty02 in
          (ret, TAtm TAIdv)
      | TSet (TAtm _ as ty02) when typelvl scx = 2 ->
          let v, scx = adj_ty0 scx v ty02 in
          let e, ty03 = expr scx e in
          let v = force_idv ty02 v in
          let ret = Choose (v, Some d, force_bool ty03 e) @@ oe in
          (ret, TAtm TAIdv)
      | _ ->
          let v, scx = adj_ty0 scx v (TAtm TAIdv) in
          let e, ty03 = expr scx e in
          let ret = Choose (v, Some (force_idv ty01 d), force_bool ty03 e) @@ oe in
          (ret, TAtm TAIdv)
      end

  | Choose (v, None, e) ->
      let v, scx = adj_ty0 scx v (TAtm TAIdv) in
      let e, ty0 = expr scx e in
      let ret = Choose (v, None, force_bool ty0 e) @@ oe in
      (ret, TAtm TAIdv)

  | Apply ({ core = Internal (B.Mem | B.Notmem) } as op, [ e ; f ]) ->
      let e, ty01 = expr scx e in
      let f, ty02 = expr scx f in
      begin match ty01, ty02 with
      | ty03, TSet ty04 when typelvl scx = 3 && ty03 = ty04->
          let op = assign op Props.tpars_prop [ ty03 ] in
          let ret = Apply (op, [ e ; f ]) @@ oe in
          (ret, TAtm TABol)
      | _, _ ->
          let ret = Apply (op, [ force_idv ty01 e ; force_idv ty02 f ]) @@ oe in
          (ret, TAtm TABol)
      end

  | Apply ({ core = Internal B.Subseteq } as op, [ e ; f ]) ->
      let e, ty01 = expr scx e in
      let f, ty02 = expr scx f in
      begin match ty01, ty02 with
      | TSet ty03, TSet ty04 when typelvl scx = 3 && ty03 = ty04 ->
          let op = assign op Props.tpars_prop [ ty03 ] in
          let ret = Apply (op, [ e ; f ]) @@ oe in
          (ret, TAtm TABol)
      | TSet ty03, TSet ty04 when typelvl scx = 2 && ty03 = ty04 ->
          let ret = Apply (op, [ force_idv ty01 e ; force_idv ty02 f ]) @@ oe in
          (ret, TAtm TABol)
      | _, _ ->
          let ret = Apply (op, [ force_idv ty01 e ; force_idv ty02 f ]) @@ oe in
          (ret, TAtm TABol)
      end

  | SetEnum es ->
      let es, ty01s = List.map (expr scx) es |> List.split in
      begin match ty01s with
      | [] when typelvl scx = 3 ->
          let ret = SetEnum es @@ oe in
          let ret = assign ret Props.tpars_prop [ TAtm TAIdv ] in
          (ret, TSet (TAtm TAIdv))
      | [] when typelvl scx = 2 ->
          let ret = SetEnum es @@ oe in
          (ret, TSet (TAtm TAIdv))
      | ty03 :: ty04s when typelvl scx = 3 && List.for_all ((=) ty03) ty04s ->
          let ret = SetEnum es @@ oe in
          let ret = assign ret Props.tpars_prop [ ty03 ] in
          (ret, TSet ty03)
      | ty03 :: ty04s when typelvl scx = 2 && List.for_all ((=) ty03) ty04s ->
          let ret = SetEnum (List.map2 force_idv ty01s es) @@ oe in
          (ret, TSet ty03)
      | _ ->
          let ret = SetEnum (List.map2 force_idv ty01s es) @@ oe in
          (ret, TAtm TAIdv)
      end

  | Apply ({ core = Internal B.UNION } as op, [ e ]) ->
      let e, ty01 = expr scx e in
      begin match ty01 with
      | TSet (TSet ty02) when typelvl scx = 3 ->
          let op = assign op Props.tpars_prop [ ty02 ] in
          let ret = Apply (op, [ e ]) @@ oe in
          (ret, TSet ty02)
      | TSet (TSet ty02) when typelvl scx = 2 ->
          let ret = Apply (op, [ force_idv ty01 e ]) @@ oe in
          (ret, TSet ty02)
      | _ ->
          let ret = Apply (op, [ force_idv ty01 e ]) @@ oe in
          (ret, TAtm TAIdv)
      end

  | Apply ({ core = Internal B.SUBSET } as op, [ e ]) ->
      let e, ty01 = expr scx e in
      begin match ty01 with
      | TSet ty02 when typelvl scx = 3 ->
          let op = assign op Props.tpars_prop [ ty02 ] in
          let ret = Apply (op, [ e ]) @@ oe in
          (ret, TSet (TSet ty02))
      | TSet ty02 when typelvl scx = 2 ->
          let ret = Apply (op, [ force_idv ty01 e ]) @@ oe in
          (ret, TSet (TSet ty02))
      | _ ->
          let ret = Apply (op, [ force_idv ty01 e ]) @@ oe in
          (ret, TAtm TAIdv)
      end

  | SetSt (v, e, f) ->
      let e, ty01 = expr scx e in
      begin match ty01 with
      | TSet ty02 when typelvl scx = 3 ->
          let v, scx = adj_ty0 scx v ty02 in
          let f, ty03 = expr scx f in
          let ret = SetSt (v, e, force_bool ty03 f) @@ oe in
          let ret = assign ret Props.tpars_prop [ ty02 ] in
          (ret, TSet ty02)
      | TSet ty02 when typelvl scx = 2 ->
          let v, scx = adj_ty0 scx v (TAtm TAIdv) in
          let f, ty03 = expr scx f in
          let ret = SetSt (v, force_idv ty01 e, force_bool ty03 f) @@ oe in
          (ret, TSet ty02)
      | _ ->
          let v, scx = adj_ty0 scx v (TAtm TAIdv) in
          let f, ty03 = expr scx f in
          let ret = SetSt (v, force_idv ty01 e, force_bool ty03 f) @@ oe in
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
        if typelvl scx > 1 then try
          Some (List.map (function TSet ty0 -> ty0 | _ -> failwith "") ty01s)
        with _ -> None
        else None
      in
      begin match oty02s with
      | Some ty03s when typelvl scx = 3 ->
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
          let ret = assign ret Props.tpars_prop (ty04 :: ty03s) in
          (ret, TSet ty04)
      | Some ty03s when typelvl scx = 2 ->
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
          let ret = assign ret Props.tpars_prop (ty04 :: ty03s) in
          (ret, TSet ty04)
      | _ ->
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
      | TSet ty03, TSet ty04 when typelvl scx = 3 && ty03 = ty04 ->
          let op = assign op Props.tpars_prop [ ty03 ] in
          let ret = Apply (op, [ e ; f ]) @@ oe in
          (ret, TSet ty03)
      | TSet ty03, TSet ty04 when typelvl scx = 2 && ty03 = ty04 ->
          let ret = Apply (op, [ force_idv ty01 e ; force_idv ty02 f ]) @@ oe in
          (ret, TSet ty03)
      | _, _ ->
          let ret = Apply (op, [ force_idv ty01 e ; force_idv ty02 f ]) @@ oe in
          (ret, TAtm TAIdv)
      end

  | Internal B.BOOLEAN ->
      if typelvl scx >= 2 then
        let ret = Internal B.BOOLEAN @@ oe in
        (ret, TSet (TAtm TABol))
      else
        let ret = Internal B.BOOLEAN @@ oe in
        (ret, TAtm TAIdv)

  | Internal B.STRING ->
      if typelvl scx >= 2 then
        let ret = Internal B.STRING @@ oe in
        (ret, TSet (TAtm TAStr))
      else
        let ret = Internal B.STRING @@ oe in
        (ret, TAtm TAIdv)

  | String s ->
      if typelvl scx >= 2 then
        let ret = String s @@ oe in
        (ret, TAtm TAStr)
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
        if typelvl scx > 1 then try
          Some (List.map (function TSet ty0 -> ty0 | _ -> failwith "") ty01s)
        with _ -> None
        else None
      in
      begin match oty02s with
      | Some ty03s when typelvl scx = 3 ->
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
          let ret = assign ret Props.tpars_prop (ty03s @ [ ty04 ]) in
          (ret, ty0)
      | Some ty03s when typelvl scx = 2 ->
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
          let ty0 =
            match ty03s with
            | [ ty05 ] -> TFun (ty05, ty04)
            | _ -> TFun (TPrd ty03s, ty04)
          in
          (ret, ty0)
      | _ ->
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
      | TFun (ty02, ty03) when typelvl scx = 3 ->
          let op = assign op Props.tpars_prop [ ty01 ] in
          let ret = Apply (op, [ e ]) @@ oe in
          (ret, TSet ty02)
      | TPrd ty02s when typelvl scx = 3 ->
          let op = assign op Props.tpars_prop [ ty01 ] in
          let ret = Apply (op, [ e ]) @@ oe in
          (ret, TSet (TAtm TAInt))
      | TRec fty0s when typelvl scx = 3 ->
          let op = assign op Props.tpars_prop [ ty01 ] in
          let ret = Apply (op, [ e ]) @@ oe in
          (ret, TSet (TAtm TAStr))
      | TFun (ty02, ty03) when typelvl scx = 2 ->
          let ret = Apply (op, [ force_idv ty01 e ]) @@ oe in
          (ret, TSet ty02)
      | TPrd ty02s when typelvl scx = 2 ->
          let ret = Apply (op, [ force_idv ty01 e ]) @@ oe in
          (ret, TSet (TAtm TAInt))
      | TRec fty0s when typelvl scx = 2 ->
          let ret = Apply (op, [ force_idv ty01 e ]) @@ oe in
          (ret, TSet (TAtm TAStr))
      | _ ->
          let ret = Apply (op, [ force_idv ty01 e ]) @@ oe in
          (ret, TAtm TAIdv)
      end

  | FcnApp (e1, [{ core = Num (n, "") } as e2]) ->
      let e1, ty01 = expr scx e1 in
      let n = int_of_string n in
      begin match ty01 with
      | TPrd ty03s when typelvl scx = 3 && List.length ty03s >= n ->
          let ret = FcnApp (e1, [ e2 ]) @@ oe in
          let ret = assign ret Props.tpars_prop [ ty01 ] in
          (ret, List.nth ty03s (n-1))
      | TPrd ty03s when typelvl scx = 2 && List.length ty03s >= n ->
          let e2 = assign e2 Props.tpars_prop [ ] in
          let ret = FcnApp (force_idv ty01 e1, [ force_idv (TAtm TAInt) e2 ]) @@ oe in
          let ty04 = List.nth ty03s (n-1) in
          let ret = proj ty04 ret in
          (ret, ty04)
      | _ ->
          let oe = FcnApp (e1, [ Apply (e2, []) %% [] ]) @@ oe in
          expr scx oe
      end

  | FcnApp (e1, [{ core = String s } as e2]) ->
      let e1, ty01 = expr scx e1 in
      begin match ty01 with
      | TRec fty0s when typelvl scx = 3 && List.exists (fun (f, _) -> f = s) fty0s ->
          let ret = FcnApp (e1, [ e2 ]) @@ oe in
          let ret = assign ret Props.tpars_prop [ ty01 ] in
          let ty02 = List.find (fun (f, _) -> f = s) fty0s |> snd in
          (ret, ty02)
      | TRec fty0s when typelvl scx = 2 && List.exists (fun (f, _) -> f = s) fty0s ->
          let ret = FcnApp (force_idv ty01 e1, [ e2 ]) @@ oe in
          let ty02 = List.find (fun (f, _) -> f = s) fty0s |> snd in
          let ret = proj ty02 ret in
          (ret, ty02)
      | _ ->
          let oe = FcnApp (e1, [ Apply (e2, []) %% [] ]) @@ oe in
          expr scx oe
      end

  | FcnApp (e, es) ->
      let e, ty01 = expr scx e in
      let es, ty02s = List.map (expr scx) es |> List.split in
      begin match ty01 with
      | TFun (TPrd ty03s, ty04) when typelvl scx = 3 && List.for_all2 (=) ty02s ty03s ->
          let ret = FcnApp (e, es) @@ oe in
          let ret = assign ret Props.tpars_prop [ ty01 ] in
          (*(ret, ty04)*)
          (ret, TAtm TAIdv)
      | TFun (ty03, ty04) when typelvl scx = 3 && List.length es = 1 && List.hd ty02s = ty03 ->
          let ret = FcnApp (e, es) @@ oe in
          let ret = assign ret Props.tpars_prop [ ty01 ] in
          (*(ret, ty04)*)
          (ret, TAtm TAIdv)
      | TFun (TPrd ty03s, ty04) when typelvl scx = 2 && List.for_all2 (=) ty02s ty03s ->
          let ret = FcnApp (force_idv ty01 e, List.map2 force_idv ty02s es) @@ oe in
          (*(ret, ty04)*)
          (ret, TAtm TAIdv)
      | TFun (ty03, ty04) when typelvl scx = 2 && List.length es = 1 && List.hd ty02s = ty03 ->
          let ret = FcnApp (force_idv ty01 e, List.map2 force_idv ty02s es) @@ oe in
          (*(ret, ty04)*)
          (ret, TAtm TAIdv)
      | _ ->
          let ret = FcnApp (force_idv ty01 e, List.map2 force_idv ty02s es) @@ oe in
          (ret, TAtm TAIdv)
      end

  | Dot (e, s) ->
      let e, ty01 = expr scx e in
      begin match ty01 with
      | TFun (TAtm TAStr, ty02) when typelvl scx = 3 ->
          let ret = Dot (e, s) @@ oe in
          let ret = assign ret Props.tpars_prop [ ty01 ] in
          (ret, ty02)
      | TRec fty0s when typelvl scx = 3 && List.exists (fun (f, _) -> f = s) fty0s ->
          let ret = Dot (e, s) @@ oe in
          let ret = assign ret Props.tpars_prop [ ty01 ] in
          let ty02 = List.find (fun (f, _) -> f = s) fty0s |> snd in
          (ret, ty02)
      | TFun (TAtm TAStr, ty02) when typelvl scx = 2 ->
          let ret = Dot (force_idv ty01 e, s) @@ oe in
          let ret = proj ty02 ret in
          (ret, ty02)
      | TRec fty0s when typelvl scx = 2 && List.exists (fun (f, _) -> f = s) fty0s ->
          let ret = Dot (force_idv ty01 e, s) @@ oe in
          let ty02 = List.find (fun (f, _) -> f = s) fty0s |> snd in
          let ret = proj ty02 ret in
          (ret, ty02)
      | _ ->
          let ret = Dot (force_idv ty01 e, s) @@ oe in
          (ret, TAtm TAIdv)
      end

  | Product es ->
      let es, ty01s = List.map (expr scx) es |> List.split in
      let oty02s =
        if typelvl scx > 1 then try
          Some (List.map (function TSet ty0 -> ty0 | _ -> failwith "") ty01s)
        with _ -> None
        else None
      in
      begin match oty02s with
      | Some ty02s when typelvl scx = 3 ->
          let ret = Product es @@ oe in
          let ret = assign ret Props.tpars_prop ty02s in
          (ret, TSet (TPrd ty02s))
      | Some ty02s when typelvl scx = 2 ->
          let ret = Product (List.map2 force_idv ty01s es) @@ oe in
          (ret, TSet (TPrd ty02s))
      | _ ->
          let ret = Product (List.map2 force_idv ty01s es) @@ oe in
          (ret, TAtm TAIdv)
      end

  | Tuple es ->
      let es, ty0s = List.map (expr scx) es |> List.split in
      if typelvl scx = 3 then
        let ret = Tuple es @@ oe in
        let ret = assign ret Props.tpars_prop ty0s in
        (ret, TPrd ty0s)
      else if typelvl scx = 2 then
        let ret = Tuple (List.map2 force_idv ty0s es) @@ oe in
        (ret, TPrd ty0s)
      else
        let ret = Tuple (List.map2 force_idv ty0s es) @@ oe in
        (ret, TAtm TAIdv)

  | Arrow (e, f) ->
      let e, ty01 = expr scx e in
      let f, ty02 = expr scx f in
      begin match ty01, ty02 with
      | TSet ty03, TSet ty04 when typelvl scx = 3 ->
          let ret = Arrow (e, f) @@ oe in
          let ret = assign ret Props.tpars_prop [ ty03 ; ty04 ] in
          (ret, TSet (TFun (ty03, ty04)))
      | TSet ty03, TSet ty04 when typelvl scx = 2 ->
          let ret = Arrow (force_idv ty01 e, force_idv ty02 f) @@ oe in
          (ret, TSet (TFun (ty03, ty04)))
      | _, _ ->
          let ret = Arrow (force_idv ty01 e, force_idv ty02 f) @@ oe in
          (ret, TAtm TAIdv)
      end

  | Rect fs ->
      let fs, ty01s =
        List.map begin fun (f, e) ->
          let e, ty0 = expr scx e in
          (f, e), ty0
        end fs |>
        List.split
      in
      let oty02s =
        if typelvl scx > 1 then try
          Some (List.map (function TSet ty0 -> ty0 | _ -> failwith "") ty01s)
        with _ -> None
        else None
      in
      begin match oty02s with
      | Some ty02s when typelvl scx = 3 ->
          let ret = Rect fs @@ oe in
          let ret = assign ret Props.tpars_prop ty02s in
          let fty0s = List.map2 (fun (f, _) ty0 -> (f, ty0)) fs ty02s in
          (ret, TSet (TRec fty0s))
      | Some ty02s when typelvl scx = 3 ->
          let fs = List.map2 (fun (f, e) ty0 -> (f, force_idv ty0 e)) fs ty01s in
          let ret = Rect fs @@ oe in
          let fty0s = List.map2 (fun (f, _) ty0 -> (f, ty0)) fs ty02s in
          (ret, TSet (TRec fty0s))
      | _ ->
          let fs = List.map2 (fun (f, e) ty0 -> (f, force_idv ty0 e)) fs ty01s in
          let ret = Rect fs @@ oe in
          (ret, TAtm TAIdv)
      end

  | Record fs ->
      let fs, ty0s =
        List.map begin fun (f, e) ->
          let e, ty0 = expr scx e in
          (f, e), ty0
        end fs |>
        List.split
      in
      if typelvl scx = 3 then
        let ret = Record fs @@ oe in
        let ret = assign ret Props.tpars_prop ty0s in
        let fty0s = List.map2 (fun (f, _) ty0 -> (f, ty0)) fs ty0s in
        (ret, TRec fty0s)
      else if typelvl scx = 2 then
        let fs = List.map2 (fun (f, e) ty0 -> (f, force_idv ty0 e)) fs ty0s in
        let ret = Record fs @@ oe in
        let fty0s = List.map2 (fun (f, _) ty0 -> (f, ty0)) fs ty0s in
        (ret, TRec fty0s)
      else
        let fs = List.map2 (fun (f, e) ty0 -> (f, force_idv ty0 e)) fs ty0s in
        let ret = Record fs @@ oe in
        (ret, TAtm TAIdv)

  | Except (e, exps) ->
      (* FIXME implement for the simplest case, overloaded for functions and records *)
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
        if typelvl scx = 3 then begin
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
      | Some ty04s when typelvl scx = 3 ->
          let ret = Except (e, exps) @@ oe in
          let ret = assign ret Props.tpars_prop ty04s in
          (ret, ty01)
      (* FIXME typelvl = 2 missing *)
      | _ ->
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
      (* NOTE Same behavior for typelvl = 2, 3
       * but axioms will differ *)
      if typelvl scx > 1 then
        let ret = Internal B.Nat @@ oe in
        (ret, TSet (TAtm TAInt))
      else
        let ret = Internal B.Nat @@ oe in
        (ret, TAtm TAIdv)

  | Internal B.Int ->
      (* NOTE Same behavior for typelvl = 2, 3
       * but axioms will differ *)
      if typelvl scx > 1 then
        let ret = Internal B.Int @@ oe in
        (ret, TSet (TAtm TAInt))
      else
        let ret = Internal B.Int @@ oe in
        (ret, TAtm TAIdv)

  | Internal B.Real ->
      if typelvl scx = 3 then
        let ret = Internal B.Real @@ oe in
        let ret = assign ret Props.tpars_prop [ ] in
        (ret, TSet (TAtm TARel))
      else if typelvl scx = 2 then
        let ret = Internal B.Real @@ oe in
        (ret, TSet (TAtm TARel))
      else
        let ret = Internal B.Real @@ oe in
        (ret, TAtm TAIdv)

  | Num (s, "") ->
      if typelvl scx > 0 then
        let ret = Num (s, "") @@ oe in
        let ret = assign ret Props.tpars_prop [ ] in
        (ret, TAtm TAInt)
      else
        let ret = Num (s, "") @@ oe in
        (ret, TAtm TAIdv)

  | Num (s1, s2) ->
      if typelvl scx > 0 then
        let ret = Num (s1, s2) @@ oe in
        let ret = assign ret Props.tpars_prop [ ] in
        (ret, TAtm TARel)
      else
        let ret = Num (s1, s2) @@ oe in
        (ret, TAtm TAIdv)

  | Internal B.Infinity ->
      if typelvl scx > 0 then
        let ret = Internal B.Infinity @@ oe in
        let ret = assign ret Props.tpars_prop [ ] in
        (ret, TAtm TARel)
      else
        let ret = Internal B.Infinity @@ oe in
        (ret, TAtm TAIdv)

  | Apply ({ core = Internal (B.Plus | B.Minus | B.Times | B.Exp) } as op, [ e ; f ]) ->
      let e, ty01 = expr scx e in
      let f, ty02 = expr scx f in
      begin match ty01, ty02 with
      | TAtm TAInt, TAtm TAInt when typelvl scx > 1 ->
          let op = assign op Props.tpars_prop [ TAtm TAInt ] in
          let ret = Apply (op, [ e ; f ]) @@ oe in
          (ret, TAtm TAInt)
      | TAtm TARel, TAtm TARel when typelvl scx > 1 ->
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
      | TAtm TAInt when typelvl scx > 1 ->
          let op = assign op Props.tpars_prop [ TAtm TAInt ] in
          let ret = Apply (op, [ e ]) @@ oe in
          (ret, TAtm TAInt)
      | TAtm TARel when typelvl scx <> 1 ->
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
      (* FIXME disabled because unsound Quotient and Remainder expect second arg to be < 0 *)
      (*| TAtm TAInt, TAtm TAInt when typelvl scx > 1 ->
          let op = assign op Props.tpars_prop [ ] in
          let ret = Apply (op, [ e ; f ]) @@ oe in
          (ret, TAtm TAInt)*)
      | _, _ ->
          let ret = Apply (op, [ force_idv ty01 e ; force_idv ty02 f ]) @@ oe in
          (ret, TAtm TAIdv)
      end

  | Apply ({ core = Internal B.Range } as op, [ e ; f ]) ->
      let e, ty01 = expr scx e in
      let f, ty02 = expr scx f in
      begin match ty01, ty02 with
      | _, _ when typelvl scx > 1 ->
          let ret = Apply (op, [ force_idv ty01 e ; force_idv ty02 f ]) @@ oe in
          (* NOTE Intervals are always sets of integers *)
          (ret, TSet (TAtm TAInt))
      | _, _ ->
          let ret = Apply (op, [ force_idv ty01 e ; force_idv ty02 f ]) @@ oe in
          (ret, TAtm TAIdv)
      end

  | Apply ({ core = Internal (B.Lteq | B.Lt | B.Gteq | B.Gt) } as op, [ e ; f ]) ->
      let e, ty01 = expr scx e in
      let f, ty02 = expr scx f in
      begin match ty01, ty02 with
      | TAtm TAInt, TAtm TAInt when typelvl scx > 1 ->
          let op = assign op Props.tpars_prop [ TAtm TAInt ] in
          let ret = Apply (op, [ e ; f ]) @@ oe in
          (ret, TAtm TABol)
      | _, _ ->
          let ret = Apply (op, [ force_idv ty01 e ; force_idv ty02 f ]) @@ oe in
          (ret, TAtm TABol)
      end

  (* NOTE Sequences implemented as untyped operators only *)

  | Apply ({ core = Internal (B.Seq | B.Len | B.BSeq | B.Head | B.Tail) } as op, [ e ]) ->
      let e, ty0 = expr scx e in
      let ret = Apply (op, [ force_idv ty0 e ]) @@ oe in
      (ret, TAtm TAIdv)

  | Apply ({ core = Internal (B.Cat | B.Append) } as op, [ e ; f ]) ->
      let e, ty01 = expr scx e in
      let f, ty02 = expr scx f in
      let ret = Apply (op, [ force_idv ty01 e ; force_idv ty02 f ]) @@ oe in
      (ret, TAtm TAIdv)

  | Apply ({ core = Internal B.SubSeq } as op, [ e ; f ; g ]) ->
      let e, ty01 = expr scx e in
      let f, ty02 = expr scx f in
      let g, ty03 = expr scx g in
      let ret = Apply (op, [ force_idv ty01 e ; force_idv ty02 f ; force_idv ty03 g ]) @@ oe in
      (ret, TAtm TAIdv)

  | Apply ({ core = Internal B.SelectSeq } as op, [ e ; f ]) ->
      let e, ty0 = expr scx e in
      let f, ty1 = earg scx f in
      let ret = Apply (op, [ force_idv ty0 e ; force_arg (Ty1 ([ TAtm TAIdv ], TAtm TABol)) ty1 f ]) @@ oe in
      (ret, TAtm TAIdv)

  (* The code may wrap `e` like this to prevent infinite loops.
   * Do not remove! *)
  | Apply (e, []) ->
      expr scx e

  | Apply (op, es) ->
      (* no type synthesis in this case, only typechecking *)
      let op, Ty2 (ty11s, ty01) = eopr scx op in
      let es, ty12s = List.map (earg scx) es |> List.split in
      let es =
        map3 begin fun e ty11 ty12 ->
          if ty11 = ty12 then
            e
          else
            force_arg ty11 ty12 e
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

and sequent scx sq =
  let force_idv ty x = force_idv ~typelvl:(typelvl scx) ty x in

  let rec hyps scx hs =
    match Deque.front hs with
    | None ->
        (scx, Deque.empty)

    | Some ({ core = Fresh (v, Shape_expr, k, b) } as h, hs) ->
        let v, scx, b =
          match b with
          | Bounded (e, Visible) ->
              let e, ty0 = expr scx e in
              begin match ty0 with
              | TSet ty01 when typelvl scx = 3 ->
                  let v, scx = adj_ty0 scx v ty01 in
                  let b = Bounded (assign e Props.mpars_prop ty01, Visible) in
                  (v, scx, b)
              | TSet (TAtm _ as ty01) when typelvl scx = 2 ->
                  let v, scx = adj_ty0 scx v ty01 in
                  let b = Bounded (force_idv ty0 e, Visible) in
                  let v = force_idv ty01 v in
                  (v, scx, b)
              | TSet ty01 when typelvl scx = 2 ->
                  let _, scx = adj_ty0 scx v ty01 in
                  let v = assign v Props.ty0_prop (TAtm TAIdv) in
                  let b = Bounded (force_idv ty0 e, Visible) in
                  (v, scx, b)
              | _ ->
                  let v, scx = adj_ty0 scx v (TAtm TAIdv) in
                  let b = Bounded (force_idv ty0 e, Visible) in
                  (v, scx, b)
              end
          | _ when typelvl scx = 2 ->
              let inferer = fun hx e -> snd (expr (fst scx, hx) e) in
              begin match T_hyps.search_type_hyp ~inferer ~pol:true (snd scx) (Sequent { context = hs ; active = sq.active } %% []) with
              | Some (TAtm _ as ty01) ->
                  let v, scx = adj_ty0 scx v ty01 in
                  let v = force_idv ty01 v in
                  (v, scx, b)
              | Some ty01 ->
                  let _, scx = adj_ty0 scx v ty01 in
                  let v = assign v Props.ty0_prop (TAtm TAIdv) in
                  (v, scx, b)
              | None ->
                  let v, scx = adj_ty0 scx v (TAtm TAIdv) in
                  (v, scx, b)
              end
          | _ ->
              let v, scx = adj_ty0 scx v (TAtm TAIdv) in
              (v, scx, b)
        in
        let h = Fresh (v, Shape_expr, k, b) @@ h in
        let scx, hs = hyps scx hs in
        (scx, Deque.cons h hs)

    | Some ({ core = Fresh (v, shp, k, Unbounded) } as h, hs) ->
        let ty1 = shp_to_ty1 shp in
        let v, scx = adj_ty1 scx v ty1 in
        let h = Fresh (v, shp, k, Unbounded) @@ h in
        let scx, hs = hyps scx hs in
        (scx, Deque.cons h hs)

    | Some ({ core = Fresh (_, Shape_op n, _, Bounded _) } as h, hs) ->
        error ~at:h "Fresh operator cannot be bounded"

    | Some ({ core = Flex v } as h, hs) ->
        if typelvl scx = 2 then
          let inferer = fun hx e -> snd (expr (fst scx, hx) e) in
          begin match T_hyps.search_type_hyp ~inferer ~pol:true (snd scx) (Sequent { context = hs ; active = sq.active } %% []) with
          | Some (TAtm _ as ty01) ->
              let v, scx = adj_ty0 scx v ty01 in
              let v = force_idv ty01 v in
              let h = Flex (force_idv ty01 v) @@ h in
              let scx, hs = hyps scx hs in
              (scx, Deque.cons h hs)
          | Some ty01 ->
              let _, scx = adj_ty0 scx v ty01 in
              let v = assign v Props.ty0_prop (TAtm TAIdv) in
              let h = Flex v @@ h in
              let scx, hs = hyps scx hs in
              (scx, Deque.cons h hs)
          | None ->
              let v, scx = adj_ty0 scx v (TAtm TAIdv) in
              let h = Flex v @@ h in
              let scx, hs = hyps scx hs in
              (scx, Deque.cons h hs)
          end
        else
          let v, scx = adj_ty0 scx v (TAtm TAIdv) in
          let h = Flex v @@ h in
          let scx, hs = hyps scx hs in
          (scx, Deque.cons h hs)

    (* Special case: Type inference is activated for hidden constant defns *)
    | Some ({ core = Defn ({ core = Operator (v, e) } as df, wd, Hidden, ex) } as h, hs)
      when typelvl scx = 2 && not (is_lambda e.core) ->
        let inferer = fun hx e -> snd (expr (fst scx, hx) e) in
        let scx, df =
          match T_hyps.search_type_hyp ~inferer ~pol:true (snd scx) (Sequent { context = hs ; active = sq.active } %% []) with
          | Some (TAtm _ as ty0) ->
              let v, scx = adj_ty0 scx v ty0 in
              let v = force_idv ty0 v in
              (scx, Operator (v, e) @@ df)
          | Some ty0 ->
              let _, scx = adj_ty0 scx v ty0 in
              let v = assign v Props.ty0_prop (TAtm TAIdv) in
              (scx, Operator (v, e) @@ df)
          | None ->
              defn ~ignore:true scx df
        in
        let h = Defn (df, wd, Hidden, ex) @@ h in
        let scx, hs = hyps scx hs in
        (scx, Deque.cons h hs)

    | Some ({ core = Defn (df, wd, vis, ex) } as h, hs) ->
        let ignore = match vis with Hidden -> true | _ -> false in
        let scx, df = defn ~ignore scx df in
        let h = Defn (df, wd, vis, ex) @@ h in
        let scx, hs = hyps scx hs in
        (scx, Deque.cons h hs)

    | Some ({ core = Fact (e, Visible, tm) } as h, hs) ->
        let e, ty0 = expr scx e in
        let scx = bump scx in
        let h = Fact (force_bool ty0 e, Visible, tm) @@ h in
        let scx, hs = hyps scx hs in
        (scx, Deque.cons h hs)

    | Some ({ core = Fact (e, Hidden, tm) } as h, hs) ->
        let scx = bump scx in
        let h = Fact (e, Hidden, tm) @@ h in
        let scx, hs = hyps scx hs in
        (scx, Deque.cons h hs)
  in

  let scx, hs = hyps scx sq.context in
  let e, ty0 = expr scx sq.active in
  (scx, { context = hs ; active = force_bool ty0 e })


let main ?(typelvl=1) sq =
  let ops, cx = init in
  let ops =
    { typelvl = typelvl
    }
  in
  snd (sequent (ops, cx) sq)

