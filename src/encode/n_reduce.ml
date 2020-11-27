(*
 * encode/reduce.ml --- eliminate higher-order
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)


open Ext
open Property
open Util

open Expr.T
open Type.T

open N_table

module A = N_axioms
module Is = Util.Coll.Is


(* {3 Helpers} *)

let error ?at mssg =
  let mssg = "Encode.Reduce: " ^ mssg in
  Errors.bug ?at mssg


let instantiate sq i e =
  begin if i < 0 then
    raise (Invalid_argument "Encode.Reduce: \\
           bad call to instantiate (i is negative)")
  end;
  let hs_l, h, hs_r =
    let rec spin hs_l hs_r i =
      match Deque.front hs_r with
      | None -> raise (Invalid_argument "Encode.Reduce: \\
                       bad call to instantiate (i is too big)")
      | Some (h, hs_r) ->
          if i = 0 then (hs_l, h, hs_r)
          else spin (Deque.snoc hs_l h) hs_r (i - 1)
    in
    spin Deque.empty sq.context i
  in
  begin match h.core with
  | Fact _ -> raise (Invalid_argument "Encode.Reduce: \\
                     ith quantifier is a fact")
  | Flex _ -> raise (Invalid_argument "Encode.Reduce: \\
                     ith quantifier is a temporal variable")
  | Defn _ -> raise (Invalid_argument "Encode.Reduce: \\
                     ith quantifier is a definition")
  | _ -> ()
  end;
  let sub = Expr.Subst.scons e (Expr.Subst.shift 0) in
  let sq' = Expr.Subst.app_sequent sub { context = hs_r ; active = sq.active } in
  { sq' with context = Deque.append hs_l sq'.context }

let instantiate_expr oe i e =
  match oe.core with
  | Sequent sq ->
      Sequent (instantiate sq i e) @@ oe
  | _ ->
      failwith "internal error"


type ctx = int Expr.Visit.scx

(* NOTE This is the complicated part *)
let do_reduce (k, hx) op ty2 es =
  match ty2 with
  | TSch ([], ty1s_1, ty0)
    when List.length es = List.length ty1s_1 ->

      (* The application is rearranged into `RR(fo_es, xs)` where:
       * - `fo_es` are the filtered first-order `es`;
       * - `xs` are all local variables found in the remaining, higher-order `es`.;
       * - `RR` is a fresh operator.
       * A variable is global if it is bound to a hyp in the top sequent, and
       * local otherwise. *)

      let ho_filt =
        List.map (function TRg _ | TOp ([], _) -> false | _ -> true) ty1s_1
      in

      let sz = Deque.size hx in
      let sz_local = sz - k in

      let is_local = fun i _ -> i <= sz_local in
      let get_local_vs e =
        let vs = Expr.Collect.fvs e in
        let fvs, _ = Expr.Collect.vs_partition hx is_local vs in
        fvs
      in

      let vs_local =
        List.combine es ho_filt |>
        List.filter_map (fun (e, b) -> if b then Some e else None) |>
        List.fold_left begin fun vs e ->
          let vs' = get_local_vs e in
          Is.union vs vs'
        end Is.empty |>
        Is.elements
      in

      let fo_es, ty0s_2 =
        List.combine es ty1s_1 |>
        List.combine ho_filt |>
        List.filter_map begin function
          | false, (e, TRg ty0)
          | false, (e, TOp ([], ty0)) ->
              Some (e, ty0)
          | true, _->
              None
          | _, _ ->
              error "internal error"
        end |>
        List.split
      in

      let xs, ty0s_3 =
        List.map begin fun i ->
          let x = Ix i %% [] in
          let h = Option.get (Deque.nth ~backwards:true hx (i - 1)) in
          let ty0 = get (hyp_hint h) Props.type_prop in
          (x, ty0)
        end vs_local |>
        List.split
      in

      let es'' = fo_es @ xs in

      let ty1s_2 =
        (ty0s_2 @ ty0s_3) |>
        List.map (fun ty0 -> TRg ty0)
      in
      let ty2 = TSch ([], ty1s_2, ty0) in

      let v = "RR" %% [] in
      let v = assign v Props.tsch_prop ty2 in

      (* `RR` is defined so that it corresponds to the original expression.
       * The definition is `RR(xs, ys) == Op(es')` where:
       * - `xs` and `ys` correspond resp. to FO and HO arguments;
       * - `es'` is obtained from the original `es` by mapping FO args to the
       *    correct `xs`, and HO args to themselves but carefully renaming so
       *    that variables are adjusted to `ys`;
       * - `Op` is just `op` adjusted to the top context. *)

      let n_fos = List.length ty0s_2 in
      let n_hos = List.length ty0s_3 in

      let sub_op = Expr.Subst.shift (n_fos + n_hos - sz_local) in
      (* If op is a variable, it is assumed it was declared globally. *)
      let op' = Expr.Subst.app_expr sub_op op in

      (* For HO arguments, the local context is 'squashed', absent variables
       * being mapped to a dummy expr; the global context is shifted to account
       * for the new local context. *)
      let dummy_e = Opaque "IAmError" %% [] in
      let maptos =
        List.init sz_local (fun i -> i + 1) |>
        List.fold_left begin fun (j, es) i ->
          if List.mem i vs_local then
            let j' = j + 1 in
            let e = Ix j' %% [] in
            (j', e :: es)
          else
            let e = dummy_e in
            (j, e :: es)
        end (0, []) |>
        fun (_, r_es) -> List.rev r_es
      in

      let sub_e =
        Expr.Subst.shift (n_fos + n_hos) |>
        List.fold_right Expr.Subst.scons maptos
      in

      let es' =
        List.combine es ho_filt |>
        List.fold_left begin fun (i, es) (e, b) ->
          if b then
            let e = Expr.Subst.app_expr sub_e e in
            (i, e :: es)
          else
            let i' = i - 1 in
            let e = Ix i' %% [] in
            (i', e :: es)
        end (n_fos + n_hos + 1, []) |>
        fun (_, r_es) -> List.rev r_es
      in

      let ys =
        List.init n_fos (fun i -> (("xx" ^ string_of_int i) %% [], Shape_expr)) @
        List.init n_hos (fun i -> (("cc" ^ string_of_int i) %% [], Shape_expr))
      in
      let e' =
        Lambda (ys, Apply (op', es') %% []) %% []
      in

      let df = Operator (v, e') %% [] in
      let h = Defn (df, User, Visible, Local) %% [] in
      (h, es'')

  | _ ->
      raise (Invalid_argument "do_reduce")

let set_ix = object (self : 'self)
  inherit [int] Expr.Visit.map as super
  (** [expr scx oe] replaces occurrences of [Ix 0] with [Ix n] where
      [n] points to an imaginary hyp above [scx].  To use after a single
      reduction step to finish variable renaming.  The [int] parameter
      is an offset to account for absent hypotheses in [scx].
  *)
  method expr scx oe =
    match oe.core with
    | Ix 0 ->
        let n = 1 + Deque.size (snd scx) + (fst scx) in
        Ix n @@ oe
    | _ ->
        super#expr scx oe
end


(* {3 Main} *)

let get_axms (_, hx) op =
  match op.core with
  | Ix n ->
      let h = Option.get (Deque.nth ~backwards:true hx (n - 1)) in
      begin match query h N_axiomatize.axm_ptrs_prop with
      | None -> []
      | Some is ->
          List.filter_map begin fun i ->
            match Deque.nth ~backwards:true hx (n - 1 - i) with
            | Some ({ core = Fact (e, Visible, _) }) -> Some e
            | _ -> None
          end is
      end
  | _ -> []

let visitor = object (self : 'self)
  inherit [int, (hyp Deque.dq) option] Type.Visit.foldmap as super

  (* The fold argument is used to record changes.  While it is [None], a case of
   * second-order application is searched for.  When one is found, the argument
   * becomes [Some hs] ([hs] being the new declarations), and the expression is
   * modified.  No more reductions will be recorded after this point, but the
   * expression is still visited for typechecking. *)
  (* FIXME Actually stop when a case is found; nevermind typechecking *)

  method expr scx a oe =
    match oe.core with
    | Apply (op, es) ->
        let a, op, ty2_1 = self#eopr scx a op in
        let a, es, ty1s_2 =
          List.fold_left begin fun (a, r_es, r_ty1s) e ->
            let a, e, ty1 = self#earg scx a e in
            (a, e :: r_es, ty1 :: r_ty1s)
          end (a, [], []) es |>
          begin fun (a, r_es, r_ty1s) ->
            (a, List.rev r_es, List.rev r_ty1s)
          end
        in

        (* Typecheck and detect second-order at the same time *)
        let b, ty0 =
          match ty2_1 with
          | TSch ([], ty1s_1, ty0) ->
              List.iter2 check_ty1_eq ty1s_1 ty1s_2;
              let b =
                List.exists begin function
                  | TRg _ | TOp ([], _) -> false | _ -> true
                end ty1s_1
              in
              (b, ty0)
          | _ -> error ~at:oe "Polymorphism not supported"
        in

        begin match a, b with
        | Some _, _
        | None, false ->
            (a, Apply (op, es) @@ oe, ty0)
        | None, true ->
            let h, es = do_reduce scx op ty2_1 es in
            (* TODO *)
            let _ = get_axms scx op in
            let hs = Deque.of_list [h] in
            (* Setting new op to special value `Ix 0`
             * Will be corrected when [h] has been inserted *)
            (Some hs, Apply (Ix 0 %% [], es) @@ oe, ty0)
        end

    | _ ->
        super#expr scx a oe

  (* NOTE The methods hyp and hyps are not used.  All the work is done in the
   * method sequent. *)

  method sequent scx _ sq =
    let rec spin scx hs =
      match Deque.front hs with
      | None ->
          let hs, e =
            match Deque.rear (snd scx) with
            | Some (hs, { core = Fact (e, _, _) }) -> (hs, e)
            | _ -> error "Cannot recover conjecture"
          in
          (scx, { context = hs ; active = e })

      | Some ({ core = Fact ({ core = Sequent _ }, Visible, tm) } as h, hs) ->
          (* TODO *)
          let scx = Expr.Visit.adj scx h in
          spin scx hs

      | Some ({ core = Fact (e, Visible, tm) } as h, hs) ->
          (* The method [expr] makes at most one modification, to make the
           * renaming of variables easier.  The method [expr] is called
           * repeatedly on the fact while changes are made. *)
          let rec do_spin (_, hx) (e, hs) =
            let scx = (Deque.size hx, hx) in (* set size of global ctx *)
            match self#expr scx None e with
            | None, e, _ ->
                (scx, e, hs)
            | Some hs', e, _ ->
                (* putting new hyps in scx to make as if they were visited *)
                let scx = Deque.fold_left Expr.Visit.adj scx hs' in
                let sub = Expr.Subst.shift (Deque.size hs') in
                let e = Expr.Subst.app_expr sub e in
                let e = set_ix#expr (Deque.size hs' - 1, Deque.empty) e in
                let _, hs = Expr.Subst.app_hyps sub hs in
                do_spin scx (e, hs)
          in

          let scx, e, hs = do_spin scx (e, hs) in
          let h = Fact (e, Visible, tm) @@ h in
          let scx = Expr.Visit.adj scx h in
          spin scx hs

      | Some (h, hs) ->
          let scx = Expr.Visit.adj scx h in
          spin scx hs
    in
    let hs = Deque.snoc sq.context (Fact (sq.active, Visible, NotSet) %% []) in
    let scx, sq = spin scx hs in
    scx, None, sq
end

let main sq =
  let scx = (0, Deque.empty) in
  let _, _, sq = visitor#sequent scx None sq in
  sq

