open Tlapm_lib

type bindings = (int * Expr.T.expr) list

let pp_bindings cx fmt bindings =
  let pp_hyp cx fmt hyp =
    ignore Expr.Fmt.(pp_print_hyp (ctx_of_expr_ctx cx) fmt hyp)
  in
  let pp_ex = Expr.Fmt.(pp_print_expr (cx, Ctx.dot)) in
  let pp_ix fmt ix =
    Fmt.pf fmt "%d=%a" ix (pp_hyp cx) (Expr.T.get_val_from_id cx ix)
  in
  Fmt.pf fmt "Matched[@[%a@]]"
    Fmt.(
      list
        ~sep:(fun fmt () -> Fmt.pf fmt ";@ ")
        (pair ~sep:(const string "=>") pp_ix pp_ex))
    bindings

let pp_bindings_opt cx fmt matched =
  match matched with
  | None -> Fmt.pf fmt "NoMatch"
  | Some bindings -> pp_bindings cx fmt bindings

let add_binding ((ix, ex) : int * Expr.T.expr) (bs : bindings option) :
    bindings option =
  match bs with
  | None -> None
  | Some bs -> (
      match List.assoc_opt ix bs with
      | None -> Some ((ix, ex) :: bs)
      | Some ex' when Expr.Eq.expr ex ex' -> Some bs
      | Some _ ->
          (* Conflicting bindings. *)
          None)

(** Call [f] and then merge bindings, if the bindings are not conflicting. *)
let merge_binding_cont f bs =
  match bs with
  | None -> None
  | Some bs -> (
      match f () with
      | None -> None
      | Some new_bs ->
          List.fold_left (fun bs b -> add_binding b bs) (Some bs) new_bs)

(** Returns [None] if expressions don't match, and [Some bindings] if
    expressions match with the bindings applied. The bindings are mappings from
    the wildcard variable indexes to replacement expressions. *)
let rec match_expr' ~(cx : Expr.T.ctx) ~(depth : int) ~(t : Expr.T.expr)
    ~(p : Expr.T.expr) : bindings option =
  (* TODO: Use visitor to maintain the stack properly. *)
  match (t.core, p.core) with
  | Expr.T.Ix t_ix, Expr.T.Ix p_ix when t_ix = p_ix ->
      (* Expressions are the same, thus they match with no substitutions needed. *)
      Some []
  | _, Expr.T.Ix p_ix -> (
      let p_hyp = Expr.T.get_val_from_id cx p_ix in
      match p_hyp.core with
      | Expr.T.Fresh (_name, _shape, _kind, Expr.T.Unbounded) ->
          (* OK, this matches anything. *)
          Some [ (p_ix - depth, Expr.Subst.(app_expr (shift (-depth)) t)) ]
      | Expr.T.Fresh (_name, _shape, _kind, _dom) ->
          (* For now, only unbounded NEW _ are considered placeholders. *)
          None
      | Expr.T.FreshTuply (_names, _dom) -> assert false
      | Expr.T.Flex _name -> assert false
      | Expr.T.Defn (_defn, _where_def, _visibility, _export) -> assert false
      | Expr.T.Fact (_expr, _visibility, _time) -> assert false)
  | Expr.T.Ix t_ix, _ -> (
      let t_hyp = Expr.T.get_val_from_id cx t_ix in
      match t_hyp.core with
      | Expr.T.Fresh (_, _, _, _) | Expr.T.FreshTuply (_, _) | Expr.T.Flex _ ->
          (* TODO: How do we match these? *)
          assert false
      | Expr.T.Defn ((defn : Expr.T.defn), _wheredef, _visible, _export) -> (
          match defn.core with
          | Expr.T.Operator (_hint, expr) ->
              let expr = Expr.Subst.(app_expr (shift t_ix) expr) in
              match_expr' ~cx ~depth ~t:expr ~p
          | Expr.T.Recursive (_, _)
          | Expr.T.Instance (_, _)
          | Expr.T.Bpragma (_, _, _) ->
              assert false)
      | Expr.T.Fact (_, _, _) ->
          (* ... *)
          assert false)
  | Expr.T.Opaque ex, Expr.T.Opaque pt ->
      if String.equal ex pt then Some [] else None
  | Expr.T.Opaque _, _ | _, Expr.T.Opaque _ -> None
  | Expr.T.Internal _, Expr.T.Internal _ ->
      if Expr.Eq.expr t p then Some [] else None
  | Expr.T.Internal _, _ | _, Expr.T.Internal _ -> None
  | Expr.T.Apply (t_op, t_args), Expr.T.Apply (p_op, p_args) -> (
      match match_expr' ~cx ~depth ~t:t_op ~p:p_op with
      | Some bindings ->
          if List.compare_lengths t_args p_args = 0 then
            List.fold_left2
              (fun acc t_arg p_arg ->
                match acc with
                | None -> None
                | Some acc -> (
                    match match_expr' ~cx ~depth ~t:t_arg ~p:p_arg with
                    | None -> None
                    | Some arg_bindings -> Some (List.append acc arg_bindings)))
              (Some bindings) t_args p_args
          else None
      | None -> None)
  | Expr.T.Apply _, _ | _, Expr.T.Apply _ -> None
  | Expr.T.Lambda (_, _), _
  | Expr.T.Sequent _, _
  | Expr.T.Bang (_, _), _
  | Expr.T.With (_, _), _
  | Expr.T.If (_, _, _), _
  | Expr.T.List (_, _), _
  | Expr.T.Let (_, _), _
  | Expr.T.Quant (_, _, _), _
  | Expr.T.QuantTuply (_, _, _), _
  | Expr.T.Tquant (_, _, _), _
  | Expr.T.Choose (_, _, _), _
  | Expr.T.ChooseTuply (_, _, _), _
  | Expr.T.SetSt (_, _, _), _
  | Expr.T.SetStTuply (_, _, _), _ ->
      assert false
  (* SetOf *)
  | Expr.T.SetOf (t_ex, t_bs), Expr.T.SetOf (p_ex, p_bs) ->
      (* TODO: We have to maintain the stack here. *)
      (* let cx' = Expr.Subst.bumpn (List.length bs_a) cx in *)
      let hs = Expr.Visit.hyps_of_bounds t_bs in
      let (), cx' = Expr.Visit.adjs ((), cx) hs in
      match_bounds ~cx ~depth ~t:t_bs ~p:p_bs
      |> merge_binding_cont @@ fun () ->
         match_expr' ~cx:cx' ~depth:(depth + List.length t_bs) ~t:t_ex ~p:p_ex
  | Expr.T.SetOf _, _ | _, Expr.T.SetOf _ -> None
  (* ... *)
  | Expr.T.SetOfTuply (_, _), _
  | Expr.T.SetEnum _, _
  | Expr.T.Product _, _
  | Expr.T.Tuple _, _
  | Expr.T.Fcn (_, _), _
  | Expr.T.FcnTuply (_, _), _
  | Expr.T.FcnApp (_, _), _
  | Expr.T.Arrow (_, _), _
  | Expr.T.Rect _, _
  | Expr.T.Record _, _
  | Expr.T.Except (_, _), _
  | Expr.T.Dot (_, _), _
  | Expr.T.Sub (_, _, _), _
  | Expr.T.Tsub (_, _, _), _
  | Expr.T.Fair (_, _, _), _
  | Expr.T.Case (_, _), _
  | Expr.T.String _, _
  | Expr.T.Num (_, _), _
  | Expr.T.At _, _
  | Expr.T.Parens (_, _), _ ->
      (* TODO: Impl. *)
      assert false

and match_bound ~(cx : Expr.T.ctx) ~(depth : int) ~(t : Expr.T.bound)
    ~(p : Expr.T.bound) =
  match (t, p) with
  | (_t_hint, t_kind, t_dom), (_p_hint, p_kind, p_dom) when t_kind = p_kind -> (
      (* We don't care the names, because later we work with indexes only. *)
      match (t_dom, p_dom) with
      | No_domain, No_domain -> Some []
      | No_domain, _ | _, No_domain -> None
      | Ditto, Ditto -> Some []
      | Ditto, _ | _, Ditto -> None
      | Domain t_ex, Domain p_ex -> match_expr' ~cx ~depth ~t:t_ex ~p:p_ex)
  | (_, _, _), (_, _, _) -> None

(** ts stands for targets, ps - for patterns. *)
and match_bounds ~(cx : Expr.T.ctx) ~(depth : int) ~(t : Expr.T.bounds)
    ~(p : Expr.T.bounds) =
  if List.compare_lengths t p = 0 then
    List.fold_left2
      (fun bs t p ->
        (* TODO: Have to adjust the depth here as well (or replace it with proper use of subst?) *)
        bs |> merge_binding_cont @@ fun () -> match_bound ~cx ~depth ~t ~p)
      (Some []) t p
  else None

let subst_of_bindings (subs : bindings) =
  let open Expr in
  let rec loop i subs =
    match subs with
    | [] -> Subst.shift (i - 1)
    | (n, r) :: subs when i = n -> Subst.(scons r (loop (i + 1) subs))
    | subs -> Subst.scons (T.Ix i |> Property.noprops) (loop (i + 1) subs)
  in
  subs |> List.sort (fun a b -> Int.compare (fst a) (fst b)) |> loop 1

(** Input is the current rule hyp, and all the bindings matched so far. The
    output of a list of binding sets, each corresponding to a possible match.

    Steps:
    - Go over each hypothesis in the rule, for each:
    - Go over all the SQ hypotheses. If it matches, call it recursively with the
      new match and the next hypothesis.

    Parameters:
    - [cx_common] -- ts the sq_base.context with sq_rule.context stacked on it.
      We compare all the expressions at the top of this context.
    - [sq_base] -- if the proof obligation (SQ we try to match against rules).
    - [sq_rule] -- rule pushed to the top of sq_base.
    - [rule_hyp_ix] -- the current rule hypothesis index we are trying to match
      now.
    - [rule_hyp_count] -- just for an optimization [len sq_rule.context]. *)
let rec match_rule_hyps' ~(cx : Expr.T.ctx) ~(t : Expr.T.sequent)
    ~(p : Expr.T.sequent) ~(rule_hyp_ix : int) ~(rule_hyp_count : int)
    ~(matched : bindings) : bindings list =
  if rule_hyp_ix > rule_hyp_count then
    (* Done traversing all the rule hypotheses, return the bindings. *)
    [ matched ]
  else
    match Expr.T.get_val_from_id p.context rule_hyp_ix |> Property.unwrap with
    | Expr.T.Fresh _ | Expr.T.FreshTuply _ | Expr.T.Flex _ | Expr.T.Defn _ ->
        (* Ignore non-fact hypotheses. *)
        match_rule_hyps' ~cx ~t ~p ~rule_hyp_ix:(rule_hyp_ix + 1)
          ~rule_hyp_count ~matched
    | Expr.T.Fact (rule_hyp_ex, _, _) ->
        (* Move the rule hyp to the stack top, apply all the known bindings. *)
        let rule_hyp_ex =
          rule_hyp_ex
          |> Expr.Subst.(app_expr (shift rule_hyp_ix))
          |> Expr.Subst.(app_expr (subst_of_bindings matched))
        in
        (* Traverse all the base hypotheses. *)
        let sq_rule_hyp_count = Util.Deque.size p.context in
        let _, bindings_list =
          Util.Deque.fold_right
            (fun base_hyp (sq_base_hyp_ix, acc) ->
              let base_hyp =
                Expr.Subst.(
                  app_hyp (shift (sq_base_hyp_ix + sq_rule_hyp_count)) base_hyp)
              in
              match base_hyp |> Property.unwrap with
              | Expr.T.Fresh _ | Expr.T.FreshTuply _ | Expr.T.Flex _
              | Expr.T.Defn _ ->
                  (* We only match against expressions. *)
                  (sq_base_hyp_ix + 1, acc)
              | Expr.T.Fact (base_hyp_ex, _, _) -> (
                  (* Ok, found the hypothesis to match with.
                     If it matches, try recurse to other rule hyps. *)
                  match
                    match_expr' ~cx ~depth:0 ~t:base_hyp_ex ~p:rule_hyp_ex
                  with
                  | None -> (sq_base_hyp_ix + 1, acc)
                  | Some b ->
                      let matched = List.append b matched in
                      let nested_matches =
                        match_rule_hyps' ~cx ~t ~p
                          ~rule_hyp_ix:(rule_hyp_ix + 1) ~rule_hyp_count
                          ~matched
                      in
                      (sq_base_hyp_ix + 1, List.append acc nested_matches)))
            t.context (1, [])
        in
        bindings_list

let match_expr ~(cx : Expr.T.ctx) ~(t : Expr.T.expr) ~(p : Expr.T.expr) :
    bindings option =
  match_expr' ~cx ~depth:0 ~t ~p

let match_rule_hyps ~(cx : Expr.T.ctx) ~(t : Expr.T.sequent)
    ~(p : Expr.T.sequent) ~(matched : bindings) : bindings list =
  match_rule_hyps' ~cx ~t ~p ~rule_hyp_ix:1
    ~rule_hyp_count:(Util.Deque.size p.context)
    ~matched
