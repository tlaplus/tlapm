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
  match (t.core, p.core) with
  (* Explicit parens carry no meaning for matching purposes. *)
  | Expr.T.Parens (t, _), _ -> match_expr' ~cx ~depth ~t ~p
  | _, Expr.T.Parens (p, _) -> match_expr' ~cx ~depth ~t ~p
  | Expr.T.Ix t_ix, Expr.T.Ix p_ix when t_ix = p_ix ->
      (* Expressions are the same, thus they match with no substitutions needed. *)
      Some []
  | _, Expr.T.Ix p_ix when p_ix <= depth ->
      (* [p_ix] refers to a hypothesis introduced in the expression,
         but indexes are different, thus don't match. *)
      None
  | _, Expr.T.Ix p_ix -> (
      let p_hyp = Expr.T.get_val_from_id cx p_ix in
      match p_hyp.core with
      | Expr.T.Fresh (_name, _shape, _kind, Expr.T.Unbounded) ->
          (* OK, this matches anything. *)
          Some [ (p_ix - depth, Expr.Subst.(app_expr (shift (-depth)) t)) ]
      | Expr.T.Fresh (_name, _shape, _kind, _dom) ->
          (* For now, only unbounded NEW _ are considered placeholders. *)
          None
      | Expr.T.FreshTuply (_names, _dom) ->
          (* Tuply placeholders are not supported. *)
          None
      | Expr.T.Flex _name ->
          (* A reference to a state variable is not a placeholder. *)
          None
      | Expr.T.Defn (defn, _where_def, _visibility, _export) -> (
          match defn.core with
          | Expr.T.Operator (_hint, expr) ->
              let expr = Expr.Subst.(app_expr (shift p_ix) expr) in
              match_expr' ~cx ~depth ~t ~p:expr
          | Expr.T.Recursive _ | Expr.T.Instance _ | Expr.T.Bpragma _ -> None)
      | Expr.T.Fact (_expr, _visibility, _time) ->
          (* Facts are not nameable, thus cannot be referenced by an [Ix]. *)
          None)
  | Expr.T.Ix t_ix, _ -> (
      let t_hyp = Expr.T.get_val_from_id cx t_ix in
      match t_hyp.core with
      | Expr.T.Fresh (_, _, _, _) | Expr.T.FreshTuply (_, _) | Expr.T.Flex _ ->
          (* A bare variable/state reference cannot match a compound pattern. *)
          None
      | Expr.T.Defn ((defn : Expr.T.defn), _wheredef, _visible, _export) -> (
          match defn.core with
          | Expr.T.Operator (_hint, expr) ->
              let expr = Expr.Subst.(app_expr (shift t_ix) expr) in
              match_expr' ~cx ~depth ~t:expr ~p
          | Expr.T.Recursive _ | Expr.T.Instance _ | Expr.T.Bpragma _ -> None)
      | Expr.T.Fact (_, _, _) -> None)
  | Expr.T.Lambda _, _ | _, Expr.T.Lambda _ -> None
  | Expr.T.Sequent _, _ | _, Expr.T.Sequent _ -> None
  | Expr.T.Bang _, _ | _, Expr.T.Bang _ -> None
  | Expr.T.With _, _ | _, Expr.T.With _ -> None
  | Expr.T.Let _, _ | _, Expr.T.Let _ -> None
  | Expr.T.Opaque ex, Expr.T.Opaque pt ->
      if String.equal ex pt then Some [] else None
  | Expr.T.Opaque _, _ | _, Expr.T.Opaque _ -> None
  | Expr.T.Internal _, Expr.T.Internal _ ->
      if Expr.Eq.expr t p then Some [] else None
  | Expr.T.Internal _, _ | _, Expr.T.Internal _ -> None
  | Expr.T.String t_s, Expr.T.String p_s ->
      if String.equal t_s p_s then Some [] else None
  | Expr.T.String _, _ | _, Expr.T.String _ -> None
  | Expr.T.Num (t_m, t_n), Expr.T.Num (p_m, p_n) ->
      if String.equal t_m p_m && String.equal t_n p_n then Some [] else None
  | Expr.T.Num _, _ | _, Expr.T.Num _ -> None
  | Expr.T.At t_b, Expr.T.At p_b -> if t_b = p_b then Some [] else None
  | Expr.T.At _, _ | _, Expr.T.At _ -> None
  | Expr.T.Apply (t_op, t_args), Expr.T.Apply (p_op, p_args) ->
      match_expr' ~cx ~depth ~t:t_op ~p:p_op
      |> merge_binding_cont @@ fun () -> match_exprs ~cx ~depth t_args p_args
  | Expr.T.Apply _, _ | _, Expr.T.Apply _ -> None
  | Expr.T.List (t_b, t_es), Expr.T.List (p_b, p_es) ->
      if t_b = p_b then match_exprs ~cx ~depth t_es p_es else None
  | Expr.T.List _, _ | _, Expr.T.List _ -> None
  | Expr.T.If (t1, t2, t3), Expr.T.If (p1, p2, p3) ->
      match_expr' ~cx ~depth ~t:t1 ~p:p1
      |> merge_binding_cont (fun () -> match_expr' ~cx ~depth ~t:t2 ~p:p2)
      |> merge_binding_cont (fun () -> match_expr' ~cx ~depth ~t:t3 ~p:p3)
  | Expr.T.If _, _ | _, Expr.T.If _ -> None
  | Expr.T.Quant (t_q, t_bs, t_ex), Expr.T.Quant (p_q, p_bs, p_ex) ->
      if t_q = p_q then match_bound_body ~cx ~depth ~t_bs ~p_bs ~t_ex ~p_ex
      else None
  | Expr.T.Quant _, _ | _, Expr.T.Quant _ -> None
  | Expr.T.QuantTuply _, _ | _, Expr.T.QuantTuply _ -> None
  | Expr.T.Tquant _, _ | _, Expr.T.Tquant _ -> None
  | Expr.T.Choose (t_hint, t_dom, t_ex), Expr.T.Choose (_, p_dom, p_ex) ->
      match_single_bound ~cx ~depth ~t_hint ~t_dom ~p_dom ~t_ex ~p_ex
  | Expr.T.Choose _, _ | _, Expr.T.Choose _ -> None
  | Expr.T.ChooseTuply _, _ | _, Expr.T.ChooseTuply _ -> None
  | Expr.T.SetSt (t_hint, t_dom, t_ex), Expr.T.SetSt (_, p_dom, p_ex) ->
      match_single_bound ~cx ~depth ~t_hint ~t_dom:(Some t_dom)
        ~p_dom:(Some p_dom) ~t_ex ~p_ex
  | Expr.T.SetSt _, _ | _, Expr.T.SetSt _ -> None
  | Expr.T.SetStTuply _, _ | _, Expr.T.SetStTuply _ -> None
  | Expr.T.SetOf (t_ex, t_bs), Expr.T.SetOf (p_ex, p_bs) ->
      match_bound_body ~cx ~depth ~t_bs ~p_bs ~t_ex ~p_ex
  | Expr.T.SetOf _, _ | _, Expr.T.SetOf _ -> None
  | Expr.T.SetOfTuply _, _ | _, Expr.T.SetOfTuply _ -> None
  | Expr.T.SetEnum t_es, Expr.T.SetEnum p_es -> match_exprs ~cx ~depth t_es p_es
  | Expr.T.SetEnum _, _ | _, Expr.T.SetEnum _ -> None
  | Expr.T.Product t_es, Expr.T.Product p_es -> match_exprs ~cx ~depth t_es p_es
  | Expr.T.Product _, _ | _, Expr.T.Product _ -> None
  | Expr.T.Tuple t_es, Expr.T.Tuple p_es -> match_exprs ~cx ~depth t_es p_es
  | Expr.T.Tuple _, _ | _, Expr.T.Tuple _ -> None
  | Expr.T.Fcn (t_bs, t_ex), Expr.T.Fcn (p_bs, p_ex) ->
      match_bound_body ~cx ~depth ~t_bs ~p_bs ~t_ex ~p_ex
  | Expr.T.Fcn _, _ | _, Expr.T.Fcn _ -> None
  | Expr.T.FcnTuply _, _ | _, Expr.T.FcnTuply _ -> None
  | Expr.T.FcnApp (t_f, t_es), Expr.T.FcnApp (p_f, p_es) ->
      match_exprs ~cx ~depth (t_f :: t_es) (p_f :: p_es)
  | Expr.T.FcnApp _, _ | _, Expr.T.FcnApp _ -> None
  | Expr.T.Arrow (t_a, t_b), Expr.T.Arrow (p_a, p_b) ->
      match_exprs ~cx ~depth [ t_a; t_b ] [ p_a; p_b ]
  | Expr.T.Arrow _, _ | _, Expr.T.Arrow _ -> None
  | Expr.T.Rect t_fs, Expr.T.Rect p_fs -> match_fields ~cx ~depth t_fs p_fs
  | Expr.T.Rect _, _ | _, Expr.T.Rect _ -> None
  | Expr.T.Record t_fs, Expr.T.Record p_fs -> match_fields ~cx ~depth t_fs p_fs
  | Expr.T.Record _, _ | _, Expr.T.Record _ -> None
  | Expr.T.Except (t_e, t_xs), Expr.T.Except (p_e, p_xs) ->
      match_expr' ~cx ~depth ~t:t_e ~p:p_e
      |> merge_binding_cont @@ fun () -> match_exspecs ~cx ~depth t_xs p_xs
  | Expr.T.Except _, _ | _, Expr.T.Except _ -> None
  | Expr.T.Dot (t_e, t_f), Expr.T.Dot (p_e, p_f) ->
      if String.equal t_f p_f then match_expr' ~cx ~depth ~t:t_e ~p:p_e
      else None
  | Expr.T.Dot _, _ | _, Expr.T.Dot _ -> None
  | Expr.T.Sub (t_m, t_e, t_f), Expr.T.Sub (p_m, p_e, p_f) ->
      if t_m = p_m then match_exprs ~cx ~depth [ t_e; t_f ] [ p_e; p_f ]
      else None
  | Expr.T.Sub _, _ | _, Expr.T.Sub _ -> None
  | Expr.T.Tsub (t_m, t_e, t_f), Expr.T.Tsub (p_m, p_e, p_f) ->
      if t_m = p_m then match_exprs ~cx ~depth [ t_e; t_f ] [ p_e; p_f ]
      else None
  | Expr.T.Tsub _, _ | _, Expr.T.Tsub _ -> None
  | Expr.T.Fair (t_fop, t_e, t_f), Expr.T.Fair (p_fop, p_e, p_f) ->
      if t_fop = p_fop then match_exprs ~cx ~depth [ t_e; t_f ] [ p_e; p_f ]
      else None
  | Expr.T.Fair _, _ | _, Expr.T.Fair _ -> None
  | Expr.T.Case (t_arms, t_oth), Expr.T.Case (p_arms, p_oth) ->
      match_case_arms ~cx ~depth t_arms p_arms
      |> merge_binding_cont @@ fun () -> match_case_other ~cx ~depth t_oth p_oth

(** Match each pair of expressions at the same [depth], threading and
    conflict-checking the bindings collected along the way. *)
and match_exprs ~(cx : Expr.T.ctx) ~(depth : int) (ts : Expr.T.expr list)
    (ps : Expr.T.expr list) : bindings option =
  if List.compare_lengths ts ps <> 0 then None
  else
    List.fold_left2
      (fun bs t p ->
        bs |> merge_binding_cont @@ fun () -> match_expr' ~cx ~depth ~t ~p)
      (Some []) ts ps

(** Match a binder over [bounds] (Quant/SetOf/Fcn) together with its body. *)
and match_bound_body ~(cx : Expr.T.ctx) ~(depth : int) ~(t_bs : Expr.T.bounds)
    ~(p_bs : Expr.T.bounds) ~(t_ex : Expr.T.expr) ~(p_ex : Expr.T.expr) :
    bindings option =
  if List.compare_lengths t_bs p_bs <> 0 then None
  else
    let hs = Expr.Visit.hyps_of_bounds t_bs in
    let (), cx' = Expr.Visit.adjs ((), cx) hs in
    match_bounds ~cx ~depth ~t:t_bs ~p:p_bs
    |> merge_binding_cont @@ fun () ->
       match_expr' ~cx:cx' ~depth:(depth + List.length t_bs) ~t:t_ex ~p:p_ex

(** Match a single-variable binder together with its body. *)
and match_single_bound ~(cx : Expr.T.ctx) ~(depth : int) ~(t_hint : Util.hint)
    ~(t_dom : Expr.T.expr option) ~(p_dom : Expr.T.expr option)
    ~(t_ex : Expr.T.expr) ~(p_ex : Expr.T.expr) : bindings option =
  (match (t_dom, p_dom) with
    | None, None -> Some []
    | Some t_d, Some p_d -> match_expr' ~cx ~depth ~t:t_d ~p:p_d
    | Some _, None | None, Some _ -> None)
  |> merge_binding_cont @@ fun () ->
     let h =
       match t_dom with
       | None -> Expr.T.From_hint.make_fresh t_hint Expr.T.Constant
       | Some d -> Expr.T.From_hint.make_bounded_fresh t_hint d
     in
     let (), cx' = Expr.Visit.adj ((), cx) h in
     match_expr' ~cx:cx' ~depth:(depth + 1) ~t:t_ex ~p:p_ex

(** Match fields, pairing them up by name regardless of the order in which they
    were written. *)
and match_fields ~(cx : Expr.T.ctx) ~(depth : int)
    (t_fs : (string * Expr.T.expr) list) (p_fs : (string * Expr.T.expr) list) :
    bindings option =
  if List.compare_lengths t_fs p_fs <> 0 then None
  else
    let by_name = List.sort (fun (a, _) (b, _) -> String.compare a b) in
    List.fold_left2
      (fun bs (t_k, t_v) (p_k, p_v) ->
        if not (String.equal t_k p_k) then None
        else
          bs
          |> merge_binding_cont @@ fun () ->
             match_expr' ~cx ~depth ~t:t_v ~p:p_v)
      (Some []) (by_name t_fs) (by_name p_fs)

and match_exspecs ~(cx : Expr.T.ctx) ~(depth : int) (t_xs : Expr.T.exspec list)
    (p_xs : Expr.T.exspec list) : bindings option =
  if List.compare_lengths t_xs p_xs <> 0 then None
  else
    List.fold_left2
      (fun bs (t_trail, t_res) (p_trail, p_res) ->
        bs
        |> merge_binding_cont (fun () ->
            match_exspec_trail ~cx ~depth t_trail p_trail)
        |> merge_binding_cont (fun () ->
            match_expr' ~cx ~depth ~t:t_res ~p:p_res))
      (Some []) t_xs p_xs

and match_exspec_trail ~(cx : Expr.T.ctx) ~(depth : int)
    (t_trail : Expr.T.expoint list) (p_trail : Expr.T.expoint list) :
    bindings option =
  match (t_trail, p_trail) with
  | [], [] -> Some []
  | Expr.T.Except_dot t_x :: t_tr, Expr.T.Except_dot p_x :: p_tr ->
      if String.equal t_x p_x then match_exspec_trail ~cx ~depth t_tr p_tr
      else None
  | Expr.T.Except_apply t_e :: t_tr, Expr.T.Except_apply p_e :: p_tr ->
      match_expr' ~cx ~depth ~t:t_e ~p:p_e
      |> merge_binding_cont @@ fun () -> match_exspec_trail ~cx ~depth t_tr p_tr
  | _, _ -> None

and match_case_arms ~(cx : Expr.T.ctx) ~(depth : int)
    (t_arms : (Expr.T.expr * Expr.T.expr) list)
    (p_arms : (Expr.T.expr * Expr.T.expr) list) : bindings option =
  if List.compare_lengths t_arms p_arms <> 0 then None
  else
    List.fold_left2
      (fun bs (t_guard, t_body) (p_guard, p_body) ->
        bs
        |> merge_binding_cont (fun () ->
            match_expr' ~cx ~depth ~t:t_guard ~p:p_guard)
        |> merge_binding_cont (fun () ->
            match_expr' ~cx ~depth ~t:t_body ~p:p_body))
      (Some []) t_arms p_arms

and match_case_other ~(cx : Expr.T.ctx) ~(depth : int)
    (t_oth : Expr.T.expr option) (p_oth : Expr.T.expr option) : bindings option
    =
  match (t_oth, p_oth) with
  | None, None -> Some []
  | Some t_o, Some p_o -> match_expr' ~cx ~depth ~t:t_o ~p:p_o
  | Some _, None | None, Some _ -> None

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
