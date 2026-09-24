open Util
open TL

let process_rule (base_sq : Expr.T.sequent) (rule_sq : Expr.T.sequent)
    (rule_ix : int) :
    (Expr.T.ctx * Expr.T.sequent * Matcher.bindings list) option =
  (* Shift the rule SQ on the top of the current CX, join the stacks. *)
  let rule_sq = Expr.Subst.(app_sequent (shift rule_ix) rule_sq) in
  let cx = Util.Deque.append base_sq.context rule_sq.context in

  (* Position at which the original SQ exist in the cx_common. *)
  let orig_ix = Util.Deque.size rule_sq.context in
  let orig_active = Expr.Subst.(app_expr (shift orig_ix) base_sq.active) in

  (* Match the goal and then hypotheses. *)
  match Matcher.match_expr ~cx ~t:orig_active ~p:rule_sq.active with
  | None -> None
  | Some matched -> (
      match Matcher.match_rule_hyps ~cx ~t:base_sq ~p:rule_sq ~matched with
      | [] -> None
      | binding_alts -> Some (cx, rule_sq, binding_alts))

(** We pulled the proof to different context, thus all the step names/levels
    have to be adjusted to match the new context. *)
let rename_steps ~(ps_parent : PS.t) (pf : Proof.T.proof) : Proof.T.proof =
  let open Proof.T in
  let rename_step_prop :
      'a.
      stepno_seq:stepno Seq_acc.t ->
      parent_sn:stepno option ->
      'a Property.wrapped ->
      'a Property.wrapped =
   fun ~stepno_seq ~parent_sn w ->
    match Property.query w Props.step with
    | None -> w
    | Some (Named _) -> Property.assign w Props.step (Seq_acc.take stepno_seq)
    | Some (Unnamed _) ->
        Property.assign w Props.step (PS.unnamed_under_stepno parent_sn)
  in
  let rec rename_proof ~stepno_seq ~parent_sn (pf : proof) : proof =
    match pf.core with
    | Obvious | Omitted _ | By _ | Error _ -> pf
    | Steps (inits, qed) ->
        let inits = List.map (rename_step ~stepno_seq ~parent_sn) inits in
        let qed = rename_qed ~stepno_seq ~parent_sn qed in
        Property.(Steps (inits, qed) @@ pf)
  and rename_step ~stepno_seq ~parent_sn (stp : step) : step =
    let stp = rename_step_prop ~stepno_seq ~parent_sn stp in
    let recurse sub_pf =
      let parent_sn = Property.query stp Props.step in
      let stepno_seq = PS.stepno_seq_under_stepno parent_sn |> Seq_acc.make in
      rename_proof ~stepno_seq ~parent_sn sub_pf
    in
    match stp.core with
    | Assert (sq, sub_pf) -> Property.(Assert (sq, recurse sub_pf) @@ stp)
    | Suffices (sq, sub_pf) -> Property.(Suffices (sq, recurse sub_pf) @@ stp)
    | Pcase (ex, sub_pf) -> Property.(Pcase (ex, recurse sub_pf) @@ stp)
    | Pick (bs, ex, sub_pf) -> Property.(Pick (bs, ex, recurse sub_pf) @@ stp)
    | PickTuply (bs, ex, sub_pf) ->
        Property.(PickTuply (bs, ex, recurse sub_pf) @@ stp)
    | Hide _ | Define _ | Use _ | Have _ | Take _ | TakeTuply _ | Witness _
    | Forget _ ->
        stp
  and rename_qed ~stepno_seq ~parent_sn (qed : qed_step) : qed_step =
    let qed = rename_step_prop ~stepno_seq ~parent_sn qed in
    match qed.core with
    | Qed sub_pf ->
        let parent_sn = Property.query qed Props.step in
        let stepno_seq = PS.stepno_seq_under_stepno parent_sn |> Seq_acc.make in
        Property.(Qed (rename_proof ~stepno_seq ~parent_sn sub_pf) @@ qed)
  in
  let stepno_seq = PS.stepno_seq_under_proof_step ps_parent |> Seq_acc.make in
  let parent_sn = PS.step_name ps_parent in
  rename_proof ~stepno_seq ~parent_sn pf

let code_actions ~cfg:_ (uri : LspT.DocumentUri.t) (ps : PS.t)
    (ps_parent : PS.t) (sq : TL.Expr.T.sequent) =
  (* For now we mark decomposition rules with `ASSUME NEW DECOMPOSITION_RULE`. *)
  let has_marker (sq : Expr.T.sequent) =
    TL.Util.Deque.find sq.context (fun (h : Expr.T.hyp) ->
        match h.core with
        | Expr.T.Fresh (nm, _, _, _) ->
            String.equal nm.core "DECOMPOSITION_RULE"
        | Expr.T.FreshTuply _ | Expr.T.Flex _ | Expr.T.Defn _ | Expr.T.Fact _ ->
            false)
    |> Option.is_some
  in
  let is_rule_sq (h : Expr.T.hyp) =
    match (h.core, Property.query h Module.T.indexed_prf_prop) with
    | Fact (expr, _, _), Some pf -> (
        match expr.core with
        | Sequent sq -> if has_marker sq then Some (sq, pf) else None
        | _ -> None)
    | _ -> None
  in

  (* Go over all the stack and look for decomposition rules. *)
  let cx_len = TL.Util.Deque.size sq.context in
  let cas = ref [] in
  (sq.context
  |> TL.Util.Deque.iter @@ fun i (h : Expr.T.hyp) ->
     (* Look if that's a decomposition rule. *)
     let (rule_opt : (Expr.T.sequent * Proof.T.proof) option) = is_rule_sq h in
     let rule_ix = cx_len - i in

     (* Try to process/match the hypothesis as a rule. *)
     match rule_opt with
     | None -> ()
     | Some (rule_sq, rule_pf) -> (
         let rule_pf =
           TL.(
             Proof.Subst.app_proof
               Expr.Subst.(
                 bumpn (Util.Deque.size rule_sq.context) (shift rule_ix))
               rule_pf)
         in
         match process_rule sq rule_sq rule_ix with
         | None -> ()
         | Some (cx, _rule_sq, binding_alts) ->
             (* Ok, that's a matching rule, and we have binding alternatives. *)
             binding_alts
             |> List.iter (fun bindings ->
                 let rule_pf =
                   rule_pf
                   |> Proof.Subst.app_proof (Matcher.subst_of_bindings bindings)
                 in
                 let rule_pf = rename_steps ~ps_parent rule_pf in

                 match rule_pf.core with
                 | Proof.T.Obvious | Proof.T.Omitted _ | Proof.T.By _
                 | Proof.T.Error _ ->
                     (* Not a rule here. We expect to have steps. *)
                     ()
                 | Proof.T.Steps (steps, qed) ->
                     (* Here we can produce a code-action. *)
                     let fcx, add_steps_rewrite =
                       let buf = Buffer.create 16 in
                       let fmt = Format.formatter_of_buffer buf in
                       let indent = indent_size ps ~nested:false in
                       Fmt.pf fmt "@[<v %d>%s" indent (String.make indent ' ');
                       let fcx =
                         Proof.Fmt.pp_print_steps_inits (fmt_cx cx) fmt steps
                       in
                       Fmt.pf fmt "@]%!";
                       let range = Range.make_before_ln (PS.full_range ps) in
                       (fcx, (range, Buffer.contents buf))
                     in
                     let ps_proof_rewrite =
                       let ps_proof = PS.proof ps |> Option.get in
                       let ps_stepno = PS.step_name ps |> Option.get in
                       let prev_usable =
                         match ps_proof.core with
                         | Proof.T.By (usable, _) -> usable
                         | Proof.T.Obvious | Proof.T.Omitted _ | Proof.T.Steps _
                         | Proof.T.Error _ ->
                             Usable.empty
                       in
                       let buf = Buffer.create 16 in
                       let fmt = Format.formatter_of_buffer buf in
                       let indent = indent_size ps ~nested:false in
                       Fmt.pf fmt "@[<v %d>" indent;
                       let qed =
                         match qed.core with
                         | Proof.T.Qed qed_pf -> (
                             let qed_pf =
                               match
                                 (* TODO: Maybe we have to take it for the other steps as well. *)
                                 Property.query qed Proof.T.Props.orig_proof
                               with
                               | None -> qed_pf
                               | Some pf -> pf
                             in
                             match qed_pf.core with
                             | Proof.T.Obvious | Proof.T.Omitted _ ->
                                 Property.(
                                   Proof.T.Qed
                                     (Proof.T.By (prev_usable, false) @@ qed_pf)
                                   @@ qed)
                             | Proof.T.By (usable, _) ->
                                 Property.(
                                   Proof.T.Qed
                                     (Proof.T.By
                                        ( {
                                            facts =
                                              List.append usable.facts
                                                prev_usable.facts;
                                            defs =
                                              List.append usable.defs
                                                prev_usable.defs;
                                          },
                                          false )
                                     @@ qed_pf)
                                   @@ qed)
                             | Proof.T.Steps _ | Proof.T.Error _ -> qed)
                       in
                       let qed =
                         Property.assign qed Proof.T.Props.step ps_stepno
                       in
                       Proof.Fmt.pp_print_steps_qed fcx fmt qed;
                       Fmt.pf fmt "@]@.";
                       let range = PS.full_range ps in
                       let range = Range.with_start_line range in
                       (range, Buffer.contents buf)
                     in
                     let ca =
                       ca_edits ~uri ~title:"⤮ Decompose by rule"
                         ~edits:[ add_steps_rewrite; ps_proof_rewrite ]
                     in
                     cas := ca :: !cas)));

  !cas |> List.rev
