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
  let step_names = Seq_acc.make (PS.stepno_seq_under_proof_step ps_parent) in
  let rename_sn sn =
    match sn with
    | Proof.T.Named _ -> Seq_acc.take step_names
    | Proof.T.Unnamed _ -> PS.sub_step_unnamed ps_parent
  in
  let rename_step : 'a. 'a Property.wrapped -> 'a Property.wrapped =
   fun w ->
    match Property.query w Proof.T.Props.step with
    | None -> w
    | Some sn -> Property.assign w Proof.T.Props.step (rename_sn sn)
  in
  match pf.core with
  | Proof.T.Obvious | Proof.T.Omitted _ | Proof.T.By _ | Proof.T.Error _ -> pf
  | Proof.T.Steps (inits, qed) ->
      let inits =
        inits
        |> List.map (fun (stp : Proof.T.step) ->
            (* TODO: make it recursive over all the steps. Probably we have to replace PS.t with something else. *)
            (* let () =
              match stp.core with
              | Proof.T.Hide _ | Proof.T.Define _
              | Proof.T.Assert (_, _)
              | Proof.T.Suffices (_, _)
              | Proof.T.Pcase (_, _)
              | Proof.T.Pick (_, _, _)
              | Proof.T.PickTuply (_, _, _)
              | Proof.T.Use (_, _)
              | Proof.T.Have _ | Proof.T.Take _ | Proof.T.TakeTuply _
              | Proof.T.Witness _ | Proof.T.Forget _ ->
                  ()
            in *)
            rename_step stp)
      in
      let qed =
        rename_step qed |> fun (qed : Proof.T.qed_step) ->
        (* TODO: make it recursive over all the steps. Probably we have to replace PS.t with something else. *)
        (* let () = match qed.core with Proof.T.Qed pf -> rename_steps ~ps_parent in *)
        qed
      in
      Property.(Proof.T.Steps (inits, qed) @@ pf)

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
    match (h.core, Property.query h Module.Gen.proof_orig_indexed_prop) with
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
