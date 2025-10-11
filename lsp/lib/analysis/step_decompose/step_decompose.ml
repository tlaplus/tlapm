(* cspell:words Actplus Cdot Deque Disj Forall Gteq Leadsto Lteq Notmem Setminus Tquant unditto *)
(* cspell:words Tquant Tsub Uminus Unprimable noprops stepno uncons Bpragma Defn  Dvar  assm  filteri *)
open Util

(** Replace {v <1> ... v} with {v <1> ... OBVIOUS v} *)
let ca_omitted ~uri ~ps =
  let title = "⤮ Prove as OBVIOUS" in
  let range = PS.head_range ps |> Range.make_after in
  let newText = " OBVIOUS" in
  ca_edit ~uri ~title ~range ~newText

(** Replace
    {v
      <1> ...
        proof
    v}
    with
    {v
      <1> ...
        <2> QED proof
    v} *)
let ca_to_steps ~uri ~ps ~cx ~pf ~depth =
  let title = "⤮ Make nested" in
  let range =
    match TL.Util.query_locus pf with
    | Some _ ->
        Range.of_points
          (ps |> PS.head_range |> Range.make_after |> Range.from)
          (ps |> PS.full_range |> Range.till)
    | None -> PS.head_range ps |> Range.make_after
  in
  let qed_depth = depth + 1 in
  let pf_pp = TL.Proof.Fmt.pp_print_proof (fmt_cx cx) in
  let newText =
    indent ps ~nested:true (Fmt.str "\n<%d> QED %a" qed_depth pf_pp pf)
  in
  (* TODO: Use ps_proof_rewrite here.  *)
  ca_edit ~uri ~title ~range ~newText

(* Propose code actions for AST nodes containing proofs. *)
let cas_of_el_with_pf (uri : LspT.DocumentUri.t) (ps : PS.t)
    (cx : TL.Expr.T.ctx) (pf : TL.Proof.T.proof) (depth : int) =
  let cas_def_expand (by : (TL.Proof.T.usable * bool) option) =
    let by =
      Option.value ~default:(TL.Proof.T.{ facts = []; defs = [] }, false) by
    in
    PS.goal ps
    |> Option.fold ~none:[] ~some:(fun g ->
           Of_defs.cas_def_expand ~uri ~ps ~cx ~by
             ~sq:TL.Proof.T.(g.obl |> unwrap))
  in
  let open TL.Proof.T in
  match unwrap pf with
  | Omitted Implicit ->
      List.concat
        [
          [ ca_omitted ~uri ~ps; ca_to_steps ~uri ~ps ~cx ~pf ~depth ];
          cas_def_expand None;
        ]
  | Omitted Explicit | Omitted (Elsewhere _) ->
      List.concat
        [ [ ca_to_steps ~uri ~ps ~cx ~pf ~depth ]; cas_def_expand None ]
  | Steps ([], _) ->
      (* TODO: Drop one level. *)
      []
  | Steps (_, _) -> []
  | Obvious ->
      List.concat
        [ [ ca_to_steps ~uri ~ps ~cx ~pf ~depth ]; cas_def_expand None ]
  | By (usable, only) ->
      List.concat
        [
          [ ca_to_steps ~uri ~ps ~cx ~pf ~depth ];
          cas_def_expand (Some (usable, only));
        ]
  | Error _ -> []

(** Propose proof decomposition CodeActions by the structure of the goal and
    assumptions. *)
let cas_of_obl (uri : LspT.DocumentUri.t) (ps : PS.t) (ps_parent : PS.t)
    (o : TL.Proof.T.obligation) =
  let o = TL.Backend.Toolbox.normalize true o in
  Fmt.epr "XXX: goal=%a@." Debug.pp_expr o.obl.core.active;
  List.concat
    [
      Of_goal.code_actions uri ps ps_parent o.obl.core;
      Of_assm.code_actions uri ps ps_parent o.obl.core.context;
    ]

(* Code Actions of Proof Step *)
let cas_of_ps (uri : LspT.DocumentUri.t) (ps : PS.t) (ps_parent : PS.t) =
  let open TL.Proof.T in
  let el, cx = PS.el ps in
  (* Fmt.epr "@[XXX: cas_of_ps, ps.cx=%a@]@." Debug.pp_cx cx; *)
  let cas_of_el_with_pf = cas_of_el_with_pf uri ps cx in
  let step_no s =
    match TL.Property.get s TL.Proof.T.Props.step with
    | Named (depth, _, _) | Unnamed (depth, _) -> depth
  in
  match el with
  | PS.El.Mutate _ | PS.El.Module _ -> []
  | PS.El.Theorem { orig_pf; _ } -> cas_of_el_with_pf orig_pf 0
  | PS.El.Step step -> (
      let step_no = step_no step in
      match unwrap step with
      | Assert (_, pf)
      | Suffices (_, pf)
      | Pcase (_, pf)
      | Pick (_, _, pf)
      | PickTuply (_, _, pf) ->
          cas_of_el_with_pf pf step_no
      | Hide _ | Define _
      | Use (_, _)
      | Have _ | Take _ | TakeTuply _ | Witness _ | Forget _ ->
          [])
  | PS.El.Qed qed_step ->
      let step_no = step_no qed_step in
      let cas_of_goal =
        PS.goal ps
        |> Option.fold ~none:[] ~some:(fun g -> cas_of_obl uri ps ps_parent g)
      in
      let cas_of_pf =
        match unwrap qed_step with Qed pf -> cas_of_el_with_pf pf step_no
      in
      List.concat [ cas_of_goal; cas_of_pf ]

let code_actions (uri : LspT.DocumentUri.t) (mule_ps : PS.t) (range : Range.t) :
    LspT.CodeAction.t list =
  match PS.locate_proof_path mule_ps range with
  | ps :: parent :: _ -> cas_of_ps uri ps parent
  | _ :: _ -> [] (* Module is the root, no decompositions there. *)
  | [] -> [] (* Should not be possible. *)
