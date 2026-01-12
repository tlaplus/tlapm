(* cspell:words Actplus Cdot Deque Disj Forall Gteq Leadsto Lteq Notmem Setminus Tquant unditto *)
(* cspell:words Tquant Tsub Uminus Unprimable noprops stepno uncons Bpragma Defn  Dvar  assm  filteri *)
open Util

(** Replace
    {v <1> ... v}
    with
    {v <1> ... OBVIOUS v} *)
let ca_omitted ~uri ~ps =
  let title = "⤮ Prove as OBVIOUS" in
  let range = PS.head_range ps |> Range.make_after in
  let newText = " OBVIOUS" in
  ca_edit ~uri ~title ~range ~newText

(** Replace
    {v
      <1> ... [proof]
    v}
    with
    {v
      <1> ...
        <2>1. QED [proof]
    v} *)
let ca_to_steps ~uri ~(ps : PS.t) ~cx =
  let open TL in
  let step_names = Seq_acc.make (PS.stepno_seq_under_proof_step ps) in
  let ps_proof = PS.proof ps |> Option.get in
  let sub_steps =
    let qed_sn = Seq_acc.take step_names in
    let qed = Proof.T.Qed ps_proof |> noprops |> with_stepno qed_sn in
    Proof.T.(Steps ([], qed)) |> noprops
  in
  let ps_proof_rewrite = ps_proof_rewrite ps cx (`Proof sub_steps) in
  let title = "⤮ To sub-steps" in
  ca_edits ~uri ~title ~edits:[ ps_proof_rewrite ]

(* Propose code actions for AST nodes containing proofs. *)
let cas_of_el_with_pf (uri : LspT.DocumentUri.t) (ps : PS.t)
    (cx : TL.Expr.T.ctx) (pf : TL.Proof.T.proof) =
  let cas_def_expand (by : (TL.Proof.T.usable * bool) option) =
    let by =
      Option.value ~default:(TL.Proof.T.{ facts = []; defs = [] }, false) by
    in
    PS.goal ps
    |> Option.fold ~none:[] ~some:(fun g ->
        Of_defs.cas_def_expand ~uri ~ps ~cx ~by ~sq:TL.Proof.T.(g.obl |> unwrap))
  in
  let open TL.Proof.T in
  match unwrap pf with
  | Omitted Implicit ->
      List.concat
        [
          [ ca_omitted ~uri ~ps; ca_to_steps ~uri ~ps ~cx ]; cas_def_expand None;
        ]
  | Omitted Explicit | Omitted (Elsewhere _) ->
      List.concat [ [ ca_to_steps ~uri ~ps ~cx ]; cas_def_expand None ]
  | Steps ([], _) ->
      (* TODO: Drop one level. *)
      []
  | Steps (_, _) -> []
  | Obvious -> List.concat [ [ ca_to_steps ~uri ~ps ~cx ]; cas_def_expand None ]
  | By (usable, only) ->
      List.concat
        [ [ ca_to_steps ~uri ~ps ~cx ]; cas_def_expand (Some (usable, only)) ]
  | Error _ -> []

(** Propose proof decomposition CodeActions by the structure of the goal and
    assumptions. *)
let cas_of_obl (uri : LspT.DocumentUri.t) (ps : PS.t) (ps_parent : PS.t)
    (o : TL.Proof.T.obligation) =
  let o = TL.Backend.Toolbox.normalize true o in
  List.concat
    [
      Of_goal.code_actions uri ps ps_parent o.obl.core;
      Of_assm.code_actions uri ps ps_parent o.obl.core.context;
    ]

(* Code Actions of Proof Step *)
let cas_of_ps (uri : LspT.DocumentUri.t) (ps : PS.t) (ps_parent : PS.t) =
  let open TL.Proof.T in
  let el, cx = PS.el ps in
  let cas_of_el_with_pf = cas_of_el_with_pf uri ps cx in
  match el with
  | PS.El.Mutate _ | PS.El.Module _ -> []
  | PS.El.Theorem { orig_pf; _ } -> cas_of_el_with_pf orig_pf
  | PS.El.Step step -> (
      match unwrap step with
      | Assert (_, pf)
      | Suffices (_, pf)
      | Pcase (_, pf)
      | Pick (_, _, pf)
      | PickTuply (_, _, pf) ->
          cas_of_el_with_pf pf
      | Hide _ | Define _
      | Use (_, _)
      | Have _ | Take _ | TakeTuply _ | Witness _ | Forget _ ->
          [])
  | PS.El.Qed qed_step ->
      let cas_of_goal =
        PS.goal ps
        |> Option.fold ~none:[] ~some:(fun g -> cas_of_obl uri ps ps_parent g)
      in
      let cas_of_pf =
        match unwrap qed_step with Qed pf -> cas_of_el_with_pf pf
      in
      List.concat [ cas_of_goal; cas_of_pf ]

let code_actions (uri : LspT.DocumentUri.t) (mule_ps : PS.t) (range : Range.t) :
    LspT.CodeAction.t list =
  match PS.locate_proof_path mule_ps range with
  | ps :: parent :: _ -> cas_of_ps uri ps parent
  | _ :: _ -> [] (* Module is the root, no decompositions there. *)
  | [] -> [] (* Should not be possible. *)
