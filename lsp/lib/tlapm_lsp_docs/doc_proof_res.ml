open Tlapm_lsp_prover
open Util

type t = {
  p_ref : int;
  nts : ToolboxProtocol.tlapm_notif list;
  ps : Proof_step.t option;
}

let make p_ref nts ps = { p_ref; nts; ps }
let empty = { p_ref = 0; nts = []; ps = None }

(* Return decorator markers and diagnostics. *)
let as_lsp pr =
  (* Collect the diagnostics and decorator markers from the proof steps. *)
  let diags, marks =
    Proof_step.fold
      (fun (diags, marks) ps ->
        let mark = Proof_step.as_lsp_tlaps_proof_state_marker ps in
        let marks = mark :: marks in
        Proof_step.fold_obs
          (fun (diags, marks) obl ->
            match Obl.as_lsp_diagnostic obl with
            | None -> (diags, marks)
            | Some diag -> (diag :: diags, marks))
          (diags, marks) ps)
      ([], []) pr.ps
  in
  (* Also add the diagnostics from the notifications. *)
  let notif_diags =
    List.map
      (fun (ntf : ToolboxProtocol.tlapm_notif) ->
        let open Tlapm_lsp_prover in
        let severity =
          match ntf.sev with
          | TlapmNotifError -> LspT.DiagnosticSeverity.Error
          | TlapmNotifWarning -> LspT.DiagnosticSeverity.Warning
        in
        LspT.Diagnostic.create ~message:ntf.msg
          ~range:(TlapmRange.as_lsp_range ntf.loc)
          ~severity ~source:Const.diagnostic_source ())
      pr.nts
  in
  (List.concat [ diags; notif_diags ], marks)

let p_ref pr = pr.p_ref

let obs_done pr =
  Proof_step.fold
    (fun acc ps ->
      Proof_step.fold_obs
        (fun acc obl ->
          match Obl.is_state_terminal_in_p_ref pr.p_ref obl with
          | true -> acc + 1
          | false -> acc)
        acc ps)
    0 pr.ps
