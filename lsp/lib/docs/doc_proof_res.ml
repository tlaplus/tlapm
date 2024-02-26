open Prover
open Util

type t = { nts : Toolbox.tlapm_notif list; ps : Proof_step.t option }

let make nts ps = { nts; ps }
let empty = { nts = []; ps = None }

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
      (fun (ntf : Toolbox.tlapm_notif) ->
        let severity =
          match ntf.sev with
          | TlapmNotifError -> LspT.DiagnosticSeverity.Error
          | TlapmNotifWarning -> LspT.DiagnosticSeverity.Warning
        in
        LspT.Diagnostic.create ~message:ntf.msg
          ~range:(Range.as_lsp_range ntf.loc)
          ~severity ~source:Const.diagnostic_source ())
      pr.nts
  in
  (List.concat [ diags; notif_diags ], marks)
