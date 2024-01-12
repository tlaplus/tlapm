open Tlapm_lsp_prover

type t = {
  p_ref : int;
  obs : ToolboxProtocol.tlapm_obligation list;
  nts : ToolboxProtocol.tlapm_notif list;
  pss : Proof_step.t list;
}

let empty = { p_ref = 0; obs = []; nts = []; pss = [] }

let obs_done t =
  let open Tlapm_lsp_prover.ToolboxProtocol in
  List.fold_left
    (fun acc ob ->
      if tlapm_obl_state_is_terminal ob.status then acc + 1 else acc)
    0 t.obs
