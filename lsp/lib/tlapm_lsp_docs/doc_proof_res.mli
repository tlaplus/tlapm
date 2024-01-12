(** Proof results of a document. Includes the errors returned from the prover
    as well as all the proof steps with their current state.
    *)

open Tlapm_lsp_prover.ToolboxProtocol

type t = {
  p_ref : int;
  obs : tlapm_obligation list;
  nts : tlapm_notif list;
  pss : Proof_step.t list;
}

val empty : t
val obs_done : t -> int
