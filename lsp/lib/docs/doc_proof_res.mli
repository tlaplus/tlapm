(** Proof results of a document. Includes the errors returned from the prover
    as well as all the proof steps with their current state.
    *)

open Util

type t

val make :
  int -> Prover.ToolboxProtocol.tlapm_notif list -> Proof_step.t option -> t

val empty : t

val as_lsp :
  t -> LspT.Diagnostic.t list * Structs.TlapsProofStateMarker.t list

(* TODO: The following should be removed when the progress reporting is reorganized. *)
val p_ref : t -> int
val obs_done : t -> int
