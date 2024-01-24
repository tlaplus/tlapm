(** Proof results of a document. Includes the errors returned from the prover
    as well as all the proof steps with their current state.
    *)

open Util
open Prover

type t

val make : Toolbox.tlapm_notif list -> Proof_step.t option -> t
val empty : t
val as_lsp : t -> LspT.Diagnostic.t list * Structs.TlapsProofStateMarker.t list
