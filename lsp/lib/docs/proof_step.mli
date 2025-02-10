(** Proof step, as it is displayed in the editor. The proof steps are obtained
    by parsing the TLAPS source file. Later the proof obligation info is added
    to the tree as they are obtained from the prover. *)

open Util
open Prover

type t

val of_module : Tlapm_lib.Module.T.mule -> t option -> t option
val with_prover_terminated : t option -> int -> t option
val with_prover_result : t option -> int -> Toolbox.Obligation.t -> t option
val with_provers : t option -> int -> int -> string list -> t option
val locate_proof_step : t option -> Range.Position.t -> t option
val locate_proof_range : t option -> Range.t -> Range.t
val is_obl_final : t option -> int -> int -> bool option
val flatten : t option -> t list
val fold : ('a -> t -> 'a) -> 'a -> t option -> 'a
val fold_obs : ('a -> Obl.t -> 'a) -> 'a -> t -> 'a
val as_lsp_tlaps_proof_state_marker : t -> Structs.TlapsProofStepMarker.t

val as_lsp_tlaps_proof_step_details :
  LspT.DocumentUri.t -> t -> Structs.TlapsProofStepDetails.t
