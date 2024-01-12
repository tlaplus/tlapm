(** Proof step, as it is displayed in the editor.
    The proof steps are obtained by parsing the the TLAPS source file.
    Later the proof obligation info is added to the tree as they are
    obtained from the prover.
    *)

open Util
open Tlapm_lsp_prover

type t

val of_module : Tlapm_lib.Module.T.mule -> t list
val with_tlapm_obligation : t list -> Obl_info.t -> t list
val with_tlapm_obligations : t list -> Obl_info.t OblMap.t -> t list
val locate_proof_range : t list -> TlapmRange.t -> TlapmRange.t
val find_proof_step : t list -> TlapmRange.t -> t option
val flatten : t list -> t list
val yojson_of_t : t -> Yojson.Safe.t option

val tlaps_proof_obligation_state_of_t :
  LspT.DocumentUri.t ->
  t ->
  Tlapm_lsp_structs.TlapsProofObligationState.t option
