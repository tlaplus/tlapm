open Util
open Prover

module Role : sig
  type t = Main of bool | Aux | Unknown | Unexpected
end

type t

val of_parsed_obligation : Tlapm_lib.Proof.T.obligation -> t
val with_prover_terminated : int -> t -> t
val with_prover_obligation : int -> Toolbox.Obligation.t -> t option -> t
val with_proof_state_from : (string -> t option) -> t -> t
val with_prover_names : int -> int -> string list -> t -> t
val parsed : t -> Tlapm_lib.Proof.T.obligation option
val parsed_main : t -> Tlapm_lib.Proof.T.obligation option
val role : t -> Role.t
val loc : t -> Range.t
val fingerprint : t -> string option
val status : t -> Proof_status.t
val is_for_obl_id : t -> int -> int -> bool
val is_final : t -> bool
val text_plain : t -> string option
val text_normalized : t -> string option
val latest_status_msg : t -> string
val latest_obl_text : t -> string option

val as_lsp_diagnostic : t -> LspT.Diagnostic.t option
(** Convert to the LSP data structures. *)

val as_lsp_tlaps_proof_obligation_state :
  t -> Structs.TlapsProofObligationState.t
(** Convert to the LSP data structures. *)
