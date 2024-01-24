open Util

module Role : sig
  type t = Main | Aux | Unknown | Unexpected
end

type t

val of_parsed_obligation :
  Tlapm_lib.Proof.T.obligation option -> Proof_status.t -> t

val with_role : Role.t -> t -> t

val with_prover_obligation :
  int -> Prover.Toolbox.tlapm_obligation -> t option -> t

val with_proof_state_from : t -> (string -> t option) -> t
val role : t -> Role.t
val loc : t -> Range.t
val fingerprint : t -> string option
val status : t -> Proof_status.t
val text_plain : t -> string option
val text_normalized : t -> string option
val latest_status_msg : t -> string
val latest_obl_text : t -> string option

val as_lsp_diagnostic : t -> LspT.Diagnostic.t option
(** Convert to the LSP data structures. *)

val as_lsp_tlaps_proof_obligation_state :
  t -> Structs.TlapsProofObligationState.t
(** Convert to the LSP data structures. *)

(* TODO: Remove afer progress reworked. *)
val is_state_terminal_in_p_ref : int -> t -> bool
