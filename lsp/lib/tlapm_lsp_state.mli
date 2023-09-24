(** State of a single session/connection with the LSP client. *)

type t

val empty : t
val ready : t -> t
val shutdown : t -> t

val handle_if_ready :
  t -> (Tlapm_lsp_docs.t -> Tlapm_lsp_docs.t) -> (t, string) result

val handle_if_ready_silent : t -> (Tlapm_lsp_docs.t -> Tlapm_lsp_docs.t) -> t
