(** Here we have all the TLAPM specific LSP action handlers. *)

module LspT := Lsp.Types

module type Callbacks = sig
  type t

  val ready : t -> t
  val shutdown : t -> t
  val lsp_send : t -> Jsonrpc.Packet.t -> t
  val with_docs : t -> (t * Docs.t -> t * Docs.t) -> t
  val prove_step : t -> LspT.DocumentUri.t -> int -> LspT.Range.t -> t
  val cancel : t -> LspT.ProgressToken.t -> t

  val suggest_proof_range :
    t -> LspT.DocumentUri.t -> LspT.Range.t -> t * (int * LspT.Range.t) option

  val track_obligation_proof_state :
    t -> LspT.DocumentUri.t -> LspT.Range.t -> t
  (** User selected a position in a document, we have to provide the
      obligation info for it. The information has to be re-sent on update. *)

  val latest_diagnostics :
    t -> LspT.DocumentUri.t -> t * (int * LspT.Diagnostic.t list)

  val diagnostic_source : string
end

module Make (CB : Callbacks) : sig
  val handle_jsonrpc_packet : Jsonrpc.Packet.t -> CB.t -> CB.t
end
