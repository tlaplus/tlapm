(** Here we have all the TLAPM specific LSP action handlers. *)

module Docs = Tlapm_lsp_docs
module LT = Lsp.Types

module type Callbacks = sig
  type cb_t

  val ready : cb_t -> cb_t
  val shutdown : cb_t -> cb_t
  val lsp_send : cb_t -> Jsonrpc.Packet.t -> cb_t
  val with_docs : cb_t -> (cb_t * Docs.t -> cb_t * Docs.t) -> cb_t
  val prove_step : cb_t -> LT.DocumentUri.t -> int -> LT.Range.t -> cb_t

  val latest_diagnostics :
    cb_t -> LT.DocumentUri.t -> cb_t * (int * LT.Diagnostic.t list)

  val diagnostic_source : string
end

module Make (CB : Callbacks) : sig
  val handle_jsonrpc_packet : Jsonrpc.Packet.t -> CB.cb_t -> CB.cb_t
end
