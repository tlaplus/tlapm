(** Here we have all the TLAPM specific LSP action handlers. *)

module Docs = Tlapm_lsp_docs

module type Callbacks = sig
  type cb_t

  val ready : cb_t -> cb_t
  val shutdown : cb_t -> cb_t
  val with_docs : cb_t -> (Docs.t -> Docs.t) -> cb_t
end

module Make (CB : Callbacks) : sig
  val handle_jsonrpc_packet :
    Jsonrpc.Packet.t -> (Jsonrpc.Packet.t -> unit) -> CB.cb_t -> CB.cb_t
end
