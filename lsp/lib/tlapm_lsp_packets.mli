(** Here we have all the TLAPM specific LSP action handlers. *)

val handle_jsonrpc_packet :
  Jsonrpc.Packet.t ->
  (Jsonrpc.Packet.t -> unit) ->
  Tlapm_lsp_state.t ->
  Tlapm_lsp_state.t
