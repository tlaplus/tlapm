(** Here we have all the TLAPM specific LSP action handlers. *)

val handle_jsonrpc_packet :
  Jsonrpc.Packet.t -> (Jsonrpc.Packet.t -> unit) -> unit
