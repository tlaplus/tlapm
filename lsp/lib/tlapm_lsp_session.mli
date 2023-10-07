(** State of a single session/connection with the LSP client. *)

type events =
  | LspEOF
  | LspPacket of Jsonrpc.Packet.t
  | TlapmEvent of int * Tlapm_lsp_prover.ToolboxProtocol.tlapm_msg

val run : (unit -> events) -> (Jsonrpc.Packet.t option -> unit) -> unit
