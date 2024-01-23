(** State of a single session/connection with the LSP client. *)

module LspT := Lsp.Types

type doc_ref = LspT.DocumentUri.t * int * int

type events =
  | LspEOF
  | LspPacket of Jsonrpc.Packet.t
  | TlapmEvent of doc_ref * Prover.ToolboxProtocol.tlapm_msg
  | TimerTick

val run :
  (unit -> events) ->
  (events -> unit) ->
  (Jsonrpc.Packet.t option -> unit) ->
  Eio.Switch.t ->
  Eio__.Fs.dir_ty Eio.Path.t ->
  Eio_unix.Process.mgr_ty Eio.Process.mgr ->
  unit
