(** State of a single session/connection with the LSP client. *)

type doc_ref = Lsp.Types.DocumentUri.t * int * int

type events =
  | LspEOF
  | LspPacket of Jsonrpc.Packet.t
  | TlapmEvent of doc_ref * Tlapm_lsp_prover.ToolboxProtocol.tlapm_msg
  | TimerTick

val run :
  (unit -> events) ->
  (events -> unit) ->
  (Jsonrpc.Packet.t option -> unit) ->
  Eio.Switch.t ->
  Eio__.Fs.dir_ty Eio.Path.t ->
  Eio_unix.Process.mgr_ty Eio.Process.mgr ->
  unit
