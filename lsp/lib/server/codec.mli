(**
Here we construct a decoder/encoder for the LSP protocol on top of Eio flows.
We use the lsp module from the ocaml-lsp server and configure it to run over Eio.
*)

type trace_fun = string -> unit
type input_chan = Eio.Buf_read.t * trace_fun
type output_chan = Eio.Buf_write.t * trace_fun

val read : input_chan -> (Jsonrpc.Packet.t option, exn) result
val write : output_chan -> Jsonrpc.Packet.t -> (unit, exn) result
