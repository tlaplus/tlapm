(**
Here we construct a decoder/encoder for the LSP protocol on top of Eio flows.
We use the lsp module from the ocaml-lsp server and configure it to run over Eio.
*)

val read : Eio.Buf_read.t -> (Jsonrpc.Packet.t option, exn) result
val write : Eio.Buf_write.t -> Jsonrpc.Packet.t -> (unit, exn) result
