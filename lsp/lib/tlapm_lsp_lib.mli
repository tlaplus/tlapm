module type EioLspParser = sig
  type 'a io_res =
  | IoOk of 'a
  | IoErr of exn

  val read : Eio.Buf_read.t -> Jsonrpc.Packet.t option io_res
  val write : Eio.Buf_write.t -> Jsonrpc.Packet.t -> unit io_res
end

module EioLspParser : EioLspParser
