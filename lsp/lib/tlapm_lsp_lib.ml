
module type EioLspParser = sig
  type 'a io_res =
  | IoOk of 'a
  | IoErr of exn

  val read : Eio.Buf_read.t -> Jsonrpc.Packet.t option io_res
  val write : Eio.Buf_write.t -> Jsonrpc.Packet.t -> unit io_res
end

(** Here we construct an LSP protocol parser on top of Eio flows. *)
module EioLspParser : EioLspParser = struct
  type 'a io_res =
  | IoOk of 'a
  | IoErr of exn

  module IoState = struct
    type 'a t = 'a io_res
    let return x = IoOk x
    let raise exn = IoErr exn
    module O = struct
      let ( let+ ) st f =
        match st with
        | IoOk a -> IoOk (f a)
        | IoErr exn -> IoErr exn
      let ( let* ) st f =
        match st with
        | IoOk a -> f a
        | IoErr exn -> IoErr exn
    end
  end

  module IoChan = struct
    type output = Eio.Buf_write.t
    type input = Eio.Buf_read.t
    let read_line (buf : input): string option IoState.t =
      let line = Eio.Buf_read.line buf in
      IoOk (Some line)
    let read_exactly (buf : input) (n : int) : string option IoState.t =
      let data = Eio.Buf_read.take n buf in
      IoOk (Some data)
    let rec write (buf : output) (lines : string list) : unit IoState.t =
      match lines with
        | [] ->
          IoOk ()
        | line :: tail ->
          let () = Eio.Buf_write.string buf line in
          write buf tail
  end

  module LspIo = Lsp.Io.Make (IoState) (IoChan)

  let read = LspIo.read
  let write = LspIo.write
end
