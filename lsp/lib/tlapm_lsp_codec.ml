module IoState = struct
  type 'a t = ('a, exn) result

  let return x = Ok x
  let raise exn = Error exn

  module O = struct
    let ( let+ ) st f = Result.map f st
    let ( let* ) st f = Result.bind st f
  end
end

module IoChan = struct
  type output = Eio.Buf_write.t
  type input = Eio.Buf_read.t

  let read_line (buf : input) : string option IoState.t =
    let line = Eio.Buf_read.line buf in
    Ok (Some line)

  let read_exactly (buf : input) (n : int) : string option IoState.t =
    let data = Eio.Buf_read.take n buf in
    Ok (Some data)

  let rec write (buf : output) (lines : string list) : unit IoState.t =
    match lines with
    | [] -> Ok ()
    | line :: tail ->
        let () = Eio.Buf_write.string buf line in
        write buf tail
end

module LspIo = Lsp.Io.Make (IoState) (IoChan)

let read = LspIo.read
let write = LspIo.write
