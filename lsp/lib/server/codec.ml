type trace_fun = string -> unit
type input_chan = Eio.Buf_read.t * trace_fun
type output_chan = Eio.Buf_write.t * trace_fun

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
  type input = input_chan
  type output = output_chan

  let read_line ((buf, trace) : input) : string option IoState.t =
    let line = Eio.Buf_read.line buf in
    let () = trace line in
    Ok (Some line)

  let read_exactly ((buf, trace) : input) (n : int) : string option IoState.t =
    let data = Eio.Buf_read.take n buf in
    let () = trace data in
    Ok (Some data)

  let rec write ((buf, trace) : output) (lines : string list) : unit IoState.t =
    match lines with
    | [] -> Ok ()
    | line :: tail ->
        let () = trace line in
        let () = Eio.Buf_write.string buf line in
        write (buf, trace) tail
end

module LspIo = Lsp.Io.Make (IoState) (IoChan)

let read = LspIo.read
let write = LspIo.write
