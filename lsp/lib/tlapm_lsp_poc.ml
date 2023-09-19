
let _ = Lsp.Cli.args

(* ================================= START Of Experiment on LSP IO ===================== *)

module MyInitialPoC = struct
  type myIoCh = string

  module MyIo = struct
    type 'a t = myIoCh
    let return = failwith "todo"
    let raise = failwith "todo"
    module O = struct
      let ( let+ ) _a _b = failwith "todo"
      let ( let* ) _a _b = failwith "todo"
    end
  end

  module MyChan = struct
    type output = myIoCh
    type input = myIoCh
    let read_line : input -> string option MyIo.t =
      failwith "todo"
    let read_exactly : input -> int -> string option MyIo.t =
      failwith "todo"
    let write : output -> string list -> unit MyIo.t =
      failwith "todo"
  end

  module MyLspIo = Lsp.Io.Make (MyIo) (MyChan)

  let _r = MyLspIo.read "myIoCh"
  let _w p = MyLspIo.write "myIoCh" p

end


let _myTextDocument =
  let tdi = Lsp.Types.TextDocumentItem.create ~languageId:"lang" ~text:"text" ~uri:(Lsp.Uri.of_path "...........") ~version:12 in
  let p = Lsp.Types.DidOpenTextDocumentParams.create ~textDocument:tdi in
  Lsp.Text_document.make ~position_encoding:`UTF8 p



(* ================================= END Of Experiment on LSP ===================== *)

module MyFibExperiment = struct

  module MyIo = struct
    include Fiber
    let raise exn = raise exn
  end

  module MyChan = struct
    type input = string Queue.t
    type output = string Queue.t

    let read_line (_ic : input) : string option MyIo.t = failwith "todo"
      (* let+ res = Lio.Reader.read_line ic in
      match res with
      | Ok s -> Some s
      | Error (`Partial_eof _) -> None *)

    let read_exactly (_ic : input) (_len : int) : string option MyIo.t = failwith "todo"
      (* let+ res = Lio.Reader.read_exactly ic len in
      match res with
      | Ok s -> Some s
      | Error (`Partial_eof _) -> None *)

    let write (_oc : output) (_strings : string list) : unit MyIo.t = failwith "todo"
      (* Fiber.of_thunk (fun () ->
          List.iter strings ~f:(Lio.Writer.add_string oc);
          Fiber.return ()) *)

  end

  module MyLspIo = Lsp.Io.Make (MyIo) (MyChan)

  (** State of the IO consists of input and output queues. *)
  type t = {
    ic : string Queue.t;
    oc : string Queue.t;
  }

  (** Here we have read/write functions, they should be called by the environment, I guess. *)
  let _r {ic; _} = MyLspIo.read ic
  let _w {oc; _} p = MyLspIo.write oc p

end




(* module Channel = struct
  type t =
    | Stdio
    | Pipe of string
    | Socket of int
end *)

(* let stream_of_channel : Lsp.Cli.Channel.t -> _ = function
  | Stdio ->
    let* stdin = Fiber.O.Stdin in
    let+ stdout = Fiber.O.Stdout in
    (stdin, stdout)
  | Pipe path ->
    if Sys.win32 then (
      Format.eprintf "windows pipes are not supported";
      exit 1)
    else
      let _sockaddr = Unix.ADDR_UNIX path in
      (Fiber.O.Stdin, Fiber.O.Stdout)
  | Socket port ->
    let _sockaddr = Unix.ADDR_INET (Unix.inet_addr_loopback, port) in
    (Fiber.O.Stdin, Fiber.O.Stdout) *)

(* let stream_of_channel : Lsp.Cli.Channel.t -> _ = function
  | Stdio ->
    let* stdin = Lev_fiber.Io.stdin in
    let+ stdout = Lev_fiber.Io.stdout in
    (stdin, stdout)
  | Pipe path ->
    if Sys.win32 then (
      Format.eprintf "windows pipes are not supported";
      exit 1)
    else
      let sockaddr = Unix.ADDR_UNIX path in
      socket sockaddr
  | Socket port ->
    let sockaddr = Unix.ADDR_INET (Unix.inet_addr_loopback, port) in
    socket sockaddr *)

