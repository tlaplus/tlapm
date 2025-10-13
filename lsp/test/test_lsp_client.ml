type t = {
  pid : int;
  stdin : out_channel;
  stdout : in_channel;
  stderr : in_channel;
  mutable id_seq : Jsonrpc.Id.t Seq.t;
}

module LspIoState = struct
  type 'a t = ('a, exn) result

  let return x = Ok x
  let raise exn = Error exn

  module O = struct
    let ( let+ ) st f = Result.map f st
    let ( let* ) st f = Result.bind st f
  end
end

module LspIoChan = struct
  type input = in_channel
  type output = out_channel

  let read_line (i : input) : string option LspIoState.t =
    let line = input_line i in
    Ok (Some line)

  let read_exactly (i : input) (n : int) : string option LspIoState.t =
    let data = In_channel.really_input_string i n in
    Ok data

  let write (o : output) (lines : string list) : unit LspIoState.t =
    lines |> List.iter (Out_channel.output_string o);
    Out_channel.flush o;
    Ok ()
end

module LspIo = Lsp.Io.Make (LspIoState) (LspIoChan)

let run cmd : t =
  let stdin_r, stdin_w = Unix.pipe () in
  let stdout_r, stdout_w = Unix.pipe () in
  let stderr_r, stderr_w = Unix.pipe () in
  let pid =
    Unix.create_process cmd
      [| cmd; "--stdio"; "--log-io"; "--log-to=test_lsp_client.log" |]
      stdin_r stdout_w stderr_w
  in
  {
    pid;
    stdin = Unix.out_channel_of_descr stdin_w;
    stdout = Unix.in_channel_of_descr stdout_r;
    stderr = Unix.in_channel_of_descr stderr_r;
    id_seq = Seq.ints 1 |> Seq.map (fun i -> `Int i);
  }

let close (t : t) : unit =
  In_channel.close t.stdout;
  Out_channel.close t.stdin;
  In_channel.close t.stdout;
  In_channel.close t.stderr;
  Unix.kill t.pid Sys.sigint;
  ()

let next_id (t : t) : Jsonrpc.Id.t =
  let id, seq = Seq.uncons t.id_seq |> Option.get in
  t.id_seq <- seq;
  id

let pp_packet fmt (p : Jsonrpc.Packet.t) : unit =
  Yojson.Safe.pretty_print fmt (Jsonrpc.Packet.yojson_of_t p)

let send_packet (t : t) (p : Jsonrpc.Packet.t) : unit =
  match LspIo.write t.stdin p with Ok () -> () | Error exn -> raise exn

let send_request (t : t) req =
  let id = next_id t in
  let json_request = Lsp.Client_request.to_jsonrpc_request ~id req in
  let json_packet = Jsonrpc.Packet.Request json_request in
  send_packet t json_packet;
  id

let send_notification t n =
  let json_notif = Lsp.Client_notification.to_jsonrpc n in
  let json_packet = Jsonrpc.Packet.Notification json_notif in
  send_packet t json_packet

let recv_packet (t : t) : Jsonrpc.Packet.t option =
  match LspIo.read t.stdout with Ok data -> data | Error exn -> raise exn

let rec recv_response ?(log : bool = true) t id =
  match recv_packet t with
  | None -> assert false
  | Some p -> (
      if log then Fmt.epr "Packet received: %a@." pp_packet p;
      match p with
      | Response { id = resp_id; result } when resp_id = id ->
          result |> Result.get_ok
      | _ -> recv_response t id)

let call t r = send_request t r |> recv_response t

let call_init t =
  Lsp.Client_request.Initialize
    Lsp.Types.InitializeParams.
      {
        processId = Some 42;
        capabilities =
          Lsp.Types.ClientCapabilities.
            {
              workspace = None;
              experimental = None;
              window = None;
              textDocument = None;
              notebookDocument = None;
              general = None;
            };
        clientInfo = None;
        locale = None;
        rootPath = None;
        rootUri = None;
        initializationOptions = None;
        trace = None;
        workDoneToken = None;
        workspaceFolders = None;
      }
  |> call t |> Lsp.Types.InitializeResult.t_of_yojson

let print_stderr (t : t) : unit =
  (* Fmt.epr "%s@." (In_channel.input_all t.stderr) *)
  match In_channel.input_line t.stderr with
  | None -> ()
  | Some line -> Fmt.epr "%s@." line
