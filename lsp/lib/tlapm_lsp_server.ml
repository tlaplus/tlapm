let max_size = 50 * 1024 * 1024
(* 50 MB should be enough. *)

type transport = Stdio | Socket of int

let rec lsp_stream_handler buf_r buf_w =
  let open Tlapm_lsp_codec in
  let writer out_packet =
    match write buf_w out_packet with
    | Ok () -> Eio.Buf_write.flush buf_w
    | Error exn ->
        Eio.traceln "IO Error reading packet: %s" (Printexc.to_string exn)
  in
  match read buf_r with
  | Ok (Some packet) ->
      Tlapm_lsp_packets.handle_jsonrpc_packet packet writer;
      lsp_stream_handler buf_r buf_w
  | Ok None -> Eio.traceln "No packet was read."
  | Error exn ->
      Eio.traceln "IO Error reading packet: %s" (Printexc.to_string exn)

let err_handler = Eio.traceln "Error handling connection: %a" Fmt.exn

let req_handler flow _addr =
  Eio.traceln "Server: got connection from client";
  let buf_r = Eio.Buf_read.of_flow flow ~max_size in
  Eio.Buf_write.with_flow flow @@ fun buf_w -> lsp_stream_handler buf_r buf_w

let switch (net : 'a Eio.Net.ty Eio.Std.r) port stop_promise sw =
  Eio.traceln "Switch started";
  let addr = `Tcp (Eio.Net.Ipaddr.V4.loopback, port) in
  let sock = Eio.Net.listen net ~sw ~reuse_addr:true ~backlog:5 addr in
  let stopResult =
    Eio.Net.run_server sock req_handler ~on_error:err_handler
      ?stop:(Some stop_promise)
  in
  Eio.traceln "StopResult=%s" stopResult

let run_on_stdio env =
  let switch_fun _sw =
    let buf_r = Eio.Buf_read.of_flow (Eio.Stdenv.stdin env) ~max_size in
    Eio.Buf_write.with_flow (Eio.Stdenv.stdout env) (lsp_stream_handler buf_r)
  in
  Eio.Switch.run switch_fun

let run_on_socket port env stop_promise =
  let net = Eio.Stdenv.net env in
  Eio.Switch.run @@ switch net port stop_promise

let run transport env stop_promise =
  match transport with
  | Stdio -> run_on_stdio env
  | Socket port -> run_on_socket port env stop_promise
