module Tlapm_lsp_lib = Tlapm_lsp_lib

module LspServer = struct

  let lsp_packet_handler (packet : Jsonrpc.Packet.t) write_fun =
    Eio.traceln "Got LSP Packet";
    write_fun packet (* // TODO: That's just echo. *)

  let rec lsp_stream_handler buf_r buf_w =
    let open Tlapm_lsp_lib.EioLspParser in
    let write_fun out_packet =
      match write buf_w out_packet with
      | IoOk () ->
        Eio.Buf_write.flush buf_w
      | IoErr exn ->
        Eio.traceln "IO Error reading packet: %s" (Printexc.to_string exn)
      in
    match read buf_r with
      | IoOk (Some packet) ->
        lsp_packet_handler packet write_fun;
        lsp_stream_handler buf_r buf_w
      | IoOk None ->
        Eio.traceln "No packet was read."
      | IoErr exn ->
        Eio.traceln "IO Error reading packet: %s" (Printexc.to_string exn)


  let err_handler =
    Eio.traceln "Error handling connection: %a" Fmt.exn

  let req_handler flow _addr =
    Eio.traceln "Server: got connection from client";
    let buf_r = Eio.Buf_read.of_flow flow ~max_size:1024 in
    Eio.Buf_write.with_flow flow @@ fun buf_w ->
      lsp_stream_handler buf_r buf_w

  let switch (net: 'a Eio.Net.ty Eio.Std.r) port stop_promise sw =
    Eio.traceln "Switch started";
    let addr = (`Tcp (Eio.Net.Ipaddr.V4.loopback, port)) in
    let sock = Eio.Net.listen net ~sw ~reuse_addr:true ~backlog:5 addr in
    let stopResult = Eio.Net.run_server sock req_handler ~on_error:err_handler ?stop:(Some stop_promise) in
    Eio.traceln "StopResult=%s" stopResult

  let run env stop_promise =
    let net = (Eio.Stdenv.net env) in
    let port = 8080 in
    Eio.Switch.run @@ switch net port stop_promise

end

let () =
  Eio_main.run @@ fun env ->
    let (stop_promise, stop_resolver) = Eio.Std.Promise.create () in
    let handle_signal (_signum : int) = Eio.Std.Promise.resolve stop_resolver "Stopping on SigINT" in
    let () = Sys.set_signal Sys.sigint (Signal_handle handle_signal) in
    LspServer.run env stop_promise
