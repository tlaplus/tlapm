module Tlapm_lsp_lib = Tlapm_lsp_lib

module LspServer = struct

  let err_handler =
    Eio.traceln "Error handling connection: %a" Fmt.exn

  let req_handler flow _addr =
    Eio.traceln "Server: got connection from client";
    let x = Eio.Buf_read.of_flow flow ~max_size:100 in
    let ml = Eio.Buf_read.line x in
    let mf = Eio.Buf_read.take 10 x in
    Eio.Flow.copy_string (Printf.sprintf "Hello from server: line=%s - fixed(10)=%S\n" ml mf) flow

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
