let max_size = 50 * 1024 * 1024
(* 50 MB should be enough. *)

type transport = Stdio | Socket of int

(** Passed to the IO codec to log the traffic, if needed. *)
let trace_fun trace direction =
  match (trace, direction) with
  | true, `Input -> fun str -> Eio.traceln "[I] %s" str
  | true, `Output -> fun str -> Eio.traceln "[O] %s" str
  | false, _ -> fun _ -> ()

(** Process an LSP packet stream. *)
let rec lsp_stream_handler input_chan output_chan =
  let open Tlapm_lsp_codec in
  let writer out_packet =
    let buf_w, _ = output_chan in
    match write output_chan out_packet with
    | Ok () -> Eio.Buf_write.flush buf_w
    | Error exn ->
        Eio.traceln "IO Error reading packet: %s" (Printexc.to_string exn)
  in
  match read input_chan with
  | Ok (Some packet) ->
      Tlapm_lsp_packets.handle_jsonrpc_packet packet writer;
      lsp_stream_handler input_chan output_chan
  | Ok None -> Eio.traceln "No packet was read."
  | Error exn ->
      Eio.traceln "IO Error reading packet: %s" (Printexc.to_string exn)

let err_handler = Eio.traceln "Error handling connection: %a" Fmt.exn

(** Configures the IO for the given input/output flows. *)
let flow_handler trace input_flow output_flow =
  let buf_r = Eio.Buf_read.of_flow input_flow ~max_size in
  let write_fun buf_w =
    let input_chan = (buf_r, trace_fun trace `Input) in
    let output_chan = (buf_w, trace_fun trace `Output) in
    lsp_stream_handler input_chan output_chan
  in
  Eio.Buf_write.with_flow output_flow write_fun

(** StdIO specifics. *)
module OnStdio = struct
  let run trace env =
    let switch_fun _sw =
      flow_handler trace (Eio.Stdenv.stdin env) (Eio.Stdenv.stdout env)
    in
    Eio.Switch.run switch_fun
end

(** Socket-specifics. *)
module OnSocket = struct
  let req_handler trace flow _addr =
    Eio.traceln "Server: got connection from client";
    flow_handler trace flow flow

  let switch (net : 'a Eio.Net.ty Eio.Std.r) port trace stop_promise sw =
    Eio.traceln "Socket switch started";
    let addr = `Tcp (Eio.Net.Ipaddr.V4.loopback, port) in
    let sock = Eio.Net.listen net ~sw ~reuse_addr:true ~backlog:5 addr in
    let stopResult =
      Eio.Net.run_server sock (req_handler trace) ~on_error:err_handler
        ?stop:(Some stop_promise)
    in
    Eio.traceln "StopResult=%s" stopResult

  let run port trace env stop_promise =
    let net = Eio.Stdenv.net env in
    Eio.Switch.run @@ switch net port trace stop_promise
end

(** Entry point. *)
let run transport trace env stop_promise =
  match transport with
  | Stdio -> OnStdio.run trace env
  | Socket port -> OnSocket.run port trace env stop_promise
