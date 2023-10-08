(* cSpell:words Printexc Ipaddr *)

let max_size = 50 * 1024 * 1024
(* 50 MB should be enough. *)

type transport = Stdio | Socket of int

(** Passed to the IO codec to log the traffic, if needed. *)
let trace_fun trace direction =
  match (trace, direction) with
  | true, `Input -> fun str -> Eio.traceln "[I] %s" str
  | true, `Output -> fun str -> Eio.traceln "[O] %s" str
  | false, _ -> fun _ -> ()

let flow_handler_fib_lsp_writer trace output_flow output_taker () =
  Eio.Buf_write.with_flow output_flow @@ fun buf_w ->
  let output_chan = (buf_w, trace_fun trace `Output) in
  let write_packet out_packet =
    let buf_w, _ = output_chan in
    match Tlapm_lsp_codec.write output_chan out_packet with
    | Ok () -> Eio.Buf_write.flush buf_w
    | Error exn ->
        Eio.traceln "IO Error reading packet: %s" (Printexc.to_string exn)
  in
  let rec write_loop () =
    match output_taker () with
    | Some out_packet ->
        write_packet out_packet;
        write_loop ()
    | None -> ()
  in
  write_loop ()

let flow_handler_fib_lsp_reader trace input_flow event_adder () =
  let buf_r = Eio.Buf_read.of_flow input_flow ~max_size in
  let input_chan = (buf_r, trace_fun trace `Input) in
  let rec read_loop () =
    match Tlapm_lsp_codec.read input_chan with
    | Ok (Some packet) ->
        event_adder (Tlapm_lsp_session.LspPacket packet);
        read_loop ()
    | Ok None ->
        event_adder Tlapm_lsp_session.LspEOF;
        Eio.traceln "No packet was read."
    | Error exn ->
        event_adder Tlapm_lsp_session.LspEOF;
        Eio.traceln "IO Error reading packet: %s" (Printexc.to_string exn)
  in
  read_loop ()

(** Configures the IO for the given input/output flows. *)
let flow_handler trace input_flow output_flow sw fs proc_mgr =
  let events = Eio.Stream.create 100 in
  let event_adder e = Eio.Stream.add events e in
  let event_taker () = Eio.Stream.take events in
  let output = Eio.Stream.create 100 in
  let output_adder e = Eio.Stream.add output e in
  let output_taker () = Eio.Stream.take output in
  Eio.Fiber.all
    [
      (fun () ->
        Tlapm_lsp_session.run event_taker event_adder output_adder sw fs
          proc_mgr);
      flow_handler_fib_lsp_reader trace input_flow event_adder;
      flow_handler_fib_lsp_writer trace output_flow output_taker;
    ]

(** StdIO specifics. *)
module OnStdio = struct
  let run trace env =
    let fs = Eio.Stdenv.fs env in
    let proc_mgr = Eio.Stdenv.process_mgr env in
    let switch_fun sw =
      flow_handler trace (Eio.Stdenv.stdin env) (Eio.Stdenv.stdout env) sw fs
        proc_mgr
    in
    Eio.Switch.run switch_fun
end

(** Socket-specifics. *)
module OnSocket = struct
  let req_handler trace sw fs proc_mgr flow _addr =
    Eio.traceln "Server: got connection from client";
    flow_handler trace flow flow sw fs proc_mgr

  let switch (net : 'a Eio.Net.ty Eio.Std.r) port trace stop_promise fs proc_mgr
      sw =
    Eio.traceln "Socket switch started";
    let on_error = Eio.traceln "Error handling connection: %a" Fmt.exn in
    let addr = `Tcp (Eio.Net.Ipaddr.V4.loopback, port) in
    let sock = Eio.Net.listen net ~sw ~reuse_addr:true ~backlog:5 addr in
    let stopResult =
      Eio.Net.run_server sock
        (req_handler trace sw fs proc_mgr)
        ~on_error ?stop:(Some stop_promise)
    in
    Eio.traceln "StopResult=%s" stopResult

  let run port trace env stop_promise =
    let net = Eio.Stdenv.net env in
    let fs = Eio.Stdenv.fs env in
    let proc_mgr = Eio.Stdenv.process_mgr env in
    Eio.Switch.run @@ switch net port trace stop_promise fs proc_mgr
end

(** Entry point. *)
let run transport trace env stop_promise =
  match transport with
  | Stdio -> OnStdio.run trace env
  | Socket port -> OnSocket.run port trace env stop_promise
