(* cSpell:words cmdliner signum Open_wronly Open_creat fprintf kdprintf *)

open Cmdliner

let traceln_mutex = Mutex.create ()

let transport_of_args tr_stdio tr_socket =
  let open Tlapm_lsp_lib.Server in
  match (tr_stdio, tr_socket) with
  | true, None -> Ok Stdio
  | false, Some port -> Ok (Socket port)
  | _ -> Error "Exactly one of transports has to be specified."

let run transport log_to log_io =
  Printexc.record_backtrace true;
  let main_fun (env : Eio_unix.Stdenv.base) =
    Tlapm_lib.Util.redirect_stdout Format.err_formatter;
    let main_switch _sw =
      let stop_promise, stop_resolver = Eio.Std.Promise.create () in
      let handle_signal (_signum : int) =
        Eio.Std.Promise.resolve stop_resolver "Stopping on SigINT"
      in
      Sys.set_signal Sys.sigint (Signal_handle handle_signal);
      Tlapm_lsp_lib.Server.run transport log_io env stop_promise
    in
    let with_log_stderr () = Eio.Switch.run main_switch in
    let with_log_file log_file =
      let with_log_chan log_chan =
        (* This is mostly a copy of default_traceln from eio/core/debug.ml,
           just modified to take a specific out channel instead of stderr. *)
        let traceln_impl ?__POS__:pos fmt =
          let k go =
            let b = Buffer.create 512 in
            let f = Format.formatter_of_buffer b in
            go f;
            Option.iter
              (fun (file, line, _, _) -> Format.fprintf f " [%s:%d]" file line)
              pos;
            Format.pp_close_box f ();
            Format.pp_print_flush f ();
            let msg = Buffer.contents b in
            let lines = String.split_on_char '\n' msg in
            Mutex.lock traceln_mutex;
            Fun.protect ~finally:(fun () -> Mutex.unlock traceln_mutex)
            @@ fun () ->
            List.iter (Printf.fprintf log_chan "+%s\n") lines;
            flush log_chan
          in
          Format.kdprintf k ("@[" ^^ fmt)
        in
        let traceln_bnd = { Eio.Debug.traceln = traceln_impl } in
        let debug = Eio.Stdenv.debug env in
        Eio.Fiber.with_binding debug#traceln traceln_bnd (fun _ ->
            Format.pp_set_formatter_out_channel Format.err_formatter log_chan;
            Eio.Switch.run main_switch)
      in
      Out_channel.with_open_gen
        [ Open_append; Open_wronly; Open_creat ]
        0o644 log_file with_log_chan
    in
    match log_to with
    | None -> with_log_stderr ()
    | Some log_file -> with_log_file log_file
  in
  Eio_main.run main_fun

module Cli = struct
  let arg_stdio =
    let doc = "Run LSP over StdIO." in
    let info = Arg.info [ "stdio" ] ~docv:"BOOL" ~doc in
    Arg.value (Arg.flag info)

  let arg_socket =
    let doc = "Run LSP over TCP, use the specified port." in
    let info = Arg.info [ "socket"; "port" ] ~docv:"NUM" ~doc in
    Arg.value (Arg.opt (Arg.some Arg.int) None info)

  let arg_log_to =
    let doc = "Log all to the specified file instead of StdErr." in
    let info = Arg.info [ "log-to" ] ~docv:"FILE" ~doc in
    Arg.value (Arg.opt (Arg.some Arg.string) None info)

  let arg_log_io =
    let doc = "Log protocol's IO." in
    let info = Arg.info [ "log-io" ] ~docv:"BOOL" ~doc in
    Arg.value (Arg.flag info)

  let term () =
    let combine tr_stdio tr_socket log_to log_io =
      match transport_of_args tr_stdio tr_socket with
      | Ok transport -> `Ok (run transport log_to log_io)
      | Error err -> `Error (false, err)
    in
    Term.(const combine $ arg_stdio $ arg_socket $ arg_log_to $ arg_log_io)

  let name = "tlapm_lsp"
  let doc = "LSP interface for TLAPS."

  let man =
    [
      `S Manpage.s_description;
      `P "tlapm_lsp allows LSP based IDEs to access the prover functions.";
      `S Manpage.s_see_also;
      `P "The TLAPM code repository: https://github.com/tlaplus/tlapm";
    ]

  let main () =
    let info = Cmd.info ~doc ~man name in
    Cmd.v info (Term.ret (term ())) |> Cmd.eval |> Stdlib.exit
end

let () = Cli.main ()
