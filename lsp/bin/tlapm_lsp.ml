open Cmdliner

let transport_of_args tr_stdio tr_socket =
  let open Tlapm_lsp_lib.Server in
  match (tr_stdio, tr_socket) with
  | true, None -> Ok Stdio
  | false, Some port -> Ok (Socket port)
  | _ -> Error "Exactly one of transports has to be specified."

let run transport trace =
  let main env =
    let stop_promise, stop_resolver = Eio.Std.Promise.create () in
    let handle_signal (_signum : int) =
      Eio.Std.Promise.resolve stop_resolver "Stopping on SigINT"
    in
    Sys.set_signal Sys.sigint (Signal_handle handle_signal);
    Tlapm_lsp_lib.Server.run transport trace env stop_promise
  in
  Eio_main.run main

module Cli = struct
  let arg_stdio =
    let doc = "Run LSP over StdIO." in
    let info = Arg.info [ "stdio" ] ~docv:"BOOL" ~doc in
    Arg.value (Arg.flag info)

  let arg_socket =
    let doc = "Run LSP over TCP, use the specified port." in
    let info = Arg.info [ "socket"; "port" ] ~docv:"NUM" ~doc in
    Arg.value (Arg.opt (Arg.some Arg.int) None info)

  let arg_trace =
    let doc = "Trace protocol's IO to the StdErr." in
    let info = Arg.info [ "trace" ] ~docv:"BOOL" ~doc in
    Arg.value (Arg.flag info)

  let term () =
    let combine tr_stdio tr_socket trace =
      match transport_of_args tr_stdio tr_socket with
      | Ok transport -> `Ok (run transport trace)
      | Error err -> `Error (false, err)
    in
    Term.(const combine $ arg_stdio $ arg_socket $ arg_trace)

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
