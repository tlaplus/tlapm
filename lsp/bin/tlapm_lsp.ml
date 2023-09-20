open Cmdliner

type cli_args = { tr_stdio : bool; tr_socket : int option }

let transport_of_args args =
  let open Tlapm_lsp_lib.Server in
  match args with
  | { tr_stdio = true; tr_socket = None; _ } -> Ok Stdio
  | { tr_stdio = false; tr_socket = Some port; _ } -> Ok (Socket port)
  | _ -> Error "Exactly one of transports has to be specified."

let run_with_transport transport =
  let main env =
    let stop_promise, stop_resolver = Eio.Std.Promise.create () in
    let handle_signal (_signum : int) =
      Eio.Std.Promise.resolve stop_resolver "Stopping on SigINT"
    in
    Sys.set_signal Sys.sigint (Signal_handle handle_signal);
    Tlapm_lsp_lib.Server.run transport env stop_promise
  in
  Eio_main.run main

module Cli = struct
  let run_with_args args =
    match transport_of_args args with
    | Ok transport -> `Ok (run_with_transport transport)
    | Error err -> `Error (false, err)

  let arg_stdio =
    let doc = "Run LSP over StdIO." in
    let info = Arg.info [ "stdio" ] ~docv:"BOOL" ~doc in
    Arg.value (Arg.flag info)

  let arg_socket =
    let doc = "Run LSP over TCP, use the specified port." in
    let info = Arg.info [ "socket"; "port" ] ~docv:"NUM" ~doc in
    Arg.value (Arg.opt (Arg.some Arg.int) None info)

  let term () =
    let combine tr_stdio tr_socket =
      let args = { tr_stdio; tr_socket } in
      run_with_args args
    in
    Term.(const combine $ arg_stdio $ arg_socket)

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
