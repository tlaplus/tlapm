module EioLspServer = Tlapm_lsp_lib.EioLspServer

(** The main entry point. *)
let () =
  Eio_main.run @@ fun env ->
    let (stop_promise, stop_resolver) = Eio.Std.Promise.create () in
    let handle_signal (_signum : int) = Eio.Std.Promise.resolve stop_resolver "Stopping on SigINT" in
    let () = Sys.set_signal Sys.sigint (Signal_handle handle_signal) in
    EioLspServer.run env stop_promise
