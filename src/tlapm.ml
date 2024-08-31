let main fs =
    Tlapm_lib.main fs;

exception Stacktrace;;

let () =
  Sys.set_signal
    Sys.sigusr1
    (Sys.Signal_handle (fun _ -> raise Stacktrace));
  Tlapm_lib.init ();
