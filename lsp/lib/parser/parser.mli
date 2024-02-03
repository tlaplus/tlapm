(** Responsible for parsing the TLA+ documents.
    TODO: SANY integration should be added here as well.
    *)

val module_of_string :
  string -> string -> (Tlapm_lib.Module.T.mule, string option * string) result

(* TODO: A dirty workaround here. Should pass the paths explicitly. *)
val use_paths : string list -> unit
