(** Responsible for parsing the TLA+ documents.
    TODO: SANY integration should be added here as well.
    *)

val module_of_string :
  content:string ->
  filename:string ->
  loader_paths:string list ->
  (Tlapm_lib.Module.T.mule, string option * string) result
