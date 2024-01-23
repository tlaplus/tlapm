(** Responsible for parsing the TLA+ documents.
    TODO: More functionality from the [proof_step] should be moved here.
    TODO: SANY integration should be added here as well.
    *)

val module_of_string :
  string -> string -> (Tlapm_lib.Module.T.mule, string option * string) result
