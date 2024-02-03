let loader_paths : string list ref = ref []

let module_of_string content file_name =
  Tlapm_lib.module_of_string content file_name !loader_paths

let use_paths paths = loader_paths := paths
