let loader_paths : string list ref = ref []

let module_of_string content filename =
  Tlapm_lib.module_of_string ~content ~filename ~loader_paths:!loader_paths
    ~prefer_stdlib:true

let use_paths paths = loader_paths := paths
