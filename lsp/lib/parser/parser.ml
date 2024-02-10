let module_of_string ~content ~filename ~loader_paths =
  Tlapm_lib.module_of_string ~content ~filename ~loader_paths
    ~prefer_stdlib:true
