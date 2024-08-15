let module_of_string ~content ~filename ~loader_paths =
  Tlapm_lib.transitive_parse_module_of_string ~content ~filename ~loader_paths
    ~prefer_stdlib:true
