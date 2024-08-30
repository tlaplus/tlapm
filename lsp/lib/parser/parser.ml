let module_of_string ~content ~filename ~loader_paths =
  match
    Tlapm_lib.modctx_of_string ~content ~filename ~loader_paths
      ~prefer_stdlib:true
  with
  | Ok (_mcx, mule) -> Ok mule
  | Error err -> Error err