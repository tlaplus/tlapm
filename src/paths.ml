(** Take paths from the sites, or fallback to the the path relative to the exec. *)
let site_paths sites sub_path =
  match sites with
  | [] ->
      let bin_dir = Filename.dirname Sys.executable_name in
      let prefix_dir = Filename.dirname bin_dir in
      [ List.fold_left Filename.concat prefix_dir sub_path ]
  | _ :: _ -> sites

(** A list of paths potentially containing the backend execs. *)
let backend_paths =
  site_paths Setup_paths.Sites.backends [ "lib"; "tlapm"; "backends" ]

(** A list of paths potentially containing the STDLIB modules. *)
let stdlib_paths =
  site_paths Setup_paths.Sites.stdlib [ "lib"; "tlapm"; "stdlib" ]

(** If the backends site is not available ([]), then look for executables in the PATH,
      otherwise we are in the dune-based build and should look for the backends in the
      specified site locations. *)
let backend_path_string =
  let site_bin bs = Filename.concat bs "bin" in
  let site_isa bs = List.fold_left Filename.concat bs [ "Isabelle"; "bin" ] in
  let site_paths bs = [ site_bin bs; site_isa bs ] in
  let path_elems = List.concat (List.map site_paths backend_paths) in
  Printf.sprintf "%s:%s" (String.concat ":" path_elems) (Sys.getenv "PATH")

let find_path_containing paths file =
  let find_actual path = Sys.file_exists (Filename.concat path file) in
  List.find_opt find_actual paths
