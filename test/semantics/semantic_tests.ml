
let find_tla_files dir =
  let cmd = Printf.sprintf "find %s -name '*.tla'" (Filename.quote dir) in
  let ic = Unix.open_process_in cmd in
  let rec loop acc =
    match input_line ic with
    | line -> loop (line :: acc)
    | exception End_of_file ->
      ignore (Unix.close_process_in ic);
      List.rev acc
  in
  loop []

let parse_tla_file filename =
  let open Tlapm_lib in
  let open Stdlib in
  let open Tlapm_lib__Params in
  parser_backend := Sany;
  add_debug_flag "sany";
  print_endline ("Parsing " ^ filename ^ " ...");
  try match modctx_of_string ~content:"" ~filename ~loader_paths:[] ~prefer_stdlib:true with
  | Error (_, msg) -> failwith msg
  | Ok _ -> print_endline (filename ^ " success")
  with
  | Failure (e : string) ->
    Printf.eprintf "%s\n" e;
    failwith filename

let _ = "." |> find_tla_files |> List.map parse_tla_file
