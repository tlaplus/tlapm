
let parse_tla_file filename =
  let open Tlapm_lib in
  let open Stdlib in
  let open Tlapm_lib__Sany in
  let open Tlapm_lib__Params in
  parser_backend := Sany;
  add_debug_flag "sany";
  print_endline ("Parsing " ^ filename ^ " ...");
  try match modctx_of_string ~content:"" ~filename ~loader_paths:[] ~prefer_stdlib:true with
  | Error (_, msg) -> failwith msg
  | Ok _ -> print_endline (filename ^ " success")
  with
  | Unsupported_language_feature (location, RecursiveOperator) ->
    (* This is okay, we just don't support recursive operators *)
    Printf.eprintf "%s:\nUnsupported recursive operator at %s\n" filename (Loc.string_of_locus (Option.get location))
  | Unsupported_language_feature (location, Subexpression) ->
    (* This is okay, we just don't support subexpressions *)
    Printf.eprintf "%s:\nUnsupported subexpression at %s\n" filename (Loc.string_of_locus (Option.get location))
  | Failure (e : string) ->
    Printf.eprintf "%s\n" e;
    failwith filename

let _ = parse_tla_file "Test.tla"
