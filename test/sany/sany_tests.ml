open Tlapm_lib;;
open Tlapm_lib__Params;;

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

let _has_substring needle haystack =
  match Str.search_forward (Str.regexp_string needle) haystack 0 with
  | _ -> true
  | exception Not_found -> false

let should_run (path : string) : bool =
  let preds = [
    String.ends_with ~suffix:"paxos/Paxos.tla";
    String.ends_with ~suffix:"ByzPaxos/BPConProof.tla";
    String.ends_with ~suffix:"GraphTheorem.tla";
    String.ends_with ~suffix:"NegativeOpTest.tla";
  ] in not (List.exists (fun pred -> pred path) preds)

let _start_at (filename : string) (files : string list) : string list =
  let rec drop_until (paths : string list) : string list =
    match paths with
    | [] -> []
    | hd :: tl ->
      if String.ends_with ~suffix:filename hd then paths
      else drop_until tl
  in drop_until files

let parse_tla_file filename =
  let open Tlapm_lib__Sany in
  print_endline ("Parsing " ^ filename ^ " ...");
  try match parse filename with
  | Error (_, msg) -> failwith msg
  | Ok _ -> print_endline (filename ^ " success")
  with
  | Unsupported_language_feature (location, RecursiveOperator) ->
    (* This is okay, we just don't support recursive operators *)
    Printf.eprintf "%s:\nUnsupported recursive operator at %s\n" filename (Loc.string_of_locus (Option.get location))
  | Unsupported_language_feature (location, Subexpression) ->
    (* This is okay, we just don't support subexpressions *)
    Printf.eprintf "%s:\nUnsupported subexpression at %s\n" filename (Loc.string_of_locus (Option.get location))
  (*| Failure (e : string) ->
    Printf.eprintf "%s\n" e;
    failwith filename*)

let _ =
  parser_backend := Sany;
  module_jar_paths := [
    "/mnt/data/ahelwer/src/tlaplus/examples/deps/apalache/lib/apalache.jar";
    "/mnt/data/ahelwer/src/tlaplus/examples/deps/community/modules.jar";
  ];
  add_debug_flag "sany";
  let tla_files = [
    "/mnt/data/ahelwer/src/tlaplus/examples/specifications";
    "/mnt/data/ahelwer/src/tlaplus/proofs/library";
    "/mnt/data/ahelwer/src/tlaplus/proofs/examples";
    "/home/ahelwer/src/tlaplus/java-tools/tlatools/org.lamport.tlatools/test/tla2sany/semantic/corpus";
    ] |> List.map find_tla_files |> List.flatten
    |> List.filter should_run
    (*|> _start_at "paxos/Paxos.tla"*)
  in List.map parse_tla_file tla_files
