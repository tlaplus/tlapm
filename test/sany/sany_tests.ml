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

let has_substring needle haystack =
  match Str.search_forward (Str.regexp_string needle) haystack 0 with
  | _ -> true
  | exception Not_found -> false

let should_run (path : string) : bool =
  let preds = [
    (* RECURSIVE operators *)
    (*
    String.ends_with ~suffix:"Chameneos.tla";
    String.ends_with ~suffix:"Stones.tla";
    String.ends_with ~suffix:"glowingRaccoon/product.tla";
    String.ends_with ~suffix:"CarTalkPuzzle.tla";
    String.ends_with ~suffix:"CarTalkPuzzle.toolbox/Model_1/MC.tla";
    String.ends_with ~suffix:"CarTalkPuzzle.toolbox/Model_2/MC.tla";
    String.ends_with ~suffix:"CarTalkPuzzle.toolbox/Model_3/MC.tla";
    String.ends_with ~suffix:"EWD840_json.tla";
    String.ends_with ~suffix:"SingleLaneBridge.tla";
    String.ends_with ~suffix:"SingleLaneBridge/MC.tla";
    String.ends_with ~suffix:"GameOfLife.tla";
    String.ends_with ~suffix:"btree.tla";
    String.ends_with ~suffix:"Nano.tla";
    String.ends_with ~suffix:"Huang.tla";
    has_substring "/tower_of_hanoi/";
    *)
    (* Subexpressions *)
    String.ends_with ~suffix:"MCPaxos.tla";
    String.ends_with ~suffix:"MCVoting.tla";
    String.ends_with ~suffix:"EWD840_proof.tla";
    String.ends_with ~suffix:"BPConProof.tla";
    String.ends_with ~suffix:"PConProof.tla";
    String.ends_with ~suffix:"VoteProof.tla";
    (* PlusCal validation output bug *)
    String.ends_with ~suffix:"AddTwo.tla";
    has_substring "/ewd998/";
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
  let open Stdlib in
  let open Tlapm_lib__Sany in
  print_endline ("Parsing " ^ filename ^ " ...");
  try match modctx_of_string ~content:"" ~filename ~loader_paths:[] ~prefer_stdlib:true with
  | Error (_, msg) -> Printf.eprintf "%s\n" msg; failwith "Parsing failed"
  | Ok _ -> print_endline (filename ^ " success")
  with
    (* This is okay, we just don't support recursive operators *)
  | Unsupported_language_feature (_, RecursiveOperator) -> ()
  | Failure (e : string) ->
    Printf.eprintf "%s\n" e;
    failwith "Parsing failed"

let _ =
  parser_backend := Sany;
  module_jar_paths := [
    "/mnt/data/ahelwer/src/tlaplus/examples/deps/apalache/lib/apalache.jar";
    "/mnt/data/ahelwer/src/tlaplus/examples/deps/community/modules.jar";
  ];
  add_debug_flag "sany";
  let tla_files =
    find_tla_files "/mnt/data/ahelwer/src/tlaplus/examples/specifications"
    |> List.filter should_run
    (*|> _start_at "SimTokenRing.tla"*)
  in List.map parse_tla_file tla_files
