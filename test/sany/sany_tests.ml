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
    String.ends_with ~suffix:"Chameneos.tla";
    String.ends_with ~suffix:"Stones.tla";
    String.ends_with ~suffix:"glowingRaccoon/product.tla";
    (* Subexpressions *)
    String.ends_with ~suffix:"MCPaxos.tla";
    String.ends_with ~suffix:"MCVoting.tla";
    (* Community modules *)
    String.ends_with ~suffix:"MCtcp.tla";
    String.ends_with ~suffix:"tcp.tla";
    String.ends_with ~suffix:"MCReplicatedLog.tla";
    String.ends_with ~suffix:"MCCRDT.tla";
    String.ends_with ~suffix:"DistributedReplicatedLog.tla";
    String.ends_with ~suffix:"SimTokenRing.tla";
    String.ends_with ~suffix:"EWD687a_anim.tla";
    String.ends_with ~suffix:"EWD687a.tla";
    has_substring "/ewd998/";
  ] in not (List.exists (fun pred -> pred path) preds)

let parse_tla_file filename =
  let open Stdlib in
  print_endline ("Parsing " ^ filename ^ " ...");
  try match modctx_of_string ~content:"" ~filename ~loader_paths:[] ~prefer_stdlib:true with
  | Error (_, msg) -> Printf.eprintf "%s\n" msg; failwith "Parsing failed"
  | Ok _ -> print_endline (filename ^ " success")
  with Failure (e : string) ->
    Printf.eprintf "%s\n" e;
    failwith "Parsing failed"

let _ =
  parser_backend := Sany;
  add_debug_flag "sany";
  let tla_files = find_tla_files "/mnt/data/ahelwer/src/tlaplus/examples/specifications" |> List.filter should_run in
  List.map parse_tla_file tla_files
