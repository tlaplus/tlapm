
let find_tla_files dir =
  let cmd = Printf.sprintf "find %s -name '*Test.tla'" (Filename.quote dir) in
  let ic = Unix.open_process_in cmd in
  let rec loop acc =
    match input_line ic with
    | line -> loop (line :: acc)
    | exception End_of_file ->
      ignore (Unix.close_process_in ic);
      List.rev acc
  in
  loop []

let read_file (filepath : string) : string =
  let ic = open_in filepath in
  let content = really_input_string ic (in_channel_length ic) in
  close_in ic;
  content

open OUnit2;;
open Tlapm_lib;;
open Stdlib;;
open Tlapm_lib__Params;;
open Tlapm_lib__Sany;;

let compare_syntax_trees (filepath : string) (source_code : string) (is_error : bool) : unit =
  parser_backend := Tlapm;
  match module_of_string source_code with
  | None -> assert_failure "TLAPM failed to parse the test input"
  | Some tlapm_mule ->
    parser_backend := Sany;
    match parse filepath with
    | Error _ -> assert_failure "SANY failed to parse the test input"
    | Ok (_, sany_mule) ->
      let open Sexplib in
      let tlapm_tree = module_to_sexp tlapm_mule in
      let sany_tree = module_to_sexp sany_mule in
      if Sexp.equal tlapm_tree sany_tree
      then assert_bool "Syntax trees equivalent but SANY failed" (not is_error)
      else
        let open Sexp_diff in
        let diff = Algo.diff ~original:tlapm_tree ~updated:sany_tree () in
        let options = Display.Display_options.(create Layout.Single_column) in
        let text = Display.display_with_ansi_colors options diff in
        assert_failure (
        if is_error then (Printf.sprintf "SANY failed and parse trees differ:\n%s" text)
        else (Printf.sprintf "SANY succeeded but parse trees differ:\n%s" text))

let run_test (filename : string) (_ctx: test_ctxt) : unit =
  (*add_debug_flag "sany";*)
  let content = read_file filename in
  parser_backend := Sany;
  try match modctx_of_string ~content ~filename ~loader_paths:[] ~prefer_stdlib:true with
  | Error _ -> compare_syntax_trees filename content true
  | Ok _ -> compare_syntax_trees filename content false
  with
  | Failure _ -> compare_syntax_trees filename content true
  | Not_found -> compare_syntax_trees filename content true

let mk_test (filepath : string) : test =
  Filename.basename filepath >:: (run_test filepath)

let tests = "SANY semantic escalation tests" >::: (
  find_tla_files "."
  |> List.sort String.compare
  |> List.map mk_test
)

(** The OUnit2 test entrypoint. *)
let () = run_test_tt_main tests
