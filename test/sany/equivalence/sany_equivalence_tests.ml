(** This series of tests reads in a list of TLA+ files that are numbered in
    increasing order. Broadly speaking each TLA+ file is slightly more complex
    than the one before it; the purpose of this is to test TLAPM's SANY output
    translation functionality by incrementally bringing it up to parity with
    the existing OCaml TLA+ parser. Method:

      1. Parse, elaborate & check proofs with TLAPM (baseline validation)
      2. Parse module by sending it through SANY XML Exporter
      3. Parse XML & convert to TLAPM-compatible syntax parse tree
      4. Run semantic & level-checking (elaboration) on converted parse tree
      5. Check proofs in converted parse tree
      6. Convert both TLAPM & SANY parse trees to standard S-expression form
      7. Check TLAPM & SANY S-expression parse trees for equivalence

    While the final comparison does not capture all aspects of parse tree
    equivalence (for example, node properties), it is a good first pass and
    importantly also produces easily diffable comparisons which greatly ease
    debugging parse tree mismatches.
    
    Note that there are several irreconcilable ways in which the TLAPM parse
    tree differs from the SANY parse tree. This is due to the peculiarities
    of SANY's XML Exporter. For example, the declaration VARIABLES x, y, z
    will be grouped together by TLAPM's parser, but SANY exports this as if
    it were VARIABLE x VARIABLE y VARIABLE z. The test files are written in
    a certain way that papers over these inconsistencies. Writing a more
    capable tree comparison operator that has knowledge of these differences
    is desirable, since then general TLA+ files seen "in the wild" could be
    compared for equivalence between the two parsers.
*)

(** Gets a list of all TLA+ files used for the test by parsing the output of
    the `find` command line tool.
*)
let find_tla_files (dir : string) : string list =
  let cmd : string = Printf.sprintf "find %s -name '*Test.tla'" (Filename.quote dir) in
  let ic : in_channel = Unix.open_process_in cmd in
  let rec loop (acc : string list) : string list =
    match input_line ic with
    | line -> loop (line :: acc)
    | exception End_of_file ->
      ignore (Unix.close_process_in ic);
      acc
  in loop []

(** Reads the entire contents of a file into a string.
*)
let read_file (filepath : string) : string =
  let ic : in_channel = open_in filepath in
  let content : string = really_input_string ic (in_channel_length ic) in
  close_in ic;
  content

open OUnit2;;
open Tlapm_lib;;
open Stdlib;;
open Tlapm_lib__Params;;
open Tlapm_lib__Sany;;

(** Compares syntax trees from TLAPM and SANY, printing a diff if they do not
    match.
*)
let compare_syntax_trees (filepath : string) (source_code : string) (is_error : bool) : unit =
  parser_backend := Tlapm;
  try match module_of_string source_code with
  | None -> assert_failure "TLAPM failed to parse the test input syntax"
  | Some tlapm_mule -> (
    parser_backend := Sany;
    try match parse filepath with
    | Error _ -> assert_failure "SANY failed to parse the test input syntax"
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
    with Failure _ -> assert_failure "SANY failed to parse the test input syntax"
  ) with Failure _ -> assert_failure "TLAPM failed to parse the test input syntax"

(** Parses & elaborates file, but does not check proofs.
*)
let _check (filename : string) (content : string) : (unit, string) result =
  try match modctx_of_string ~content ~filename ~loader_paths:[] ~prefer_stdlib:true with
  | Error (_, msg) -> Error msg 
  | Ok _ -> Ok ()
  with Failure msg -> Error msg

(** Parses & elaborates file, then checks proofs.
*)
let full_check (filename : string) (_content : string) : (unit, string) result =
  try Ok (main [filename])
  with Failure (msg : string) -> Error msg

(** Parses the given file with TLAPM's OCaml parser.
*)
let check_in_tlapm : string -> string -> (unit, string) result =
  parser_backend := Tlapm;
  full_check

(** Parses the given file with SANY.
*)
let check_in_sany : string -> string -> (unit, string) result =
  parser_backend := Sany;
  full_check

(** Checks that the given TLA+ file can be parsed with TLAPM's parser,
    then checks that it can be parsed with SANY, then compare the two
    syntax trees for equivalence.
*)
let run_test (filename : string) (_ctx: test_ctxt) : unit =
  (*add_debug_flag "sany";*)
  let content = read_file filename in
  match check_in_tlapm filename content with
  | Error msg -> assert_failure ("TLAPM failed to parse the test input: " ^ msg)
  | Ok () -> match check_in_sany filename content with
  | Error _ -> compare_syntax_trees filename content true
  | Ok () -> compare_syntax_trees filename content false

(** Constructs a test case out of the given TLA+ file path.
*)
let mk_test (filepath : string) : test =
  Filename.basename filepath >:: (run_test filepath)

(** Constructs a test suite out of the series of TLA+ files by sorting them
    according to increasing number.
*)
let tests = "SANY-TLAPM equivalence tests" >::: (
  find_tla_files "."
  |> List.sort String.compare
  |> List.map mk_test
)

(** The OUnit2 test entrypoint. *)
let () =
  add_debug_flag "sany";
  run_test_tt_main tests
