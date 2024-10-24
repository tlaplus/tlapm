(** This test runs a battery of TLA+ syntax fragments against TLAPM's syntax
    parser. In the future it will check the actual parse tree emitted by
    TLAPM, but for now it just checks whether TLAPM parses without error all
    the syntax it is expected to parse. Tests sourced from:
    https://github.com/tlaplus/tlaplus-standard/tree/main/tests/tlaplus_syntax
*)

open Syntax_corpus_file_parser;;
open OUnit2;;

(** Calls TLAPM's parser with the given input. Catches all exceptions and
    treats them as parse failures.
    @param input The TLA+ fragment to parse.
    @return None if parse failure, syntax tree root if successful.
*)
let parse (input : string) : Tlapm_lib__M_t.mule option =
  try Tlapm_lib.module_of_string input
  with _ -> None

(** Datatype summarizing a run of all the syntax tests. *)
type test_run_summary = {
  total     : int;
  succeeded : int;
  failed    : int;
  skipped   : int;
  failures  : syntax_test_info list;
} [@@deriving show]

(** A blank test summary. *)
let test_summary_init = {
  total     = 0;
  succeeded = 0;
  failed    = 0;
  skipped   = 0;
  failures  = [];
}

(** Runs a given syntax test by determining its type then sending the input
    into the TLAPM parser. 
    @param expect_failure Whether this test should fail due to a TLAPM bug.
    @param test Information about the test itself.
    @return Whether the test succeeded.
*)
let run_test (test : syntax_test) : bool =
  match test.test with
  | Error_test input -> parse input |> Option.is_none
  | Expected_test (input, _) -> parse input |> Option.is_some

(** Controls run of a given syntax test. Checks whether test should be
    skipped and whether it is expected to fail, then runs test and returns
    summary.
    @param expect_failure Whether this test should fail due to a TLAPM bug.
    @param acc Accumulation variable for test summarization.
    @param test Information about the test itself.
    @return Test run summary.
*)
let control_test_run
  (expect_failure : syntax_test -> bool)
  (acc : test_run_summary)
  (test : syntax_test)
    : test_run_summary =
  let acc = {acc with total = acc.total + 1} in
  if test.skip then {acc with skipped = acc.skipped + 1} else
  if run_test test = expect_failure test
  then {acc with failed = acc.failed + 1; failures = test.info :: acc.failures}
  else {acc with succeeded = acc.succeeded + 1}

(** Given a path to a directory containing a corpus of syntax tests, get all
    the tests encoded in those files, filter them as appropriate, then run
    them all and collect the results.
    @param path Path to the directory containing the corpus of syntax tests.
    @param expect_failure Whether a test should fail due to a TLAPM bug.
    @param filter_predicate Whether to actually execute a test.
    @return Accumulated summary of all test executions.
*)
let run_test_corpus
  (path : string)
  (expect_failure : syntax_test -> bool)
  (filter_pred : syntax_test -> bool)
    : test_run_summary =
  path
  |> get_all_tests_under
  |> List.filter filter_pred
  |> List.fold_left (control_test_run expect_failure) test_summary_init

(** Names of tests that are known to fail due to TLAPM parser bugs.
    @param test Information about the test.
    @return Whether the test is expected to fail.
*)
let expect_failure (test : syntax_test) : bool =
  List.mem test.info.name [
    (* https://github.com/tlaplus/tlapm/issues/11 *)
    "Bounded Quantification With Tuples";
    "Mixed Bounded Quantification With Tuples";
    "Bounded CHOOSE With Tuple";
    "Unbounded CHOOSE With Tuple";
    "Set Filter with Tuple";

    (* https://github.com/tlaplus/tlapm/issues/54#issuecomment-2435515180 *)
    "RECURSIVE inside LET/IN";
    "Conjlist with RECURSIVE in LET/IN";
    "Disjlist with RECURSIVE in LET/IN";
    
    (* https://github.com/tlaplus/tlapm/issues/160 *)
    "Verbose Bounded Quantification";

    (* https://github.com/tlaplus/tlapm/issues/161 *)
    "Infix Minus as Parameter";
    "Prefix Operator References";

    (* https://github.com/tlaplus/tlapm/issues/162 *)
    "Cartesian Product Infix Op Definition";
    "Cartesian Product Declaration as Parameter";

    (* https://github.com/tlaplus/tlapm/issues/163 *)
    "Bitfield Number Formats";

    (* https://github.com/tlaplus/tlapm/issues/164 *)
    "Mistaken Set Filter Test";

    (* https://github.com/tlaplus/tlapm/issues/165 *)
    "Proof by QED with implicit step level";

    (* https://github.com/tlaplus/tlapm/issues/166 *)
    "Use & Hide Modules";
    "Proof by Module References";

    (* https://github.com/tlaplus/tlapm/issues/167 *)
    "Proof with INSTANCE step type";

    "Invalid parentheses use in jlist";
    "Label interfering with precedence";
    "Proof Containing Jlist";
    "Proof Step ID Subexpression Tree Navigation";
  ]

(** Filter predicate to control which tests to run.
    @param name Optional; a test name to filter on.
    @return Predicate matching all tests or tests with given name.
*)
let should_run ?name test =
  match name with
  | Some name -> String.equal test.info.name name
  | None -> true

(** The top-level test; runs all syntax tests, prints summary, then fails
    with an assertion if any tests failed.
*)
let () =
  let test_results =
    run_test_corpus
      "syntax_corpus"
      expect_failure
      (should_run (*~name:"Set Filter with Tuple"*))
  in
  print_endline (show_test_run_summary test_results);
  assert_equal 0 test_results.failed;