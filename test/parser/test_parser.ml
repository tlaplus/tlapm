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
    @param should_fail Whether this test should fail due to a TLAPM bug.
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
    @param should_fail Whether this test should fail due to a TLAPM bug.
    @param acc Accumulation variable for test summarization.
    @param test Information about the test itself.
    @return Test run summary.
*)
let control_test_run
  (should_fail : syntax_test -> bool)
  (acc : test_run_summary)
  (test : syntax_test)
    : test_run_summary =
  let acc = {acc with total = acc.total + 1} in
  if test.skip then {acc with skipped = acc.skipped + 1} else
  if run_test test = should_fail test
  then {acc with failed = acc.failed + 1; failures = test.info :: acc.failures}
  else {acc with succeeded = acc.succeeded + 1}

(** Given a path to a directory containing a corpus of syntax tests, get all
    the tests encoded in those files, filter them as appropriate, then run
    them all and collect the results.
    @param path Path to the directory containing the corpus of syntax tests.
    @param should_fail Whether a test should fail due to a TLAPM bug.
    @param filter_predicate Whether to actually execute a test.
    @return Accumulated summary of all test executions.
*)
let run_test_corpus
  (path : string)
  (should_fail : syntax_test -> bool)
  (filter_pred : syntax_test -> bool)
    : test_run_summary =
  path
  |> get_all_tests_under
  |> List.filter filter_pred
  |> List.fold_left (control_test_run should_fail) test_summary_init

(** Names of tests that are known to fail due to TLAPM parser bugs. *)
let failing_test_names = [
  "Invalid parentheses use in jlist";
  "Bounded Quantification With Tuples";
  "Mixed Bounded Quantification With Tuples";
  "Bounded CHOOSE With Tuple";
  "Unbounded CHOOSE With Tuple";
  "Cartesian Product Infix Op Definition";
  "Cartesian Product Declaration as Parameter";
  "Infix Minus as Parameter";
  "RECURSIVE inside LET/IN";
  "Conjlist with RECURSIVE in LET/IN";
  "Disjlist with RECURSIVE in LET/IN";
  "Use & Hide Declarations";
  "Label interfering with precedence";
  "Bitfield Number Formats";
  "Proof by Module References";
  "Proof by QED with implicit step level";
  "Proof with INSTANCE step type";
  "Proof Containing Jlist";
  "Prefix Operator References";
  "Mistaken Set Filter Test";
  "Set Filter with Tuple";
  "Proof Step ID Subexpression Tree Navigation";
]

(** The top-level test; runs all syntax tests, prints summary, then fails
    with an assertion if any tests failed.
*)
let () =
  (* Keeping this around because it's useful when wanting to run a single test. *)
  (*let filter_pred = fun test -> String.equal test.info.name "Proof Containing Jlist" in*)
  let filter_pred = fun _ -> true in
  let should_fail = fun (test : syntax_test) -> List.mem test.info.name failing_test_names in
  let test_results = run_test_corpus "syntax_corpus" should_fail filter_pred in
  print_endline (show_test_run_summary test_results);
  assert_equal 0 test_results.failed;