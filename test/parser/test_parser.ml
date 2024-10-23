(** This test runs a battery of TLA+ syntax fragments against TLAPM's syntax
    parser. In the future it will check the actual parse tree emitted by
    TLAPM, but for now it just checks whether TLAPM parses without error all
    the syntax it is expected to parse. Tests sourced from:
    https://github.com/tlaplus/tlaplus-standard/tree/main/tests/tlaplus_syntax
*)

open Syntax_corpus_file_parser;;

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

(** Summary for a successful test. *)
let test_summary_succeeded = {
  test_summary_init with
  total = 1;
  succeeded = 1;
}

(** Summary for a failed test. *)
let test_summary_failed info = {
  test_summary_init with
  total     = 1;
  failed    = 1;
  failures  = [info];
}

(** Summary for a skipped test. *)
let test_summary_skipped = {
  test_summary_init with
  total     = 1;
  skipped   = 1;
}

(** Merge and accumulate two test summaries into one. *)
let acc_test_summary acc e = {
  total     = acc.total     + e.total;
  succeeded = acc.succeeded + e.succeeded;
  failed    = acc.failed    + e.failed;
  skipped   = acc.skipped   + e.skipped;
  failures  = List.append acc.failures e.failures;
}

(** Runs a given syntax test by determining its type then sending the input
    into the TLAPM parser. 
    @param should_fail Whether this test should fail due to a TLAPM bug.
    @param test Information about the test itself.
    @return Whether the test succeeded.
*)
let run_test (test : syntax_test) : bool =
  match test.test with
  | Error_test input -> (
    match parse input with
    | None -> true
    | Some _ -> false)
  | Expected_test (input, _) -> (
    match parse input with
    | None -> false
    | Some _ -> true)

(** Controls run of a given syntax test. Checks whether test should be
    skipped and whether it is expected to fail, then runs test and returns
    summary.
    @param should_fail Whether this test should fail due to a TLAPM bug.
    @param test Information about the test itself.
    @return Test run summary.
*)
let control_test_run (should_fail : syntax_test -> bool) (test : syntax_test) : test_run_summary =
  if test.skip then test_summary_skipped else
  if run_test test = should_fail test
  then test_summary_failed test.info
  else test_summary_succeeded

(** Given a path to a directory containing a corpus of syntax tests, get all
    the tests encoded in those files, filter them as appropriate, then run
    them all and collect the results.
    @param path Path to the directory containing the corpus of syntax tests.
    @param should_fail Whether a test should fail due to a TLAPM bug.
    @param filter_predicate Whether to actually execute a test.
    @return Accumulated summary of all test executions.
*)
let run_test_corpus (path : string) (should_fail : syntax_test -> bool) (filter_pred : syntax_test -> bool)  : test_run_summary =
  path
  |> get_all_tests_under
  |> List.filter filter_pred
  |> List.map (control_test_run should_fail)
  |> List.fold_left acc_test_summary test_summary_init

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
  ignore (assert (0 == test_results.failed));
