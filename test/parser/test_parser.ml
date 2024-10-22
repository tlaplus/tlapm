open Syntax_corpus_file_parser;;

let parse (input : string) : Tlapm_lib__M_t.mule option =
  try Tlapm_lib.module_of_string input
  with _ -> None

type test_run_summary = {
  total     : int;
  succeeded : int;
  failed    : int;
  skipped   : int;
  failures  : syntax_test_info list;
} [@@deriving show]

let test_summary_init = {
  total     = 0;
  succeeded = 0;
  failed    = 0;
  skipped   = 0;
  failures  = [];
}

let test_summary_succeeded = {
  test_summary_init with
  total = 1;
  succeeded = 1;
}

let test_summary_failed info = {
  test_summary_init with
  total     = 1;
  failed    = 1;
  failures  = [info];
}

let test_summary_skipped = {
  test_summary_init with
  total     = 1;
  skipped   = 1;
}

let acc_test_summary acc e = {
  total     = acc.total     + e.total;
  succeeded = acc.succeeded + e.succeeded;
  failed    = acc.failed    + e.failed;
  skipped   = acc.skipped   + e.skipped;
  failures  = List.append acc.failures e.failures;
}

let run_test (should_fail : syntax_test -> bool) (test : syntax_test) : test_run_summary =
  if test.skip then test_summary_skipped else
  match test.test with
  | Error_test input -> (
    match parse input with
    | None -> if should_fail test then test_summary_failed test.info else test_summary_succeeded
    | Some _ -> if should_fail test then test_summary_succeeded else test_summary_failed test.info)
  | Expected_test (input, _) -> (
    match parse input with
    | None -> if should_fail test then test_summary_succeeded else test_summary_failed test.info
    | Some _ -> if should_fail test then test_summary_failed test.info else test_summary_succeeded)

let run_test_corpus (path : string) (should_fail : syntax_test -> bool) (filter_pred : syntax_test -> bool)  : test_run_summary =
  path
  |> get_all_tests_under
  |> List.filter filter_pred
  |> List.map (run_test should_fail)
  |> List.fold_left acc_test_summary test_summary_init

let error_test_names = [
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

let () =
  (* Keeping this around because it's useful when wanting to run a single test. *)
  (*let filter_pred = fun test -> String.equal test.info.name "Proof Containing Jlist" in*)
  let filter_pred = fun _ -> true in
  let test_results = run_test_corpus
    "syntax_corpus"
    (fun test -> List.mem test.info.name error_test_names)
    filter_pred
  in print_endline (show_test_run_summary test_results);
  ignore (assert (0 == test_results.failed));