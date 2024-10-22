open Syntax_corpus_file_parser;;

let () =
  match Tlapm_lib.module_of_string "---- MODULE Test ---- x == 5 ====" with
  | None -> print_endline "Parse failed"
  | Some mule -> print_endline mule.core.name.core

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

let run_test (test : syntax_test) : test_run_summary =
  if test.skip then test_summary_skipped else
  match test.test with
  | Error_test input -> (
    match parse input with
    | None -> test_summary_succeeded
    | Some _ -> test_summary_failed test.info)
  | Expected_test (input, _) -> (
    match parse input with
    | None -> test_summary_failed test.info
    | Some _ -> test_summary_succeeded)

let run_test_corpus (path : string) (pred : syntax_test -> bool) : test_run_summary =
  path
  |> get_all_tests_under
  |> List.filter pred
  |> List.map run_test
  |> List.fold_left acc_test_summary test_summary_init

let () =
  (*fun test -> String.equal test.info.name "Proof Containing Jlist"*)
  (fun _ -> true)
  |> run_test_corpus "syntax_corpus" 
  |> show_test_run_summary
  |> print_endline