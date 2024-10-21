open Syntax_corpus_file_parser;;

let () =
  match Tlapm_lib.module_of_string "---- MODULE Test ---- x == 5 ====" with
  | None -> print_endline "Parse failed"
  | Some mule -> print_endline mule.core.name.core

let () =
  "syntax_corpus"
  |> get_all_tests_under
  |> List.iter (
    fun test ->
      if test.skip then print_endline (show_syntax_test_info test.info) else
      match test.test with
      | Error_test test -> (
        match Tlapm_lib.module_of_string test.input with
        | None -> print_endline "Successful failure"
        | Some _ -> print_endline "Failing success")
      | Expected_test test -> (
        match Tlapm_lib.module_of_string test.input with
        | None -> print_endline "Successful success"
        | Some _ -> print_endline "Failing failure")
  )