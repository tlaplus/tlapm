open Syntax_corpus_file_parser;;
open Printf;;

let () =
  match Tlapm_lib.module_of_string "---- MODULE Test ---- x == 5 ====" with
  | None -> print_endline "Parse failed"
  | Some mule -> print_endline mule.core.name.core

let parse (input : string) : Tlapm_lib__M_t.mule option =
  try Tlapm_lib.module_of_string input
  with _ -> None

let () =
  "syntax_corpus"
  |> get_all_tests_under
  |> List.iter (
    fun test ->
      if test.skip then print_endline (show_syntax_test_info test.info) else
      match test.test with
      | Error_test error_test -> (
        match parse error_test.input with
        | None -> (*print_endline (sprintf "SUCCESS [   error] %s: %s" test.info.file test.info.name)*) ()
        | Some _ -> print_endline (sprintf "FAILURE [no error] %s: %s" test.info.file test.info.name); flush stdout)
      | Expected_test expected_test -> (
        match parse expected_test.input with
        | None -> print_endline (sprintf "FAILURE [   error] %s: %s" test.info.file test.info.name); flush stdout
        | Some _ -> (*print_endline (sprintf "SUCCESS [no error] %s: %s" test.info.file test.info.name))*) ())
  )