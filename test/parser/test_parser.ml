open Syntax_corpus_file_parser;;

let () =
  match Tlapm_lib.module_of_string "---- MODULE Test ---- x == 5 ====" with
  | None -> print_endline "Parse failed"
  | Some mule -> print_endline mule.core.name.core

let () =
  "syntax_corpus"
  |> get_all_tests_under
  |> List.map show_syntax_test
  |> List.iter print_endline;
  flush stdout;