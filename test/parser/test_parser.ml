open In_channel;;
open List;;
open Str;;

let () =
    match Tlapm_lib.module_of_string "---- MODULE Test ---- x == 5 ====" with
    | None -> print_endline "Parse failed"
    | Some mule -> print_endline mule.core.name.core

let () =
    let test_file = open_in "syntax_corpus/modules.txt" in
    try
        let lines = input_lines test_file in
        iter print_endline lines;
        flush stdout;
        close_in test_file
    with e ->
        close_in_noerr test_file;
        raise e