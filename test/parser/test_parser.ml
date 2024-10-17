open In_channel;;
open List;;
open Str;;
open String;;

let () =
    match Tlapm_lib.module_of_string "---- MODULE Test ---- x == 5 ====" with
    | None -> print_endline "Parse failed"
    | Some mule -> print_endline mule.core.name.core
    
let header_regex = regexp {|^===+||||}

let separator_regex = regexp {|^---+||||}

let parse_test_body input =
    match split separator_regex input with
    | input :: output :: [] -> (trim input, trim output)
    | _ -> raise (Invalid_argument "Malformed test body")

let rec parse_split_test_file input =
    match input with
    | [] -> []
    | test_name :: test_body :: ls ->
        let (test_input, test_output) = parse_test_body test_body in
        (trim test_name, test_input, test_output) :: (parse_split_test_file ls)
    | _ -> raise (Invalid_argument "Malformed test file")

let parse_test_file path =
    let test_file = open_in path in
    try
        let text = input_all test_file in
        close_in test_file;
        parse_split_test_file (split header_regex text)
    with e ->
        close_in_noerr test_file;
        raise e


let () =
    let tests = parse_test_file "syntax_corpus/modules.txt" in
    let test_names = List.map (fun (a, _, _) -> a) tests in
    List.iter print_endline test_names;
    flush stdout;