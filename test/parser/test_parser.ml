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

type syntax_test = {
  file    : string;
  name    : string;
  input   : string;
  output  : string;
}

let parse_test_file path =
  let test_file = open_in path in
  try
    let text = input_all test_file in
    close_in test_file;
    let rec parse_split_test_file input =
      let parse_test_body input =
        match split separator_regex input with
        | input :: output :: [] -> (trim input, trim output)
        | _ -> Invalid_argument "Test body lacks separator" |> raise
      in match input with
      | [] -> []
      | test_name :: test_body :: ls ->
        let (test_input, test_output) = parse_test_body test_body in {
          file = path;
          name = trim test_name;
          input = test_input;
          output = test_output;
        } :: (parse_split_test_file ls)
      | _ -> Invalid_argument (Printf.sprintf "Test file %s contains extra header separators" path) |> raise
    in split header_regex text |> parse_split_test_file 
  with e ->
    close_in_noerr test_file;
    raise e

let rec get_all_files_under path =
  if Sys.is_directory path then
    Sys.readdir path
    |> Array.to_list
    |> List.map (Filename.concat path)
    |> List.map get_all_files_under
    |> List.flatten
  else [path]

let () =
  let corpus_files = get_all_files_under "syntax_corpus" in
  let test_corpus = List.map parse_test_file corpus_files in
  test_corpus
  |> List.flatten
  |> List.iter (fun r -> Printf.printf "%s\n%s\n%s\n%s\n" r.file r.name r.input r.output);
  flush stdout;