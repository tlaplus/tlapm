open In_channel;;
open List;;
open Str;;
open String;;

let header_regex = regexp {|^===+||||}

let separator_regex = regexp {|^---+||||}

type test_attribute =
  | Skip
  | Error
[@@deriving show]

let str_to_test_attribute (attr : string) : test_attribute =
  match attr with
  | ":skip" -> Skip
  | ":error" -> Error
  | _ -> Invalid_argument (Printf.sprintf "Invalid attribute %s" attr) |> raise

type syntax_test = {
  file    : string;
  name    : string;
  attrs   : test_attribute list;
  input   : string;
  expect  : string;
} [@@deriving show]

let parse_test_header (header : string list) : string * (test_attribute list) =
  let is_attr (line : string) : bool = length line > 0 && ':' == get line 0 in
  let test_name = List.find (fun line -> line |> is_attr |> not) header in
  let test_attrs = header |> List.filter is_attr |> List.map str_to_test_attribute in
  (test_name, test_attrs)

(** Given the body of a test as a string, split it into input and expected
    output; raise an error if this is not possible.
    @param path The path to the test file, for error reporting purposes.
    @param test_name The test name, for error reporting purposes.
    @param input The unparsed test body, as a string.
    @return A two-tuple with first element input and second element output.
    @raise Invalid_argument If body text lacks a separator. *)
let parse_test_body (path : string) (test_name : string) (input : string) : string * string =
  match split separator_regex input with
  | input :: output :: [] -> (trim input, trim output)
  | _ -> Invalid_argument (Printf.sprintf "Test body for %s in file %s lacks separator" test_name path) |> raise

let rec parse_split_test_file (path : string) (input : string list) : syntax_test list =
  match input with
  | [] -> []
  | test_header :: test_body :: ls ->
    let (test_name, test_attrs) = test_header |> trim |> split_on_char '\n' |> parse_test_header in
    let (test_input, test_output) = parse_test_body path test_name test_body in {
      file = path;
      name = test_name;
      attrs = test_attrs;
      input = test_input;
      expect = test_output;
    } :: (parse_split_test_file path ls)
  | _ -> Invalid_argument (Printf.sprintf "Test file %s contains extra header separators" path) |> raise

let parse_test_file (path : string) : syntax_test list =
  let test_file = open_in path in
  try
    let text = input_all test_file in
    close_in test_file;
    split header_regex text |> parse_split_test_file path
  with e ->
    close_in_noerr test_file;
    raise e

let rec get_all_files_under (path : string) : string list =
  if Sys.is_directory path then
    Sys.readdir path
    |> Array.to_list
    |> List.map (Filename.concat path)
    |> List.map get_all_files_under
    |> List.flatten
  else [path]

let get_all_tests_under (path : string) : syntax_test list =
  path |> get_all_files_under |> List.map parse_test_file |> List.flatten