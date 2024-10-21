(** This file contains functionality for parsing syntax test corpus files
    into a form for consumption by unit tests. The file format was created
    by tree-sitter; see:
    https://tree-sitter.github.io/tree-sitter/creating-parsers#command-test
*)

open In_channel;;
open List;;
open Str;;
open String;;

(** A regex for finding test header delimiters. *)
let header_regex = regexp {|^===+||||}

(** A regex for finding test body separators. *)
let separator_regex = regexp {|^---+||||}

(** Test attributes for controlling test execution. *)
type test_attribute =
  | Skip
  | Error
[@@deriving show]

(** Given a string attribute tag, resolve it to an enumerated type.
    @param attr The unparsed attribute tag.
    @return A {!type:test_attribute} instance corresponding to the tag.
    @raise Invalid_argument If tag does not correspond to valid attribute.
*)
let str_to_test_attribute (attr : string) : test_attribute =
  match attr with
  | ":skip" -> Skip
  | ":error" -> Error
  | _ -> Invalid_argument (Printf.sprintf "Invalid attribute %s" attr) |> raise

(** All information necessary to run a single syntax test. *)
type syntax_test = {
  file    : string;
  name    : string;
  attrs   : test_attribute list;
  input   : string;
  expect  : string;
} [@@deriving show]

(** Given a test header as a list of lines, decompose & parse it into the
    test name and a list of test attributes.
    @param header A test header split into a list of lines.
    @return A tuple of (test_name, test_attributes).
*)
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
    @raise Invalid_argument If body text lacks a separator.
*)
let parse_test_body (path : string) (test_name : string) (input : string) : string * string =
  match split separator_regex input with
  | input :: output :: [] -> (trim input, trim output)
  | _ -> Invalid_argument (Printf.sprintf "Test body for %s in file %s lacks separator" test_name path) |> raise

(** Given a test file which has been split using the {!val:header_regex},
    parse the various sections to construct a list of information about the
    tests that it contains.
    @param path The test file path, for error reporting purposes.
    @param input The test file contents, split on header tokens.
    @return A list of syntax tests.
    @raise Invalid_argument If there are too many or too few sections.
*)
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

(** Given a path to a syntax test corpus file, parse all tests in that file.
    @param path The path to the syntax test corpus file.
    @return A list of tests contained in the file.
*)
let parse_test_file (path : string) : syntax_test list =
  let test_file = open_in path in
  try
    let text = input_all test_file in
    close_in test_file;
    split header_regex text |> parse_split_test_file path
  with e ->
    close_in_noerr test_file;
    raise e

(** Given the path to a directory, recursively find all files located within
    that directory.
    @param path The path to a directory to search under.
    @return A list of paths to files under the directory.
*)
let rec get_all_files_under (path : string) : string list =
  if Sys.is_directory path then
    Sys.readdir path
    |> Array.to_list
    |> List.map (Filename.concat path)
    |> List.map get_all_files_under
    |> List.flatten
  else [path]

(** Given the path to a directory, return a list of all syntax tests in all
    files under that directory.
    @param path The path to a directory to search under.
    @return A list of syntax tests from the files under the directory.
*)
let get_all_tests_under (path : string) : syntax_test list =
  path |> get_all_files_under |> List.map parse_test_file |> List.flatten