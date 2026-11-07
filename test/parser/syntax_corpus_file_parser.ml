(** This file contains functionality for parsing syntax test corpus files
    into a form for consumption by unit tests. The file format was created
    by tree-sitter; see:
    https://tree-sitter.github.io/tree-sitter/creating-parsers#command-test
*)

open In_channel;;
open List;;
open Printf;;
open Str;;
open String;;
open Sexplib;;

(** A regex for finding test header delimiters. *)
let header_regex = regexp {|^===+||||}

(** A regex for finding test body separators. *)
let separator_regex = regexp {|^---+||||}

(** Test attributes for controlling test execution. *)
type test_attribute =
  | Skip
  | Accept (* Require successful parsing without comparing the tree. *)
  | Equiv (* Compare the Actual and Reference expression structures. *)
  | Roundtrip (* Preserve expressions when printing and reparsing. *)
  | Error of string option
[@@deriving show]

(** Given a string attribute tag, resolve it to an enumerated type.
    @param attr The unparsed attribute tag.
    @return A {!type:test_attribute} instance corresponding to the tag.
    @raise Invalid_argument If tag does not correspond to valid attribute.
*)
let str_to_test_attribute (attr : string) : test_attribute =
  match attr with
  | ":skip" -> Skip
  | ":accept" -> Accept
  | ":equiv" -> Equiv
  | ":roundtrip" -> Roundtrip
  | ":error" -> Error None
  | _ when String.starts_with ~prefix:":error " attr ->
      let message = String.sub attr 7 (String.length attr - 7) |> trim in
      if message = "" then invalid_arg "Empty :error diagnostic";
      Error (Some message)
  | _ -> Invalid_argument (sprintf "Invalid attribute %s" attr) |> raise

(** Metadata about a syntax test. *)
type syntax_test_info = {
  path    : string;
  name    : string;
} [@@deriving show]

(** Enumeration of syntax test variants. *)
type syntax_test_variant =
  | Accept_test of string
  | Equiv_test of string
  | Roundtrip_test of string
  | Error_test of (string * string option)
  | Expected_test of (string * Sexp.t)
[@@deriving show]

(** All information necessary to run a single syntax test. *)
type syntax_test = {
  info  : syntax_test_info;
  skip  : bool;
  test  : syntax_test_variant;
} [@@deriving show]

(** Given a test header as a list of lines, decompose & parse it into the
    test name and a list of test attributes.
    @param header A test header split into a list of lines.
    @return A tuple of (test_name, test_attributes).
*)
let parse_test_header (header : string list) : string * (test_attribute list) =
  let is_attr = String.starts_with ~prefix: ":" in
  let (test_attrs, test_name) = List.partition is_attr header in
  (hd test_name, test_attrs |> List.map str_to_test_attribute)

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
  | _ -> Invalid_argument (sprintf "Test body for %s in file %s lacks separator" test_name path) |> raise

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
    let (name, test_attrs) = test_header |> trim |> split_on_char '\n' |> parse_test_header in
    let (test_input, test_output) = parse_test_body path name test_body in
    let errors = List.filter_map (function Error msg -> Some msg | _ -> None) test_attrs in
    let test = match List.mem Accept test_attrs, List.mem Equiv test_attrs,
                     List.mem Roundtrip test_attrs, errors with
      | true, false, false, [] -> Accept_test test_input
      | false, true, false, [] -> Equiv_test test_input
      | false, false, true, [] -> Roundtrip_test test_input
      | false, false, false, [] -> Expected_test (test_input, Sexp.of_string test_output)
      | false, false, false, [message] -> Error_test (test_input, message)
      | _ -> Invalid_argument
          (sprintf "Conflicting test attributes for %s in %s" name path) |> raise
    in {
      info = { path; name; };
      skip = List.mem Skip test_attrs; 
      test;
    } :: (parse_split_test_file path ls)
  | _ -> Invalid_argument (sprintf "Test file %s contains extra header separators" path) |> raise

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

module Shape = struct
  type 'a t = { label : string; content : 'a content }
  and 'a content =
    | Atom of 'a
    | List of 'a t list

  let rec map f x = { x with content = map_content f x.content }
  and map_content f = function
    | Atom x -> f x
    | List xs -> List (List.map (map f) xs)
end

(** Given the path to a directory, recursively find all files located within
    that directory.
    @param path The path to a directory to search under.
    @return A list of paths to files under the directory.
*)
let rec get_all_files_under (path : string) : string Shape.content =
  if Sys.is_directory path then
    Sys.readdir path
    |> Array.to_list
    |> List.sort String.compare
    |> List.map (fun label ->
           let content = get_all_files_under (Filename.concat path label) in
           Shape.{ label; content })
    |> (fun x -> Shape.List x)
  else Atom path

(** Given the path to a directory, return a list of all syntax tests in all
    files under that directory.
    @param path The path to a directory to search under.
    @return A list of syntax tests from the files under the directory.
*)
let get_all_tests_under (path : string) : syntax_test Shape.content =
  path |> get_all_files_under
  |> Shape.map_content
       (fun path ->
         parse_test_file path
         |> List.map
              (fun (t : syntax_test) ->
                Shape.{ label = t.info.name; content = Atom t })
         |> (fun x -> Shape.List x))
