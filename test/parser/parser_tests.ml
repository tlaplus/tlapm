(** This test runs a battery of TLA+ syntax fragments against TLAPM's syntax
    parser. In the future it will check the actual parse tree emitted by
    TLAPM, but for now it just checks whether TLAPM parses without error all
    the syntax it is expected to parse. Tests sourced from:
    https://github.com/tlaplus/rfcs/tree/2a772d9dd11acec5d7dedf30abfab91a49de48b8/language_standard/tests/tlaplus_syntax
*)

open Tlapm_lib;;

open Syntax_corpus_file_parser;;
open Translate_syntax_tree;;

open Sexplib;;
open OUnit2;;

(** Calls TLAPM's parser with the given input. Catches all exceptions and
    treats them as parse failures.
    @param input The TLA+ fragment to parse.
    @return None if parse failure, syntax tree root if successful.
*)
let parse (input : string) : Module.T.mule option =
  let send_output (_ : out_channel) (_ : string) : unit = () in
  try module_of_string ~send_output input
  with _ -> None

(** Names of tests that are known to fail due to TLAPM parser bugs.
    @param test Information about the test.
    @return Whether the test is expected to fail.
*)
let expect_failure (test : syntax_test) : bool =
  List.mem test.info.name [

    (* https://github.com/tlaplus/tlapm/issues/54#issuecomment-2435515180 *)
    "RECURSIVE inside LET/IN";
    "Conjlist with RECURSIVE in LET/IN";
    "Disjlist with RECURSIVE in LET/IN";

    (* https://github.com/tlaplus/tlapm/issues/161 *)
    "Infix Minus as Parameter";
    "Prefix Operator References";

    (* https://github.com/tlaplus/tlapm/issues/162 *)
    "Cartesian Product Infix Op Definition";
    "Cartesian Product Declaration as Parameter";

    (* https://github.com/tlaplus/tlapm/issues/163 *)
    "Bitfield Number Formats";

    (* https://github.com/tlaplus/tlapm/issues/165 *)
    "Proof by QED with implicit step level";

    (* https://github.com/tlaplus/tlapm/issues/166 *)
    "Use & Hide Modules";
    "Proof by Module References";

    (* https://github.com/tlaplus/tlapm/issues/167 *)
    "Proof with INSTANCE step type";

    (* https://github.com/tlaplus/tlapm/issues/168 *)
    "Invalid parentheses use in jlist";

    (* https://github.com/tlaplus/tlapm/issues/169 *)
    "Label interfering with precedence";
    
    (* https://github.com/tlaplus/tlapm/issues/156 *)
    "Step Expression With Parameterized Subscript";

    (* https://github.com/tlaplus/tlapm/issues/170 *)
    "Implicit Proof Steps With Names";
    "Plus Proof Step With Name";

    (* https://github.com/tlaplus/tlapm/issues/172 *)
    "Invalid LOCAL Declaration of THEOREM";
    "Invalid LOCAL Declaration of ASSUME";
    "Invalid LOCAL Declaration of USE";
    
    (* https://github.com/tlaplus/tlapm/issues/173 *)
    "Decimal No Leading Zero (GH tlaplus/tlaplus #596)";

    (* https://github.com/tlaplus/tlapm/issues/173 *)
    "Nonfix Submodule Excl (GH tlaplus/tlaplus #GH884)";
    "Nonfix Double Exclamation Operator (GH TSTLA #GH97, GH tlaplus/tlaplus #884)";
  ]
let should_skip (test : syntax_test) : bool =
  List.mem test.info.path [
    "syntax_corpus/assume-prove.txt";
    "syntax_corpus/case.txt";
    "syntax_corpus/disjlist.txt";
    "syntax_corpus/except.txt";
    "syntax_corpus/expressions.txt";
    "syntax_corpus/fairness.txt";
    "syntax_corpus/functions.txt";
    "syntax_corpus/if_then_else.txt";
    "syntax_corpus/infix_op.txt";
    "syntax_corpus/jlist.txt";
    "syntax_corpus/labels.txt";
    "syntax_corpus/let_in.txt";
    "syntax_corpus/modules.txt";
    "syntax_corpus/number.txt";
    "syntax_corpus/operators.txt";
    "syntax_corpus/postfix_op.txt";
    "syntax_corpus/prefix_op.txt";
    "syntax_corpus/proofs.txt";
    "syntax_corpus/quantification.txt";
    "syntax_corpus/records.txt";
    "syntax_corpus/recursive.txt";
    "syntax_corpus/sets.txt";
    "syntax_corpus/step_expressions.txt";
    "syntax_corpus/string.txt";
    "syntax_corpus/subexpressions.txt";
    "syntax_corpus/tuples.txt";
    "syntax_corpus/use_or_hide.txt";
  ] || List.mem test.info.name [
    (* Jlist terminated by single line comment omitted in TLAPM AST *)
    "Keyword-Unit-Terminated Conjlist";
  ]

let tests = "Standardized syntax test corpus" >::: (
  get_all_tests_under "syntax_corpus"
  |> List.map (fun test ->
    Format.sprintf "[%s] %s" test.info.path test.info.name >::
    (fun _ ->
      skip_if test.skip "Test has skip attribute";
      skip_if (should_skip test) "Skip file";
      match test.test with
      | Error_test input -> (
        match parse input with
        | None -> assert_bool "Expected error test to fail" (not (expect_failure test))
        | Some _ -> assert_bool "Expected parse failure" (expect_failure test)
      )
      | Expected_test (input, expected) -> (
          match parse input with
          | None -> assert_bool "Expected parse success" (expect_failure test)
          | Some tlapm_output ->
            let actual = tlapm_output |> translate_module |> ts_node_to_sexpr in
            if Sexp.equal expected actual
            then assert_bool "Expected parse test to fail" (not (expect_failure test))
            else
              let open Sexp_diff in
              let diff = Algo.diff ~original:expected ~updated:actual () in
              let options = Display.Display_options.(create Layout.Single_column) in
              let text = Display.display_with_ansi_colors options diff in
              assert_bool text (expect_failure test)
      )
    )
  )
)

let _ = run_test_tt_main tests
