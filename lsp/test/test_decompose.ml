open Test_utils

let test_to_sub_steps () =
  let lsp = lsp_init () in
  let text =
    {|
    ---- MODULE test ----
    THEOREM Test ==
        ASSUME NEW S PROVE \A a, b \in S : a
    PROOF
      <1>1. QED OBVIOUS
    ====
    |}
  in
  let expected =
    {|
    ---- MODULE test ----
    THEOREM Test ==
        ASSUME NEW S PROVE \A a, b \in S : a
    PROOF
      <1>1. QED
        <2>1. QED OBVIOUS
    ====
    |}
  in
  let actual = lsp_ca ~lsp ~text ~line:5 "⤮ To sub-steps" in
  check_multiline_diff_td ~title:"refactoring output" ~expected ~actual;
  lsp_stop lsp

let test_expand_def () =
  let lsp = lsp_init () in
  let text =
    {|
    ---- MODULE test ----
    Some == TRUE
    THEOREM Test ==
        ASSUME NEW S PROVE \A a, b \in Some : a
    PROOF
      <1>1. QED OBVIOUS
    ====
    |}
  in
  let expected =
    {|
    ---- MODULE test ----
    Some == TRUE
    THEOREM Test ==
        ASSUME NEW S PROVE \A a, b \in Some : a
    PROOF
      <1>1. QED BY DEF Some
    ====
    |}
  in
  let actual = lsp_ca ~lsp ~text ~line:6 "→ Expand Some" in
  check_multiline_diff_td ~title:"refactoring output" ~expected ~actual;
  lsp_stop lsp

let test_cases =
  let open Alcotest in
  List.concat
    [
      [
        test_case "To-steps" `Quick test_to_sub_steps;
        test_case "Expand DEF" `Quick test_expand_def;
      ];
      Test_decompose_goal.test_cases;
      Test_decompose_assm.test_cases;
    ]
