open Test_utils

(** {1 Misc} *)

let test_lsp_init () = lsp_init () |> lsp_stop

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

(** {1 Goal: ∀} *)

let test_goal_forall_bounded () =
  let lsp = lsp_init () in
  let text =
    {|
    ---- MODULE test ----
    THEOREM Test ==
        ASSUME NEW S PROVE \A a, b \in S : a
    PROOF
      <1> QED
    ====
    |}
  in
  let expected =
    {|
    ---- MODULE test ----
    THEOREM Test ==
        ASSUME NEW S PROVE \A a, b \in S : a
    PROOF
      <1> TAKE a, b \in S
      <1> QED
    ====
    |}
  in
  let actual = lsp_ca ~lsp ~text ~line:5 "⤮ Decompose goal (∀)" in
  check_multiline_diff_td ~title:"refactoring output" ~expected ~actual;
  lsp_stop lsp

let test_goal_forall_unbounded () =
  let lsp = lsp_init () in
  let text =
    {|
    ---- MODULE test ----
    THEOREM Test ==
        \A a, b : a
    PROOF
      <1> QED
    ====
    |}
  in
  let expected =
    {|
    ---- MODULE test ----
    THEOREM Test ==
        \A a, b : a
    PROOF
      <1> TAKE a, b
      <1> QED
    ====
    |}
  in
  let actual = lsp_ca ~lsp ~text ~line:5 "⤮ Decompose goal (∀)" in
  check_multiline_diff_td ~title:"refactoring output" ~expected ~actual;
  lsp_stop lsp

let test_goal_forall_name_clash () =
  let lsp = lsp_init () in
  let text =
    {|
    ---- MODULE test ----
    THEOREM Test ==
      ASSUME NEW P(_), NEW S
      PROVE \A a \in S : P(a)
    PROOF
      <1> a == TRUE
          a_1 == TRUE
      <1> HIDE DEF a, a_1
      <1>q. QED OBVIOUS
    ====
    |}
  in
  let expected =
    {|
    ---- MODULE test ----
    THEOREM Test ==
      ASSUME NEW P(_), NEW S
      PROVE \A a \in S : P(a)
    PROOF
      <1> a == TRUE
          a_1 == TRUE
      <1> HIDE DEF a, a_1
      <1> TAKE a_2 \in S
      <1>q. QED OBVIOUS
    ====
    |}
  in
  let actual = lsp_ca ~lsp ~text ~line:9 "⤮ Decompose goal (∀)" in
  check_multiline_diff_td ~title:"refactoring output" ~expected ~actual;
  lsp_stop lsp

(** {1 Goal: ∃} *)

let test_goal_exists_basic () =
  let lsp = lsp_init () in
  let text =
    {|
    ---- MODULE test ----
    THEOREM Test ==
      ASSUME NEW P(_, _), NEW S
      PROVE \E a, b \in S : P(a, b)
    PROOF
      <1>3. QED
    ====
    |}
  in
  let expected =
    {|
    ---- MODULE test ----
    THEOREM Test ==
      ASSUME NEW P(_, _), NEW S
      PROVE \E a, b \in S : P(a, b)
    PROOF
      <1> a == "TODO: Replace this with actual witness for a"
      <1> b == "TODO: Replace this with actual witness for b"
      <1> HIDE DEFS a, b
      <1>4. a \in S
      <1>5. b \in S
      <1> WITNESS a \in S, b \in S
      <1>3. QED
    ====
    |}
  in
  let actual = lsp_ca ~lsp ~text ~line:6 "⤮ Decompose goal (∃)" in
  check_multiline_diff_td ~title:"refactoring output" ~expected ~actual;
  lsp_stop lsp

let () =
  let open Alcotest in
  run "tlapm_lsp"
    [
      ( "meta",
        [
          test_case "Init" `Quick test_lsp_init;
          test_case "To-steps" `Quick test_to_sub_steps;
          test_case "Goal ∀, bounded" `Quick test_goal_forall_bounded;
          test_case "Goal ∀, unbounded" `Quick test_goal_forall_unbounded;
          test_case "Goal ∀, name clash" `Quick test_goal_forall_name_clash;
          test_case "Goal ∃, basic" `Quick test_goal_exists_basic;
        ] );
    ]
