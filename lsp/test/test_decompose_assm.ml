open Test_utils

(** {1 Assm: ∧} *)

let test_assm_conj_basic () =
  let lsp = lsp_init () in
  let text =
    {|
    ---- MODULE test ----
    THEOREM Test ==
        ASSUME NEW a, NEW b, NEW c, a /\ b /\ c PROVE TRUE
    PROOF
      <1> QED OBVIOUS
    ====
    |}
  in
  let expected =
    {|
    ---- MODULE test ----
    THEOREM Test ==
        ASSUME NEW a, NEW b, NEW c, a /\ b /\ c PROVE TRUE
    PROOF
      <1>1. a OBVIOUS
      <1>2. b OBVIOUS
      <1>3. c OBVIOUS
      <1> QED BY <1>1, <1>2, <1>3
    ====
    |}
  in
  let actual = lsp_ca ~lsp ~text ~line:5 "⤮ Split (∧): a /\\\\ b /\\\\ c" in
  check_multiline_diff_td ~title:"refactoring output" ~expected ~actual;
  lsp_stop lsp

(** {1 Assm: ∨} *)

let test_assm_disj_basic () =
  let lsp = lsp_init () in
  let text =
    {|
    ---- MODULE test ----
    THEOREM Test ==
        ASSUME NEW a, NEW b, NEW c, a \/ b \/ c PROVE TRUE
    PROOF
      <1> QED OBVIOUS
    ====
    |}
  in
  let expected =
    {|
    ---- MODULE test ----
    THEOREM Test ==
        ASSUME NEW a, NEW b, NEW c, a \/ b \/ c PROVE TRUE
    PROOF
      <1>1. CASE a BY <1>1
      <1>2. CASE b BY <1>2
      <1>3. CASE c BY <1>3
      <1> QED BY <1>1, <1>2, <1>3
    ====
    |}
  in
  let actual =
    lsp_ca ~lsp ~text ~line:5 "⤮ Case split (∨): a \\\\/ b \\\\/ c"
  in
  check_multiline_diff_td ~title:"refactoring output" ~expected ~actual;
  lsp_stop lsp

(** {1 Assm: ⇒} *)

let test_assm_implies_basic () =
  let lsp = lsp_init () in
  let text =
    {|
    ---- MODULE test ----
    THEOREM Test ==
        ASSUME NEW a, NEW b, NEW c, a => b => c PROVE c
    PROOF
      <1> QED OBVIOUS
    ====
    |}
  in
  let expected =
    {|
    ---- MODULE test ----
    THEOREM Test ==
        ASSUME NEW a, NEW b, NEW c, a => b => c PROVE c
    PROOF
      <1>1. c
            <2>1. a OBVIOUS
            <2>2. b OBVIOUS
            <2>3. QED BY <2>1, <2>2
      <1> QED BY <1>1
    ====
    |}
  in
  let actual = lsp_ca ~lsp ~text ~line:5 "⤮ Use (⇒): a => (b => c)" in
  check_multiline_diff_td ~title:"refactoring output" ~expected ~actual;
  lsp_stop lsp

(** {1 Assm: ∀} *)

let test_assm_forall_basic () =
  let lsp = lsp_init () in
  let text =
    {|
    ---- MODULE test ----
    THEOREM Test ==
      ASSUME NEW S, NEW P(_), \A x \in S : P(x) PROVE \E x \in S : P(x)
    PROOF
      <1> QED OBVIOUS
    ====
    |}
  in
  let expected =
    {|
    ---- MODULE test ----
    THEOREM Test ==
      ASSUME NEW S, NEW P(_), \A x \in S : P(x) PROVE \E x \in S : P(x)
    PROOF
      <1>1. PICK x \in S : P(x)
            <2>1. \E x \in S : TRUE OBVIOUS
            <2>2. QED BY <2>1
      <1> QED BY <1>1
    ====
    |}
  in
  let actual = lsp_ca ~lsp ~text ~line:5 "⤮ Use (∀): \\\\A x \\\\in S : P(x)" in
  check_multiline_diff_td ~title:"refactoring output" ~expected ~actual;
  lsp_stop lsp

(** {1 Assm: ∃} *)

let test_assm_exists_basic () =
  let lsp = lsp_init () in
  let text =
    {|
    ---- MODULE test ----
    THEOREM Test ==
      ASSUME NEW S, NEW P(_), \E x \in S : P(x) PROVE \A x \in S : P(x)
    PROOF
      <1> QED OBVIOUS
    ====
    |}
  in
  let expected =
    {|
    ---- MODULE test ----
    THEOREM Test ==
      ASSUME NEW S, NEW P(_), \E x \in S : P(x) PROVE \A x \in S : P(x)
    PROOF
      <1>1. PICK x \in S : P(x) OBVIOUS
      <1> QED BY <1>1
    ====
    |}
  in
  let actual = lsp_ca ~lsp ~text ~line:5 "⤮ Use (∃): \\\\E x \\\\in S : P(x)" in
  check_multiline_diff_td ~title:"refactoring output" ~expected ~actual;
  lsp_stop lsp

let test_cases =
  let open Alcotest in
  [
    test_case "Assm ∧, basic" `Quick test_assm_conj_basic;
    test_case "Assm ∨, basic" `Quick test_assm_disj_basic;
    test_case "Assm ⇒, basic" `Quick test_assm_implies_basic;
    test_case "Assm ∀, basic" `Quick test_assm_forall_basic;
    test_case "Assm ∃, basic" `Quick test_assm_exists_basic;
  ]
