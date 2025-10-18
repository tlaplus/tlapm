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

(** Here the \E is not immediate, but under a definition which is expanded. *)
let test_goal_exists_under_def () =
  let lsp = lsp_init () in
  let text =
    {|
    ---- MODULE test ----
    THEOREM Test ==
      ASSUME NEW P(_, _), NEW S
      PROVE \E a, b \in S : P(a, b)
    PROOF
      <1> DEFINE Tmp == \E a, b \in S : P(a, b)
      <1> SUFFICES Tmp OBVIOUS
      <1> HIDE DEF Tmp
      <1>4. QED BY DEF Tmp
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
      <1> DEFINE Tmp == \E a, b \in S : P(a, b)
      <1> SUFFICES Tmp OBVIOUS
      <1> HIDE DEF Tmp
      <1> a == "TODO: Replace this with actual witness for a"
      <1> b == "TODO: Replace this with actual witness for b"
      <1> HIDE DEFS a, b
      <1>5. a \in S
      <1>6. b \in S
      <1>7. USE DEF Tmp
      <1> WITNESS a \in S, b \in S
      <1>4. QED BY DEF Tmp
    ====
    |}
  in
  let actual = lsp_ca ~lsp ~text ~line:9 "⤮ Decompose goal (∃)" in
  check_multiline_diff_td ~title:"refactoring output" ~expected ~actual;
  lsp_stop lsp

(** Here the \E is not immediate, but under an expanded operator. *)
let test_goal_exists_under_op () =
  let lsp = lsp_init () in
  let text =
    {|
    ---- MODULE test ----
    THEOREM Test ==
      ASSUME NEW P(_, _), NEW S
      PROVE \E a, b \in S : P(a, b)
    PROOF
      <1> DEFINE D(X) == \E a, b \in X : P(a, b)
      <1> SUFFICES D(S) OBVIOUS
      <1> HIDE DEF D
      <1>4. QED BY DEF D
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
      <1> DEFINE D(X) == \E a, b \in X : P(a, b)
      <1> SUFFICES D(S) OBVIOUS
      <1> HIDE DEF D
      <1> a == "TODO: Replace this with actual witness for a"
      <1> b == "TODO: Replace this with actual witness for b"
      <1> HIDE DEFS a, b
      <1>5. a \in S
      <1>6. b \in S
      <1>7. USE DEF D
      <1> WITNESS a \in S, b \in S
      <1>4. QED BY DEF D
    ====
    |}
  in
  let actual = lsp_ca ~lsp ~text ~line:9 "⤮ Decompose goal (∃)" in
  check_multiline_diff_td ~title:"refactoring output" ~expected ~actual;
  lsp_stop lsp

let test_goal_exists_name_clash () =
  let lsp = lsp_init () in
  let text =
    {|
    ---- MODULE test ----
    THEOREM Test ==
      ASSUME NEW P(_, _), NEW S
      PROVE \E a, b \in S : P(a, b)
    PROOF
      <1> a == TRUE
      <1> a_1 == TRUE
      <1> HIDE DEF a, a_1
      <1>q. QED OBVIOUS
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
      <1> a == TRUE
      <1> a_1 == TRUE
      <1> HIDE DEF a, a_1
      <1> a_2 == "TODO: Replace this with actual witness for a_2"
      <1> b == "TODO: Replace this with actual witness for b"
      <1> HIDE DEFS a_2, b
      <1>1. a_2 \in S
      <1>2. b \in S
      <1> WITNESS a_2 \in S, b \in S
      <1>q. QED OBVIOUS
    ====
    |}
  in
  let actual = lsp_ca ~lsp ~text ~line:9 "⤮ Decompose goal (∃)" in
  check_multiline_diff_td ~title:"refactoring output" ~expected ~actual;
  lsp_stop lsp

(** {1 Goal: ⇒} *)

let test_goal_implies_basic () =
  let lsp = lsp_init () in
  let text =
    {|
    ---- MODULE test ----
    THEOREM Test ==
        ASSUME NEW a PROVE a => a
    PROOF
      <1>1. QED OBVIOUS
    ====
    |}
  in
  let expected =
    {|
    ---- MODULE test ----
    THEOREM Test ==
        ASSUME NEW a PROVE a => a
    PROOF
      <1>2. HAVE a
      <1>1. QED BY <1>2
    ====
    |}
  in
  let actual = lsp_ca ~lsp ~text ~line:5 "⤮ Decompose goal (⇒)" in
  check_multiline_diff_td ~title:"refactoring output" ~expected ~actual;
  lsp_stop lsp

(** {1 Goal: ∧} *)

let test_goal_conj_basic () =
  let lsp = lsp_init () in
  let text =
    {|
    ---- MODULE test ----
    THEOREM Test ==
      ASSUME NEW a, NEW b, NEW c PROVE a /\ b /\ c
    PROOF
      <1> QED OBVIOUS
    ====
    |}
  in
  let expected =
    {|
    ---- MODULE test ----
    THEOREM Test ==
      ASSUME NEW a, NEW b, NEW c PROVE a /\ b /\ c
    PROOF
      <1>1. a OBVIOUS
      <1>2. b OBVIOUS
      <1>3. c OBVIOUS
      <1> QED BY <1>1, <1>2, <1>3
    ====
    |}
  in
  let actual = lsp_ca ~lsp ~text ~line:5 "⤮ Decompose goal (∧)" in
  check_multiline_diff_td ~title:"refactoring output" ~expected ~actual;
  lsp_stop lsp

let test_goal_conj_list () =
  let lsp = lsp_init () in
  let text =
    {|
    ---- MODULE test ----
    THEOREM Test ==
      ASSUME NEW a, NEW b, NEW c PROVE
        /\ a
        /\ b /\ c
    PROOF
      <1> QED OBVIOUS
    ====
    |}
  in
  let expected =
    {|
    ---- MODULE test ----
    THEOREM Test ==
      ASSUME NEW a, NEW b, NEW c PROVE
        /\ a
        /\ b /\ c
    PROOF
      <1>1. a OBVIOUS
      <1>2. b OBVIOUS
      <1>3. c OBVIOUS
      <1> QED BY <1>1, <1>2, <1>3
    ====
    |}
  in
  let actual = lsp_ca ~lsp ~text ~line:7 "⤮ Decompose goal (∧)" in
  check_multiline_diff_td ~title:"refactoring output" ~expected ~actual;
  lsp_stop lsp

(** {1 Goal: ∨} *)

let test_goal_disj_basic_case2 () =
  let lsp = lsp_init () in
  let text =
    {|
    ---- MODULE test ----
    THEOREM Test ==
      ASSUME NEW a, NEW b, NEW c PROVE a \/ b \/ c
    PROOF
      <1> QED OBVIOUS
    ====
    |}
  in
  let expected =
    {|
    ---- MODULE test ----
    THEOREM Test ==
      ASSUME NEW a, NEW b, NEW c PROVE a \/ b \/ c
    PROOF
      <1>1. SUFFICES ASSUME ~a ,
                            ~c
                    PROVE  b
            OBVIOUS
      <1> QED BY <1>1
    ====
    |}
  in
  let actual = lsp_ca ~lsp ~text ~line:5 "⤮ Decompose goal (∨, case 2)" in
  check_multiline_diff_td ~title:"refactoring output" ~expected ~actual;
  lsp_stop lsp

let test_goal_disj_list_case3 () =
  let lsp = lsp_init () in
  let text =
    {|
    ---- MODULE test ----
    THEOREM Test ==
      ASSUME NEW a, NEW b, NEW c PROVE
        \/ a
        \/ b \/ c
    PROOF
      <1> QED OBVIOUS
    ====
    |}
  in
  let expected =
    {|
    ---- MODULE test ----
    THEOREM Test ==
      ASSUME NEW a, NEW b, NEW c PROVE
        \/ a
        \/ b \/ c
    PROOF
      <1>1. SUFFICES ASSUME ~a ,
                            ~b
                    PROVE  c
            OBVIOUS
      <1> QED BY <1>1
    ====
    |}
  in
  let actual = lsp_ca ~lsp ~text ~line:7 "⤮ Decompose goal (∨, case 3)" in
  check_multiline_diff_td ~title:"refactoring output" ~expected ~actual;
  lsp_stop lsp

(** {1 Goal: ≡} *)

let test_goal_equiv_basic () =
  let lsp = lsp_init () in
  let text =
    {|
    ---- MODULE test ----
    THEOREM Test ==
      ASSUME NEW a, NEW b PROVE a <=> b
    PROOF
      <1> QED OBVIOUS
    ====
    |}
  in
  let expected =
    {|
    ---- MODULE test ----
    THEOREM Test ==
      ASSUME NEW a, NEW b PROVE a <=> b
    PROOF
      <1>1. a => b OBVIOUS
      <1>2. b => a OBVIOUS
      <1> QED BY <1>1, <1>2
    ====
    |}
  in
  let actual = lsp_ca ~lsp ~text ~line:5 "⤮ Decompose goal (≡)" in
  check_multiline_diff_td ~title:"refactoring output" ~expected ~actual;
  lsp_stop lsp

let test_goal_equiv_circular () =
  let lsp = lsp_init () in
  let text =
    {|
    ---- MODULE test ----
    THEOREM Test ==
      ASSUME NEW a, NEW b, NEW c PROVE a <=> b <=> c
    PROOF
      <1> QED OBVIOUS
    ====
    |}
  in
  let expected =
    {|
    ---- MODULE test ----
    THEOREM Test ==
      ASSUME NEW a, NEW b, NEW c PROVE a <=> b <=> c
    PROOF
      <1>1. a => b OBVIOUS
      <1>2. b => c OBVIOUS
      <1>3. c => a OBVIOUS
      <1> QED BY <1>1, <1>2, <1>3
    ====
    |}
  in
  let actual = lsp_ca ~lsp ~text ~line:5 "⤮ Decompose goal (≡)" in
  check_multiline_diff_td ~title:"refactoring output" ~expected ~actual;
  lsp_stop lsp

let () =
  let open Alcotest in
  run "tlapm_lsp"
    [
      ("meta", [ test_case "Init" `Quick test_lsp_init ]);
      ( "decompose",
        [
          test_case "To-steps" `Quick test_to_sub_steps;
          test_case "Goal ∀, bounded" `Quick test_goal_forall_bounded;
          test_case "Goal ∀, unbounded" `Quick test_goal_forall_unbounded;
          test_case "Goal ∀, name clash" `Quick test_goal_forall_name_clash;
          test_case "Goal ∃, basic" `Quick test_goal_exists_basic;
          test_case "Goal ∃, under def" `Quick test_goal_exists_under_def;
          test_case "Goal ∃, under op" `Quick test_goal_exists_under_op;
          test_case "Goal ∃, name clash" `Quick test_goal_exists_name_clash;
          test_case "Goal ⇒, basic" `Quick test_goal_implies_basic;
          test_case "Goal ∧, basic" `Quick test_goal_conj_basic;
          test_case "Goal ∧, list" `Quick test_goal_conj_list;
          test_case "Goal ∨, basic, case 2" `Quick test_goal_disj_basic_case2;
          test_case "Goal ∨, list, case 3" `Quick test_goal_disj_list_case3;
          test_case "Goal ≡, basic" `Quick test_goal_equiv_basic;
          test_case "Goal ≡, circular" `Quick test_goal_equiv_circular;
        ] );
    ]
