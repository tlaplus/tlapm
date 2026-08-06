open Test_utils

(** This is only to understand better how subst works.

    - Option 1 (This works, but too complex because of the negative shift?):

    [Subst.(bumpn 3 (compose (shift (-3)) (scons repl_e (shift 4))))]

    - Option 2 (More explicit?)

    [Subst.( scons (T.Ix 1 |> np) (scons (T.Ix 2 |> np) (scons (T.Ix 3 |> np)
     (scons repl_e (shift 4)))))]

    - Option 3, a helper based on 2.

    [(subst_n 4 repl_e)] *)
let test_subst () =
  let open Tlapm_lib in
  let module Deque = Util.Deque in
  let np = Property.noprops in
  let const n = Expr.T.Fresh (n |> np, Shape_expr, Constant, Unbounded) |> np in
  let cx = Deque.empty in
  let cx = Deque.snoc cx (const "A") in
  let cx = Deque.snoc cx (const "B") in
  let cx = Deque.snoc cx (const "C") in
  let cx = Deque.snoc cx (const "D") in
  let cx =
    (* This is (C \/ D), (Ix=1) *)
    Deque.snoc cx
      Expr.T.(
        Fact
          ( Apply (Internal Builtin.Disj |> np, [ Ix 2 |> np; Ix 1 |> np ]) |> np,
            Visible,
            Always )
        |> np)
  in
  let pp_ex = Expr.Fmt.(pp_print_expr (cx, Ctx.dot)) in
  (* ------ That's the helper to replace particular symbol by index
     with an sub-expression residing at the same level. -----------------
  *)
  let subst_list (subs : (int * Expr.T.expr) list) =
    let open Expr in
    let rec loop i subs =
      match subs with
      | [] -> Subst.shift (i - 1)
      | (n, r) :: subs when i = n -> Subst.(scons r (loop (i + 1) subs))
      | subs -> Subst.scons (T.Ix i |> np) (loop (i + 1) subs)
    in
    subs |> List.sort (fun a b -> Int.compare (fst a) (fst b)) |> loop 1
  in
  (* ------ Find the replacement expression. ---------------------------- *)
  let repl_e =
    (* Lookup the fact, take its expr, shift it to the current context. *)
    let open Expr in
    let repl_ix = 1 in
    (match Expr.T.get_val_from_id cx repl_ix |> Property.unwrap with
      | T.Fact (e, _, _) -> e
      | _ -> assert false)
    |> Subst.app_expr (Subst.shift repl_ix)
  in
  Alcotest.(
    check string "replacement" {|C \/ D|} (Fmt.to_to_string pp_ex repl_e));
  (* ------ Check if works with basic expr. ------------------------------ *)
  begin
    let e =
      (* This is (A /\ B). *)
      Expr.T.(
        Apply (Internal Builtin.Conj |> np, [ Ix 5 |> np; Ix 4 |> np ]) |> np)
    in
    Alcotest.(
      check string "before subst, basic" {|A /\ B|} (Fmt.to_to_string pp_ex e));
    let e' = Expr.Subst.app_expr (subst_list [ (4, repl_e) ]) e in
    Alcotest.(
      check string "after subst, quant" {|A /\ (C \/ D)|}
        (Fmt.to_to_string pp_ex e'))
  end;
  (* ------ Check if works with quantifiers ------------------------------ *)
  begin
    let e =
      (* This is \A x: \E y: (A /\ B). *)
      Expr.T.(
        Quant
          ( Forall,
            [ ("x" |> np, Constant, No_domain) ],
            Quant
              ( Exists,
                [ ("y" |> np, Constant, No_domain) ],
                Apply (Internal Builtin.Conj |> np, [ Ix 7 |> np; Ix 6 |> np ])
                |> np )
            |> np ))
      |> np
    in
    Alcotest.(
      check string "before subst, quant" {|\A x : \E y : A /\ B|}
        (Fmt.to_to_string pp_ex e));
    let e' = Expr.Subst.app_expr (subst_list [ (4, repl_e) ]) e in
    Alcotest.(
      check string "after subst, quant" {|\A x : \E y : A /\ (C \/ D)|}
        (Fmt.to_to_string pp_ex e'))
  end;
  (* ------ Check multiple symbols can be replaced. ------------------------------ *)
  begin
    let e =
      (* This is \A x: (A /\ B /\ C). *)
      Expr.T.(
        Quant
          ( Forall,
            [ ("x" |> np, Constant, No_domain) ],
            Apply
              ( Internal Builtin.Conj |> np,
                [
                  Apply (Internal Builtin.Conj |> np, [ Ix 6 |> np; Ix 5 |> np ])
                  |> np;
                  Ix 4 |> np;
                ] )
            |> np ))
      |> np
    in
    Alcotest.(
      check string "before subst, multi" {|\A x : A /\ B /\ C|}
        (Fmt.to_to_string pp_ex e));
    let s =
      subst_list
        [
          ( 3,
            Expr.T.(
              Apply
                ( Internal Builtin.Plus |> np,
                  [ Ix 4 |> np; Num ("1", "") |> np ] ))
            |> np );
          (4, repl_e);
        ]
    in
    Alcotest.(
      check string "subst, multi" {|[??? FACT ??? . D . B + 1 . C \/ D . ^4]|}
        ((Fmt.to_to_string (Expr.Subst.pp_print_sub (cx, Ctx.dot))) s));
    let e' =
      (* B (Ix=4) ==> (C \/ D)
         C (Ix=3) ==> (B + 1)
      *)
      Expr.Subst.app_expr s e
    in
    Alcotest.(
      check string "after subst, multi" {|\A x : A /\ (C \/ D) /\ B + 1|}
        (Fmt.to_to_string pp_ex e'))
  end;
  ()

let test_pattern_match () =
  let lsp = lsp_init () in
  let text =
    {|
    ---- MODULE a ----
    C == 123
    THEOREM T == TRUE
    THEOREM
        ASSUME NEW DECOMPOSITION_RULE,
            NEW A, NEW B, NEW Q,
            A \/ B
        PROVE Q
    PROOF
        <1>1. ASSUME A PROVE Q
        <1>2. CASE B
        <1>q. QED BY <1>1, <1>2

    \* Some context.
    INSTANCE  Naturals
    VARIABLE x
    StepA == x' = x + 1
    StepB == x' = x + 2
    StepC == x' = x + 3
    Next == StepA \/ StepB \/ StepC
    Inv == x \in Nat

    \* The theorem to prove.
    LEMMA ApplyItHere == Inv /\ Next => Inv'
        <1>1. SUFFICES ASSUME Inv, Next PROVE Inv' OBVIOUS
        <1>q. QED BY DEF Next
    ====
    |}
  in
  let expected =
    {|
    ---- MODULE a ----
    C == 123
    THEOREM T == TRUE
    THEOREM
        ASSUME NEW DECOMPOSITION_RULE,
            NEW A, NEW B, NEW Q,
            A \/ B
        PROVE Q
    PROOF
        <1>1. ASSUME A PROVE Q
        <1>2. CASE B
        <1>q. QED BY <1>1, <1>2

    \* Some context.
    INSTANCE  Naturals
    VARIABLE x
    StepA == x' = x + 1
    StepB == x' = x + 2
    StepC == x' = x + 3
    Next == StepA \/ StepB \/ StepC
    Inv == x \in Nat

    \* The theorem to prove.
    LEMMA ApplyItHere == Inv /\ Next => Inv'
        <1>1. SUFFICES ASSUME Inv, Next PROVE Inv' OBVIOUS
        <1>2. ASSUME StepA \/ StepB
              PROVE  Inv'
        <1>3. CASE StepC
        <1>q. QED BY <1>2, <1>3 DEF Next
    ====
    |}
  in
  let actual = lsp_ca ~lsp ~text ~line:26 "⤮ Decompose by rule" in
  check_multiline_diff_td ~title:"refactoring output" ~expected ~actual;
  lsp_stop lsp

let test_goal_cap () =
  let lsp = lsp_init () in
  let text =
    {|
    ---- MODULE a ----
    THEOREM
        ASSUME NEW DECOMPOSITION_RULE,
            NEW x, NEW A, NEW B, NEW Q
        PROVE x \in A \cap B
    PROOF
        <1>1. x \in A
        <1>2. x \in B
        <1>q. QED BY <1>1, <1>2

    LEMMA \A x : x \in {1, 2} \cap {2, 3}
        <1>1. TAKE x
        <1>q. QED OBVIOUS
    ====
    |}
  in
  let expected =
    {|
    ---- MODULE a ----
    THEOREM
        ASSUME NEW DECOMPOSITION_RULE,
            NEW x, NEW A, NEW B, NEW Q
        PROVE x \in A \cap B
    PROOF
        <1>1. x \in A
        <1>2. x \in B
        <1>q. QED BY <1>1, <1>2

    LEMMA \A x : x \in {1, 2} \cap {2, 3}
        <1>1. TAKE x
        <1>2. x \in {1, 2}
        <1>3. x \in {2, 3}
        <1>q. QED BY <1>2, <1>3
    ====
    |}
  in
  let actual = lsp_ca ~lsp ~text ~line:13 "⤮ Decompose by rule" in
  check_multiline_diff_td ~title:"refactoring output" ~expected ~actual;
  lsp_stop lsp

let test_assm_set_map () =
  let lsp = lsp_init () in
  let text =
    {|
    ---- MODULE a ----
    EXTENDS Naturals
    THEOREM XTh0 == TRUE
    THEOREM
        ASSUME NEW DECOMPOSITION_RULE,
            NEW x, NEW f(_), NEW S, NEW Q,
            x \in {f(y) : y \in S}
        PROVE Q
    PROOF
        <1>1. PICK y \in S : x = f(y) OBVIOUS
        <1>q. QED BY <1>1, XTh0

    add(a) == a + a
    LEMMA ASSUME NEW j, j \in { add(i) : i \in {1, 2} } PROVE TRUE
        <1>q. QED OBVIOUS
    ====
    |}
  in
  let expected =
    {|
    ---- MODULE a ----
    EXTENDS Naturals
    THEOREM XTh0 == TRUE
    THEOREM
        ASSUME NEW DECOMPOSITION_RULE,
            NEW x, NEW f(_), NEW S, NEW Q,
            x \in {f(y) : y \in S}
        PROVE Q
    PROOF
        <1>1. PICK y \in S : x = f(y) OBVIOUS
        <1>q. QED BY <1>1, XTh0

    add(a) == a + a
    LEMMA ASSUME NEW j, j \in { add(i) : i \in {1, 2} } PROVE TRUE
        <1>1. PICK y \in {1, 2} : j = add(y) OBVIOUS
        <1>q. QED BY <1>1, XTh0
    ====
    |}
  in
  let actual = lsp_ca ~lsp ~text ~line:15 "⤮ Decompose by rule" in
  check_multiline_diff_td ~title:"refactoring output" ~expected ~actual;
  lsp_stop lsp

let test_cases =
  let open Alcotest in
  [
    test_case "How Subst works" `Quick test_subst;
    test_case "Experiments" `Quick test_pattern_match;
    test_case "Goal: x ∈ A ∩ B" `Quick test_goal_cap;
    test_case "Assm: x ∈ {f(y) : y ∈ S}" `Quick test_assm_set_map;
  ]
