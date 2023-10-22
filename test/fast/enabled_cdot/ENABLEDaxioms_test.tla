------------------------- MODULE ENABLEDaxioms_test ----------------------------
(* Unit tests for the implementation of axioms about `ENABLED`. *)
EXTENDS TLAPS


(* This statement declares two variables. *)
VARIABLE x, y


P == x = 1  (* A state predicate. *)
A == x' = 1  (* An action with a primed variable. *)
B == y' = 1  (* Another action with primed variables, such that the set of
    primed variables of action A is disjoint from the set of primed variables
    of action B. *)
R(z) == z  (* An operator that takes a parameter. *)


--------------------------------------------------------------------------------
(* ENABLED distributes over disjunction.

In more detail, we deduce
    ENABLED (A \/ B) <=> (ENABLED A \/ ENABLED B)
*)
THEOREM ENABLED (A \/ B) <=> (ENABLED A \/ ENABLED B)
BY ENABLEDaxioms

THEOREM (ENABLED A \/ ENABLED B) <=> ENABLED (A \/ B)
BY ENABLEDaxioms


--------------------------------------------------------------------------------
(* ENABLED commutes with existential quantification.

This axiom allows renaming of the bound constant, and
requires that the quantifier bounds be identical and
state predicates or constants,
and that the quantified expressions be identical.
*)
THEOREM ENABLED (\E i \in {1, 2}:  R(i)) <=>
        \E i \in {1, 2}:  ENABLED R(i)
BY ENABLEDaxioms

THEOREM (\E i \in {1, 2}:  ENABLED R(i)) <=>
        ENABLED (\E i \in {1, 2}:  R(i))
BY ENABLEDaxioms


--------------------------------------------------------------------------------
(* ENABLED distributes over conjunction of actions
with disjoint sets of primed variables.

In more detail, from
    A and B have disjoint sets of primed variables
we deduce
    ENABLED (A /\ B) <=> (ENABLED A /\ ENABLED B)
The premise that A and B have disjoint sets of primed variables
is automatically checked by TLAPS.
The
*)
THEOREM ENABLED (A /\ B) <=> (ENABLED A /\ ENABLED B)
BY ENABLEDaxioms DEF A, B

THEOREM (ENABLED A /\ ENABLED B) <=> ENABLED (A /\ B)
BY ENABLEDaxioms DEF A, B


--------------------------------------------------------------------------------
(* State predicates can be pulled outside of ENABLED.

In more detail, from
    P has at most state level
we deduce
    ENABLED (P /\ A) <=> (P /\ ENABLED A)
The premise about the level of P is automatically checked by TLAPS.
*)
THEOREM ENABLED (P /\ A) <=> (P /\ ENABLED A)
BY ENABLEDaxioms

THEOREM (P /\ ENABLED A) <=> ENABLED (P /\ A)
BY ENABLEDaxioms


================================================================================
