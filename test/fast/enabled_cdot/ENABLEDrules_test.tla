--------------------------- MODULE ENABLEDrules_test ---------------------------
(* Unit tests for the implementation of proof rules about `ENABLED`. *)
EXTENDS TLAPS


VARIABLE x  (* This statement declares a variable. *)


A == x' = 1 /\ x = 1  (* An action. *)
B == x' = x /\ x = 1  (* An action equivalent to action A. *)

C == x' = 1  (* An action. *)
D == x' = 1 \/ x' = 2  (* An action implied by action C. *)


--------------------------------------------------------------------------------
(* Equivalence of actions entails equivalence of their enabledness.

In more detail, from
    A <=> B
we deduce
    ENABLED A <=> ENABLED B
The premise A <=> B needs to be provable where ENABLEDrules is invoked.

The proof step where ENABLEDrules appears should not depend (directly or
indirectly) on any assumption with level higher than constant or state level
(except through only intermediate steps that have constant or state level).
*)
THEOREM
    ENABLED A <=> ENABLED B
BY ENABLEDrules DEF A, B


--------------------------------------------------------------------------------
(* Implication of actions entails implication of their enabledness.

In more detail, from
    A => B
we deduce
    ENABLED A => ENABLED B
The premise A => B needs to be provable where ENABLEDrules is invoked.

The proof step where ENABLEDrules appears should not depend (directly or
indirectly) on any assumption with level higher than constant or state level
(except through only intermediate steps that have constant or state level).
*)
THEOREM
    ENABLED C => ENABLED D
BY ENABLEDrules DEF C, D


================================================================================
