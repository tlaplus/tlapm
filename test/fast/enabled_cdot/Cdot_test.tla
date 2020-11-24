---------------------------- MODULE Cdot_test ----------------------------------
(* Tests for the expansion of the operator \cdot. *)
(* EXTENDS TLAPS *)

(* The proof directives below are from the module `TLAPS`.
Including them here to compare the number of definitions
with when extending the module `TLAPS`.
*)

Zenon == TRUE (*{ by (prover:"zenon") }*)

ExpandENABLED == TRUE  (*{ by (prover:"expandenabled") }*)
ExpandCdot == TRUE  (*{ by (prover:"expandcdot") }*)
AutoUSE == TRUE  (*{ by (prover:"autouse") }*)


--------------------------------------------------------------------------------
(* Unit test with a single variable. *)

VARIABLE x

R == x' = TRUE

A == /\ x = FALSE
     /\ R

B == /\ x = TRUE
     /\ x' = FALSE

C == A \cdot B

D == /\ x = FALSE
     /\ x' = FALSE


THEOREM C <=> D
PROOF
BY ExpandCdot, Zenon DEF A, B, R, C, D


THEOREM C <=> D
PROOF
BY ExpandCdot, AutoUSE, Zenon DEF C, D


--------------------------------------------------------------------------------
(* Unit test with two variables. *)

VARIABLE y


A2 == /\ x = TRUE /\ y = FALSE
      /\ x' = FALSE /\ y' = TRUE

B2 == /\ x = FALSE /\ y = TRUE
      /\ x' = TRUE /\ y' = TRUE

C2 == A2 \cdot B2

D2 == /\ x = TRUE /\ y = FALSE
      /\ x' = TRUE /\ y' = TRUE


THEOREM C2 <=> D2
PROOF
BY ExpandCdot, Zenon DEF A2, B2, C2, D2


================================================================================
