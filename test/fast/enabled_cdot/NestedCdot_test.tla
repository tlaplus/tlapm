---------------------------- MODULE NestedCdot_test ----------------------------
(* Test proof directive `ExpandCdot` with nested occurrences of `\cdot`. *)
EXTENDS Naturals


Zenon == TRUE (*{ by (prover:"zenon") }*)
ExpandCdot == TRUE  (*{ by (prover:"expandcdot") }*)
AutoUSE == TRUE  (*{ by (prover:"autouse") }*)

--------------------------------------------------------------------------------

THEOREM
    ASSUME VARIABLE x
    PROVE (
        (x = 0 /\ x' = 1) \cdot (
            ((x = 1 /\ x' = 2) \cdot (x = 2 /\ x' = 3))  )
        )
        =
        ((x = 0 /\ x' = 1) \cdot (x = 1) /\ (x' = 3))
PROOF
BY ExpandCdot, Zenon


THEOREM
    ASSUME VARIABLE x
    PROVE (
        ((x = 0 /\ x' = 1) \cdot (x = 1) /\ (x' = 3)) )
        <=>
        ((x = 0) /\ (x' = 3))
PROOF
BY ExpandCdot, Zenon

--------------------------------------------------------------------------------
VARIABLE x


A == (x = 0 /\ x' = 1) \cdot (
    ((x = 1 /\ x' = 2) \cdot (x = 2 /\ x' = 3))  )


THEOREM  ((x = 0) /\ (x' = 3))  =>  A
PROOF
BY ExpandCdot, Zenon DEF A
--------------------------------------------------------------------------------

P == (x = 1 /\ x' = 2) \cdot (x = 2 /\ x' = 3)
Q == (x = 0 /\ x' = 1) \cdot P


THEOREM  ((x = 0) /\ (x' = 3))  =>  Q
PROOF
BY ExpandCdot, Zenon, AutoUSE DEF Q
================================================================================
