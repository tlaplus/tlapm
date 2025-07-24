-------------- MODULE temp --------------
(* Test that changing the level of the conjuncts in a conjunction within
`ENABLED` also changes the result of the proof directive `ENABLEDrewrites`.
*)
EXTENDS TLAPS


VARIABLE x, y


A == x
B == y'


THEOREM (ENABLED (A /\ B)) = (A /\ ENABLED B)
BY ENABLEDrewrites DEF B

================================================================================
