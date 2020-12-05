------------ MODULE temp -------------
(* Test that changing the level of the test expression in a ternary conditional
also changes the result of the proof directive `ENABLEDrewrites`.
*)
EXTENDS TLAPS


VARIABLE x, y


A == x
B == x'
C == y'


THEOREM (ENABLED (IF A THEN B ELSE C)) = IF A THEN ENABLED B ELSE ENABLED C
BY ENABLEDrewrites

================================================================================
