-------------------- MODULE temp ---------------
(* Test that fingerprints do not affect the correctness of `ExpandENABLED`
when the levels of operators change.
*)
EXTENDS TLAPS


VARIABLE x


A == x


THEOREM ENABLED (x' /\ A) = (\E u:  u /\ A)
BY ExpandENABLED

================================================================================
