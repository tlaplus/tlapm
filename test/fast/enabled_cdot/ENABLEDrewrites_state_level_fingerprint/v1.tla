-------------- MODULE temp -------------
(* Test that changing the level of the argument of `ENABLED`
also changes the result of the proof directive `ENABLEDrewrites`.
*)
EXTENDS TLAPS


VARIABLE x


A == x


THEOREM (ENABLED A) = A
BY ENABLEDrewrites

================================================================================
