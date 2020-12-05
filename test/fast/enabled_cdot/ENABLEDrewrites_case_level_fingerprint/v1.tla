-------------- MODULE temp --------------
(* Test that changing the level of the test expression in a `CASE` conditional
also changes the result of the proof directive `ENABLEDrewrites`.
*)
EXTENDS TLAPS


VARIABLE x


p1 == x
a1 == x'


THEOREM (ENABLED CASE p1 -> a1) = CASE p1 -> ENABLED a1
BY ENABLEDrewrites

================================================================================
