------------ MODULE temp ----------
(* Test that changing the level of the right-hand side of equality within
`ENABLED` also changes the result of the proof directive `ENABLEDrewrites`.
*)
EXTENDS TLAPS


VARIABLE x


A == x


THEOREM (ENABLED (x' = A)) = TRUE
BY ENABLEDrewrites

================================================================================
