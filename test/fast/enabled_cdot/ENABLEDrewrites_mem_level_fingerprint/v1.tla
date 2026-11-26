--------------- MODULE temp --------------
(* Test that changing the level of the right-hand side of set membership within
`ENABLED` also changes the result of the proof directive `ENABLEDrewrites`.
*)
EXTENDS TLAPS


VARIABLE x


A == x


THEOREM (ENABLED (x' \in A)) = (A # {})
BY ENABLEDrewrites

================================================================================
