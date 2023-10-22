------------------ MODULE ENABLEDaxioms_conj_hidden_actions_test ---------------
(* Test that when in `ENABLED (A /\ B)` the operator `A` is hidden and of
action level, then the proof directive `ENABLEDaxioms` does not distribute
`ENABLED` over conjunction.
*)
EXTENDS TLAPS


VARIABLE x, y


A == x'
B == y'


THEOREM ENABLED (A /\ B) <=> (ENABLED A /\ ENABLED B)
BY ENABLEDaxioms

================================================================================
stderr: obligations failed
