------------------ MODULE ENABLEDaxioms_conj_visible_actions_test --------------
(* Test that when in `ENABLED (A /\ B)` the operators are visible, but have
primed variables in common, then the proof directive `ENABLEDaxioms` does not
distribute `ENABLED` over conjunction.
*)
EXTENDS TLAPS


VARIABLE x


A == x'
B == x'


THEOREM ENABLED (A /\ B) <=> (ENABLED A /\ ENABLED B)
BY ENABLEDaxioms DEF A, B

================================================================================
stderr: obligations failed
