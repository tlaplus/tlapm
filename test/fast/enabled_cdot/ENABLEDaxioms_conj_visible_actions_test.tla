------------------ MODULE ENABLEDaxioms_conj_visible_actions_test --------------
(* Test that when in `ENABLED (A /\ B)` the operators are visible, then the
proof directive `ENABLEDaxioms` distributes `ENABLED` over conjunction.
*)
EXTENDS TLAPS


VARIABLE x, y


A == x'
B == y'


THEOREM ENABLED (A /\ B) <=> (ENABLED A /\ ENABLED B)
BY ENABLEDaxioms DEF A, B

================================================================================
