-------------------------- MODULE ENABLEDaxioms_conj_test ----------------------
(* Test a variety of cases for `ENABLED (A /\ B)` using the proof directive
`ENABLEDaxioms`.
*)
EXTENDS TLAPS


VARIABLE x, y


A == x'
B == y'
C == x


THEOREM ENABLED (A /\ B) <=> (ENABLED A /\ ENABLED B)
BY ENABLEDaxioms DEF A, B


(* symmetric to the previous theorem *)
THEOREM (ENABLED A /\ ENABLED B) <=> ENABLED (A /\ B)
BY ENABLEDaxioms DEF A, B


THEOREM ENABLED (A /\ C) <=> (ENABLED A /\ ENABLED C)
BY ENABLEDaxioms DEF A


(* symmetric to the previous theorem *)
THEOREM (ENABLED A /\ ENABLED C) <=> ENABLED (A /\ C)
BY ENABLEDaxioms DEF A


THEOREM ENABLED (B /\ C) <=> (ENABLED B /\ ENABLED C)
BY ENABLEDaxioms DEF B


(* symmetric to the previous theorem *)
THEOREM (ENABLED B /\ ENABLED C) <=> ENABLED (B /\ C)
BY ENABLEDaxioms DEF B

================================================================================
