----------------- MODULE temp ----------------
EXTENDS TLAPS


VARIABLE x, y


A == x'
B == y'


THEOREM ENABLED (A /\ B) <=> (ENABLED A /\ ENABLED B)
BY ENABLEDaxioms DEF A

================================================================================
