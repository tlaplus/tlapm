-------------- MODULE temp --------------
EXTENDS TLAPS


VARIABLE x, y


A == x'
B == y'


THEOREM (ENABLED (A /\ B)) = (A /\ ENABLED B)
BY ENABLEDrewrites DEF B

================================================================================
