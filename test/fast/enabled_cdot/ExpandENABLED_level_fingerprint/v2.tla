-------------------- MODULE temp ---------------
EXTENDS TLAPS


VARIABLE x


A == x'


THEOREM ENABLED (x' /\ A) = (\E u:  u /\ A)
BY ExpandENABLED

================================================================================
