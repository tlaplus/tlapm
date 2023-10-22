------------ MODULE temp -------------
EXTENDS TLAPS


VARIABLE x, y


A == x'
B == x'
C == y'


THEOREM (ENABLED (IF A THEN B ELSE C)) = IF A THEN ENABLED B ELSE ENABLED C
BY ENABLEDrewrites

================================================================================
