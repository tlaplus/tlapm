---- MODULE 10_BasicStepProofTest ----
A == 0
B == 0
C == 0
THEOREM AB == A = B
PROOF BY ONLY DEFS A, B
THEOREM BC == B = C
PROOF BY ONLY DEFS B, C
THEOREM AC == A = C
PROOF
<1>a AB
<1>b BC
<1>c QED

====