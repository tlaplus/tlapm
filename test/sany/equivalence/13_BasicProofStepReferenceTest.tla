---- MODULE 13_BasicProofStepReferenceTest ----
A == FALSE
B == TRUE
THEOREM A => B
PROOF
<1>a ~A BY ONLY DEF A
<1> QED BY <1>a

====
