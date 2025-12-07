---- MODULE 20_MixedByProofTest ----
A == TRUE
THEOREM A
PROOF
<1>1 A
  BY DEF A
<1> QED
  BY <1>1 DEF A
====
