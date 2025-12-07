---- MODULE 23_SufficesAssumeProveTest ----
A == TRUE
THEOREM A
PROOF
<1> SUFFICES ASSUME TRUE
             PROVE  A
  OBVIOUS
<1> QED
  BY DEF A
====
