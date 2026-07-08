---- MODULE 19_HierarchicalProofTest ----
THEOREM TRUE
PROOF
<1>1 TRUE
  <2> QED
    OBVIOUS
<1> QED
  BY <1>1
====
