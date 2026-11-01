---- MODULE 24_StepAssumeBoundedNewTest ----
CONSTANT Key
THEOREM TRUE
PROOF
<1>1 ASSUME NEW k \in Key
     PROVE TRUE
     OBVIOUS
<1> QED BY <1>1
====
