---- MODULE 11_BasicAssumeProveTest ----
THEOREM
  ASSUME
    NEW CONSTANT A,
    NEW CONSTANT B,
    NEW CONSTANT C
  PROVE
    /\ A = B
    /\ B = C
    => A = C
PROOF OBVIOUS
====