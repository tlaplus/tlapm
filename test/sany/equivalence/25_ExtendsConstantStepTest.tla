---- MODULE 25_ExtendsConstantStepTest ----
EXTENDS 25_ExtendsConstantBase
THEOREM
  ASSUME TypeInv, [Next]_store, NEW k \in Key
  PROVE  TypeInv'
PROOF BY DEF TypeInv, Next
====
