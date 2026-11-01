---- MODULE 25_ExtendsConstantBase ----
CONSTANT Key
VARIABLE store
TypeInv == store \in SUBSET Key
Next == store' = store
====
