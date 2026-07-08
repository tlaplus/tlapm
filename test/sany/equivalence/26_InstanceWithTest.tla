---- MODULE 26_InstanceWithTest ----
CONSTANT M
I == INSTANCE 26_InstanceWithBase WITH N <- M
THEOREM I!op = I!op
PROOF OBVIOUS
====
