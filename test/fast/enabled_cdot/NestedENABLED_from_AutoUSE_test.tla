--------------------- MODULE NestedENABLED_from_AutoUSE_test -------------------
(* Test for multiply nested `ENABLED` with definitions that need expansion. *)
EXTENDS TLAPS


VARIABLE x


A == ENABLED (x /\ x')
B == ENABLED (x /\ A')
C == ENABLED (x /\ B')
D == ENABLED (x /\ C')
E == ENABLED (x /\ D')
F == ENABLED (x /\ E')
G == ENABLED (x /\ F')
H == ENABLED (x /\ G')
I == ENABLED (x /\ H')
J == ENABLED (x /\ I')


THEOREM
    ENABLED (J')
PROOF
BY ExpandENABLED, Isa, AutoUSE


================================================================================
