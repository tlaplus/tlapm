---- MODULE tupleapp_test ----

EXTENDS TLAPS, Integers

THEOREM ASSUME NEW x,
               NEW y
        PROVE /\ << x, y >>[1] = x
              /\ << x, y >>[2] = y
    OBVIOUS

====
