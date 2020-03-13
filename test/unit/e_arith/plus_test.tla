---- MODULE plus_test ----

EXTENDS TLAPS, Integers

THEOREM \A m, n \in Int :
                /\ n + 0 = n
                /\ 0 + n = n
                /\ m + n = n + m
    OBVIOUS

====
