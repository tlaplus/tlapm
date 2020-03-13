---- MODULE mult_test ----

EXTENDS TLAPS, Integers

THEOREM \A m, n \in Int :
                /\ n \times 1 = n
                /\ 1 \times n = n
                /\ n \times 0 = 0
                /\ 0 \times n = 0
                /\ m \times n = n \times m
    OBVIOUS

====
