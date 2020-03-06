---- MODULE intlit_test ----

EXTENDS TLAPS, Integers

THEOREM /\ 0 \in Int
        /\ 1 \in Int
        /\ 2 \in Int
        /\ -1 \in Int
    OBVIOUS

====
