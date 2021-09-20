---- MODULE range_test ----

EXTENDS TLAPS, Integers

THEOREM ASSUME NEW m,
               NEW n,
               NEW p
        PROVE p \in m..n <=> p \in Int /\ m <= p /\ p <= n
    OBVIOUS

====
