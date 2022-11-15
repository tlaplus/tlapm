---- MODULE nat_test ----

EXTENDS TLAPS, Integers, Naturals

THEOREM ASSUME NEW n
        PROVE n \in Nat <=> n \in Int /\ n >= 0
    OBVIOUS

====
