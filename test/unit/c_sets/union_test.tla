---- MODULE union_test ----

EXTENDS TLAPS

THEOREM ASSUME NEW a
        PROVE \A x : x \in UNION a <=> \E y : y \in a /\ x \in y
    OBVIOUS

====
