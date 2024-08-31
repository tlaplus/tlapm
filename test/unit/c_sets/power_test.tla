---- MODULE power_test ----

EXTENDS TLAPS

THEOREM ASSUME NEW a
        PROVE \A x : x \in SUBSET a <=> \A y : y \in x => y \in a
    OBVIOUS

====
