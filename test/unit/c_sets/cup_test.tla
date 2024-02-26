---- MODULE cup_test ----

EXTENDS TLAPS

THEOREM ASSUME NEW a,
               NEW b
        PROVE \A x : x \in a \cup b <=> x \in a \/ x \in b
    OBVIOUS

====
