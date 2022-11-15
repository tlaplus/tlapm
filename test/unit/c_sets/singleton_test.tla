---- MODULE singleton_test ----

EXTENDS TLAPS

THEOREM ASSUME NEW a
        PROVE \A x : x \in { a } <=> x = a
    OBVIOUS

====
