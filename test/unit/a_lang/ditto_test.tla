---- MODULE ditto_test ----

EXTENDS TLAPS

THEOREM ASSUME NEW A
        PROVE \A x, y \in A : x \in A /\ y \in A
    OBVIOUS

====
