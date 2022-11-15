---- MODULE setst_test ----

EXTENDS TLAPS

THEOREM ASSUME NEW a,
               NEW P(_)
        PROVE \A x : x \in { y \in a : P(y) } <=> x \in a /\ P(x)
    OBVIOUS

====
