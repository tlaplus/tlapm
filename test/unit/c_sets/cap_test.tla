---- MODULE cap_test ----

EXTENDS TLAPS

THEOREM ASSUME NEW a,
               NEW b
        PROVE \A x : x \in a \cap b <=> x \in a /\ x \in b
    OBVIOUS

====
