---- MODULE setof_test ----

EXTENDS TLAPS

THEOREM ASSUME NEW a,
               NEW F(_)
        PROVE \A x : x \in { F(y) : y \in a } <=> \E y : y \in a /\ x = F(y)
    OBVIOUS

====
