---- MODULE setof_2_test ----

EXTENDS TLAPS

THEOREM ASSUME NEW a,
               NEW b,
               NEW F(_, _)
        PROVE \A x : x \in { F(y, z) : y \in a, z \in b } <=> \E y, z : y \in a /\ z \in b /\ x = F(y, z)
    OBVIOUS

====
