---- MODULE bounded_test ----

EXTENDS TLAPS

THEOREM ASSUME NEW a,
               NEW b \in a
               PROVE b \in a
    OBVIOUS

====
