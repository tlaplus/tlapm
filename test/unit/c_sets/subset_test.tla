---- MODULE subset_test ----

EXTENDS TLAPS

THEOREM ASSUME NEW a,
               NEW b
        PROVE a \subseteq b <=> \A x : x \in a => x \in b
    OBVIOUS

====
