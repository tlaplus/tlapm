---- MODULE pair_test ----

EXTENDS TLAPS

THEOREM ASSUME NEW a,
               NEW b
        PROVE \A x : x \in { a, b } <=> x = a \/ x = b
    OBVIOUS

====
