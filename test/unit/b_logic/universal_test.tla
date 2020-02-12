---- MODULE universal_test ----

EXTENDS TLAPS

THEOREM ASSUME NEW P(_)
        PROVE \A x : P(x) => P(x)
    OBVIOUS

====
