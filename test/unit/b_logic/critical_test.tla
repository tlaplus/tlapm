---- MODULE critical_test ----

EXTENDS TLAPS

THEOREM ASSUME NEW P(_),
               NEW a,
               P(a)
        PROVE P(CHOOSE x : P(x))
    OBVIOUS

====
