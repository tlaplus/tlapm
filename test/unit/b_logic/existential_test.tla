---- MODULE existential_test ----

EXTENDS TLAPS

THEOREM ASSUME NEW P(_),
               NEW a,
               P(a)
        PROVE \E x : P(x)
    OBVIOUS

====
