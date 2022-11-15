---- MODULE critical_bounded_test ----

EXTENDS TLAPS

THEOREM ASSUME NEW P(_),
               NEW s,
               NEW a \in s,
               P(a)
        PROVE P(CHOOSE x \in s : P(x))
    OBVIOUS

====
