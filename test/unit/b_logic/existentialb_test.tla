---- MODULE existentialb_test ----

EXTENDS TLAPS

THEOREM ASSUME NEW P(_),
               NEW s,
               NEW a \in s,
               P(a)
        PROVE \E x \in s : P(x)
    OBVIOUS

====
