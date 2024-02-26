---- MODULE universal_bounded_test ----

EXTENDS TLAPS

THEOREM ASSUME NEW P(_),
               NEW s
        PROVE \A x \in s : P(x) => P(x)
    OBVIOUS

====
