---- MODULE forall_empty_test ----

EXTENDS TLAPS

THEOREM ASSUME NEW P
        PROVE \A x \in {} : P
    OBVIOUS

====
