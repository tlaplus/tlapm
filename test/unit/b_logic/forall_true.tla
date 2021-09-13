---- MODULE forall_true_test ----

EXTENDS TLAPS

THEOREM ASSUME NEW S
        PROVE \A x \in S : TRUE
    OBVIOUS

====
