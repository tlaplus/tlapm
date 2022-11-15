---- MODULE setminus_test ----

EXTENDS TLAPS

THEOREM ASSUME NEW a,
               NEW b
        PROVE \A x : x \in a \ b <=> x \in a /\ x \notin b
    OBVIOUS

====
