---- MODULE productset_test ----

EXTENDS TLAPS

THEOREM ASSUME NEW A,
               NEW B,
               NEW t
        PROVE t \in A \X B <=>
                \E x, y : /\ x \in A
                          /\ y \in B
                          /\ t = << x, y >>
    OBVIOUS

====
