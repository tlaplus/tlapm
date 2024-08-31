---- MODULE rectset_test ----

EXTENDS TLAPS

THEOREM ASSUME NEW A,
               NEW B,
               NEW r
        PROVE r \in [ foo : A, bar : B ] <=>
                    \E x, y : /\ x \in A
                              /\ y \in B
                              /\ r = [ foo |-> x, bar |-> y ]
    OBVIOUS

====
