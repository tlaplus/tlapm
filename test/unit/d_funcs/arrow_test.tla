---- MODULE arrow_test ----

EXTENDS TLAPS

THEOREM ASSUME NEW A,
               NEW B,
               NEW C,
               NEW F(_)
        PROVE [ x \in C |-> F(x) ] \in [ A -> B ] <=>
                      /\ A = C
                      /\ \A x \in A : F(x) \in B
    OBVIOUS

====
