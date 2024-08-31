---- MODULE excdom_test ----

EXTENDS TLAPS

THEOREM ASSUME NEW A,
               NEW B,
               NEW f \in [ A -> B ],
               NEW x,
               NEW a
        PROVE LET g == [ f EXCEPT ![x] = a ] IN
              DOMAIN g = DOMAIN f
    OBVIOUS

====
