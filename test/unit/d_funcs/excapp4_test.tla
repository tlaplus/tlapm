---- MODULE excapp4_test ----

EXTENDS TLAPS

THEOREM ASSUME NEW A,
               NEW B,
               NEW C,
               NEW f \in [ A -> [ B -> C ] ],
               NEW x \in A,
               NEW y \in B,
               NEW a
        PROVE LET g == [ f EXCEPT ![x][y] = a ] IN
              g[x][y] = a
    OBVIOUS

====
