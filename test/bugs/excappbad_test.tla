---- MODULE excapp3_test ----

EXTENDS TLAPS

THEOREM ASSUME NEW A,
               NEW B,
               NEW f \in [ A -> B ],
               NEW x \in A,
               NEW y \in A,
               NEW a,
               NEW b
        PROVE LET g == [ f EXCEPT ![x] = a, ![y] = b ] IN
              g[x] = a
    OBVIOUS

====
stderr: status:failed
