---- MODULE funext_test ----

EXTENDS TLAPS

THEOREM ASSUME NEW A,
               NEW B,
               NEW f \in [ A -> B ]
        PROVE f = [ x \in DOMAIN f |-> f[x] ]
<1> DEFINE F == [ x \in DOMAIN f |-> f[x] ]
<1>1 DOMAIN F = DOMAIN f        OBVIOUS
<1>2 \A x \in A : F[x] = f[x]   OBVIOUS
<1>3 F \in [ A -> B ]
    <2>1 DOMAIN F = A               BY <1>1
    <2>2 \A x \in A : F[x] \in B    BY <1>2
    <2> QED                         BY <2>1, <2>2
<1>4 SUFFICES ASSUME NEW x \in A
              PROVE f[x] = F[x]     BY <1>3
<1> QED                         BY <1>2

====
