---- MODULE redsndord2_test ----

EXTENDS TLAPS

THEOREM ASSUME NEW F(_, _, _),
               NEW S, NEW x \in S
        PROVE \A y, z : [ v \in S |-> F(v, y, z) ][x] = F(x, y, z)
    OBVIOUS

====
