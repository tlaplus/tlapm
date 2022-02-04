---- MODULE redsndord1_test ----

EXTENDS TLAPS

THEOREM ASSUME NEW P(_, _, _),
               NEW S, NEW a,
               NEW c,
               \E n : a = { y \in S : y = { x \in S : P(x, y, c) } },
               NEW y, NEW x
        PROVE y \in a => y \in S /\ ( x \in y <=> x \in S /\ P(x, y, c) )
    OBVIOUS

====
