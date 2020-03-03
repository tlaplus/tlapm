---- MODULE relocalize_setst_test ----

EXTENDS TLAPS

THEOREM ASSUME NEW S,
               NEW a,
               NEW b,
               NEW c,
               NEW P(_, _, _),
               NEW Q(_, _, _),
               NEW R(_, _, _),
               \A y : \A x \in S : P(x, y, a) => Q(y, b, x) /\ R(c, x, y)
               PROVE \A u, y, v : { x \in S : P(x, y, a) }
                        \subseteq { x \in S : Q(y, b, x) }
                             \cap { x \in S : R(c, x, y) }
    OBVIOUS

====
