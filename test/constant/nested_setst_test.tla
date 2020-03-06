---- MODULE nested_setst_test ----

EXTENDS TLAPS

THEOREM ASSUME NEW S,
               NEW T,
               NEW P(_),
               NEW Q(_)
        PROVE \A x : x \in { y \in S : P(y) /\ y \in { z \in T : Q(z) } }
                     <=> x \in S \cap T /\ P(x) /\ Q(x)
    OBVIOUS

====
