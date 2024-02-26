---- MODULE tupleext_test ----

EXTENDS TLAPS

THEOREM ASSUME NEW x,
               NEW y,
               NEW u,
               NEW v
        PROVE << x, y >> = << u, v >>
                    <=> /\ x = u
                        /\ y = v
    OBVIOUS

====
