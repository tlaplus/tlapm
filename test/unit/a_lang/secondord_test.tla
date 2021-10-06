---- MODULE secondord_test ----

EXTENDS TLAPS

F(x, G(_), y) == TRUE

THEOREM ASSUME NEW a,
               NEW G(_),
               NEW b
        PROVE F(a, G, b) = F(a, G, b)
    OBVIOUS

====
