---- MODULE tupledom_test ----

EXTENDS TLAPS, Integers

THEOREM ASSUME NEW x,
               NEW y
        PROVE DOMAIN << x, y >> = 1..2
    OBVIOUS

====
