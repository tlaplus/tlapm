---- MODULE recorddom_test ----

EXTENDS TLAPS

THEOREM ASSUME NEW x,
               NEW y
        PROVE DOMAIN [ foo |-> x, bar |-> y ] = { "foo", "bar" }
    OBVIOUS

====
