---- MODULE drinker_test ----

EXTENDS TLAPS

THEOREM ASSUME NEW D(_)
        PROVE \E x : D(x) => \A y : D(y)
    OBVIOUS

====
