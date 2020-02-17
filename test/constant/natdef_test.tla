---- MODULE natdef_test ----

EXTENDS TLAPS, Integers

THEOREM ASSUME NEW n
        PROVE n \in Nat <=> n \in { z \in Int : z >= 0 }
    OBVIOUS

====
