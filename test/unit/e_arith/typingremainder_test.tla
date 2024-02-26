---- MODULE typingremainder_test ----

EXTENDS TLAPS, Integers

THEOREM ASSUME NEW m \in Int,
               NEW n \in Int,
               n > 0
        PROVE (m % n) \in 0..(n-1)
    OBVIOUS

====
