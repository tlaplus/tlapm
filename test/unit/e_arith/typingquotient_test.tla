---- MODULE typingquotient_test ----

EXTENDS TLAPS, Integers

THEOREM ASSUME NEW m \in Int,
               NEW n \in Int,
               n > 0
        PROVE (m \div n) \in Int
    OBVIOUS

====
