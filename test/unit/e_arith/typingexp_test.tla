---- MODULE typingexp_test ----

EXTENDS TLAPS, Integers

THEOREM ASSUME NEW m \in Int,
               m # 0,
               NEW n \in Int
        PROVE (m ^ n) \in Int
    OBVIOUS

====
