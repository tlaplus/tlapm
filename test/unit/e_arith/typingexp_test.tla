---- MODULE typingexp_test ----

EXTENDS TLAPS, Integers

THEOREM ASSUME NEW m \in Int,
               NEW n \in Int,
               m # 0 \/ n > 0
        PROVE (m ^ n) \in Int
    OBVIOUS

====
