---- MODULE gteq_test ----

EXTENDS TLAPS, Integers

THEOREM ASSUME NEW m \in Int,
               NEW n \in Int
        PROVE (m >= n) \in Int

====
