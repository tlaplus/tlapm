---- MODULE lenisint_test ----

EXTENDS TLAPS, Sequences

----

THEOREM
ASSUME NEW CONSTANT s
PROVE  Len(s) \in Int
    OBVIOUS

====
stderr: status:failed
