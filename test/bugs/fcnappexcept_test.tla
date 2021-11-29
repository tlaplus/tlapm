---- MODULE fcnappexcept_test ----

EXTENDS TLAPS

----

THEOREM
ASSUME NEW CONSTANT f,
       NEW CONSTANT a,
       NEW CONSTANT b,
       a # b,
       f[b] = "foo"
PROVE  [f EXCEPT ![a] = "bar"][b] = "foo"
    OBVIOUS

====
stderr: status:failed
