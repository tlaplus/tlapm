---- MODULE isa_false_test ----

EXTENDS TLAPS

THEOREM t == FALSE BY Isa

====
stderr: status:failed
