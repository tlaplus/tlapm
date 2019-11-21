---- MODULE smt_false_test ----

EXTENDS TLAPS

THEOREM t == FALSE BY SMT

====
stderr: reason:false
