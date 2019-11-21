---- MODULE yices_false_test ----

EXTENDS TLAPS

THEOREM t == FALSE BY Yices

====
stderr: reason:false
