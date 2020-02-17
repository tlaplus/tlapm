------ MODULE neither_zero_one_test ------

EXTENDS TLAPS, Integers

THEOREM ~ 0 \/ ~ 1
<1>1 SUFFICES ASSUME 0, 1 PROVE FALSE   OBVIOUS
<1>2 0 = TRUE /\ 1 = TRUE               BY <1>1
<1>3 0 = 1                              BY <1>2
<1> QED                                 BY <1>3

====

