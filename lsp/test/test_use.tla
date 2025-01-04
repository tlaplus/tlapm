---- MODULE test_use ----
op == TRUE
USE DEF op
USE TRUE
USE FALSE
HIDE TRUE
THEOREM TRUE
    <1> USE TRUE
    <1> USE FALSE
    <1> HIDE TRUE
    <1> QED
====
