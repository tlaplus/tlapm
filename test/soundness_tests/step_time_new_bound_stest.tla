------------- MODULE step_time_new_bound_stest --------------

\* The theorem is false: c is x in the first state only.

EXTENDS TLAPS

VARIABLE x

THEOREM ASSUME NEW c \in {x} PROVE [](c = x)
<1>1. c = x
    OBVIOUS
<1> QED
    BY <1>1, PTL

============================================================
known: https://github.com/tlaplus/tlapm/issues/new
