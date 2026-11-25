------------- MODULE new_bound_time_stest --------------

\* Before PTL, NEW c \in {x} becomes NEW c and the fact c \in {x}.  The
\* time of this fact must be computed for {x} in the context that holds
\* c: otherwise x is read as c, the bound looks constant, and the fact is
\* boxed.  The theorem is false: c is x in the first state only.

EXTENDS TLAPS

VARIABLE x

THEOREM ASSUME NEW c \in {x} PROVE [](c \in {x})
BY PTL

============================================================
