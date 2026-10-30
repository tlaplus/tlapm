------------- MODULE new_bound_time_test --------------

\* Before PTL, NEW c \in {k} becomes NEW c and the fact c \in {k}.  The
\* time of this fact must be computed for {k} in the context that holds
\* c.  CONSTANT k is declared before VARIABLE x, so the unshifted index
\* of k lands on x and the bound looks state-dependent.  The fact must
\* still be boxed: c \in {k} holds in every state.

EXTENDS TLAPS

CONSTANT k
VARIABLE x

THEOREM ASSUME NEW c \in {k} PROVE [](c \in {k})
BY PTL

============================================================
