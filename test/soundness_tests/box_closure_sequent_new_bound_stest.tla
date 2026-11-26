---- MODULE box_closure_sequent_new_bound_stest ----
EXTENDS TLAPS

VARIABLE x

\* A sequent with a state-dependent NEW bound is not box-closed.
\* Counterexample: x is {} initially, then {0} forever.
THEOREM
    ASSUME ASSUME NEW c \in x PROVE FALSE
    PROVE [](\A c \in x : FALSE)
BY PTL

==================================================
