------------- MODULE box_closure_sequent_multiple_assumptions_stest --------------

EXTENDS TLAPS

VARIABLES x, y

\* Both assumptions are state formulas.  x is 1 and y is 0, then x is 0
\* and y is 1: x = 0 /\ y = 1 => [](x = y) holds only in the first state.
THEOREM ASSUME ASSUME x = 0, y = 1 PROVE [](x = y)
         PROVE [](x = 0 /\ y = 1 => [](x = y))
BY PTL

============================================================
