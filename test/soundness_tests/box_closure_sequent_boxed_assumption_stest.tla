------------- MODULE box_closure_sequent_boxed_assumption_stest --------------

EXTENDS TLAPS

VARIABLES x, y

\* [](x = 0) is not diamond-closed, so ([](x = 0) => [](y = 0)) does not
\* imply its own box.  At the first state x is 1 and y is 0, then x is 0
\* and y is 0, then y becomes 1 while x stays 0: the implication holds
\* only in the first state.
THEOREM ASSUME ASSUME [](x = 0) PROVE [](y = 0)
         PROVE []([](x = 0) => [](y = 0))
BY PTL

============================================================
known: https://github.com/tlaplus/tlapm/issues/338
