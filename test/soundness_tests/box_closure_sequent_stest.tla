------------- MODULE box_closure_sequent_stest --------------

\* (x = 0 => [](y = 0)) does not imply [](x = 0 => [](y = 0)).  The
\* theorem is false for a behavior where x is 1 and then 0, and y is
\* always 1.

EXTENDS TLAPS

VARIABLES x, y

THEOREM (x = 0 => [](y = 0)) => [](x = 0 => [](y = 0))
<1> SUFFICES ASSUME ASSUME x = 0 PROVE [](y = 0)
             PROVE [](x = 0 => [](y = 0))
    OBVIOUS
<1> QED
    BY PTL

============================================================
known: https://github.com/tlaplus/tlapm/issues/new
