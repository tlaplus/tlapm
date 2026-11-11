------------- MODULE box_closure_sequent_false_conclusion_stest --------------

EXTENDS TLAPS

VARIABLES x, y

\* FALSE is closed, so ASSUME x = 0 PROVE FALSE is treated as closed.
\* x # 0 does not imply [](x # 0).  x is 1 and then 0 forever.
THEOREM ASSUME ASSUME x = 0 PROVE FALSE
         PROVE [](x = 0 => FALSE)
BY PTL

============================================================
known: https://github.com/tlaplus/tlapm/issues/338
