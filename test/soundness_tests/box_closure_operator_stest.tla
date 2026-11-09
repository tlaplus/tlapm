------------- MODULE box_closure_operator_stest --------------

\* F negates its argument, so F([](x = 0)) is <>(x # 0).  That does not
\* imply [](<>(x # 0)).  The theorem is false for a behavior where x is
\* 1 and then 0 forever.

EXTENDS TLAPS

VARIABLE x

F(a) == ~a

THEOREM ASSUME F([](x = 0)) PROVE [](F([](x = 0)))
BY PTL

============================================================
known: https://github.com/tlaplus/tlapm/issues/new
