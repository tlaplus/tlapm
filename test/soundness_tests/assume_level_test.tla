------------- MODULE assume_level_test --------------

\* An assumption must be constant.  tlapm must reject the ASSUME, or it
\* takes x = 0 as an axiom that holds at all times and proves [](x = 0).
\* SANY reports "assumptions must be level 0 (Constant)".

EXTENDS TLAPS

VARIABLE x

ASSUME A == x = 0

THEOREM [](x = 0)
BY A, PTL

============================================================
result: 3
stderr: Assumptions must be level 0
\* related to: https://github.com/tlaplus/tlapm/issues/213
