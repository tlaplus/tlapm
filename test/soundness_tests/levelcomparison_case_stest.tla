------------- MODULE levelcomparison_case_stest --------------

\* The CASE is 3, so it does not equal 2.  The theorem is false.

EXTENDS TLAPS

THEOREM (CASE FALSE -> 1 [] TRUE -> 3) = 2
<1>1. (CASE FALSE -> 1 [] TRUE -> 2) = 2
    OBVIOUS
<1> QED
    BY <1>1, LevelComparison

============================================================
known: https://github.com/tlaplus/tlapm/issues/new
