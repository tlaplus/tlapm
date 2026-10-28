------------- MODULE issue304_case_first_arm_smt_stest --------------

\* https://github.com/tlaplus/tlapm/issues/304
\* Neither of two enabled CASE arms has priority, so the value of this CASE
\* is unspecified among "u" and "v" and the theorem is false.  Lowering
\* CASE to an ordered IF/ite picks the first arm and proves it.

EXTENDS TLAPS

THEOREM (CASE TRUE -> "u" [] TRUE -> "v") = "u"
BY SMT

=====================================================================
known: https://github.com/tlaplus/tlapm/issues/304
