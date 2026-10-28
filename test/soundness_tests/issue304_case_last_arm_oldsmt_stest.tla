------------- MODULE issue304_case_last_arm_oldsmt_stest --------------

\* https://github.com/tlaplus/tlapm/issues/304
\* Neither of two enabled CASE arms has priority, so the value of this CASE
\* is unspecified among "u" and "v" and the theorem is false.  The old
\* encoding lowers CASE to an ordered IF that picks the last enabled arm
\* and proves it.

EXTENDS TLAPS

THEOREM (CASE TRUE -> "u" [] TRUE -> "v") = "v"
BY SMT

========================================================================
flags: --debug oldsmt
known: https://github.com/tlaplus/tlapm/issues/304
