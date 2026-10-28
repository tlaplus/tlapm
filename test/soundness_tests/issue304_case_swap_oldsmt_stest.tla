------------- MODULE issue304_case_swap_oldsmt_stest --------------

\* https://github.com/tlaplus/tlapm/issues/304
\* A CASE denotes a CHOOSE among the results of its enabled arms; the arms
\* are unordered.  Swapping two enabled arms therefore leaves the value
\* unchanged, and this theorem is false.  The old encoding lowers CASE to
\* an ordered IF that picks the last enabled arm and proves it.

EXTENDS TLAPS

THEOREM (CASE TRUE -> "u" [] TRUE -> "v" [] OTHER -> "w")
          # (CASE TRUE -> "v" [] TRUE -> "u" [] OTHER -> "w")
BY SMT

====================================================================
flags: --debug oldsmt
known: https://github.com/tlaplus/tlapm/issues/304
