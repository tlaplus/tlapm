------------- MODULE issue304_case_swap_smt_stest --------------

\* https://github.com/tlaplus/tlapm/issues/304
\* A CASE denotes a CHOOSE among the results of its enabled arms; the arms
\* are unordered.  Swapping two enabled arms therefore leaves the value
\* unchanged, and this theorem is false.  Lowering CASE to an ordered
\* IF/ite makes the two sides distinct and proves it.

EXTENDS TLAPS

THEOREM (CASE TRUE -> "u" [] TRUE -> "v" [] OTHER -> "w")
          # (CASE TRUE -> "v" [] TRUE -> "u" [] OTHER -> "w")
BY SMT

=================================================================
known: https://github.com/tlaplus/tlapm/issues/304
