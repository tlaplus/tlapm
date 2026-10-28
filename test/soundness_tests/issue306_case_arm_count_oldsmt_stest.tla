------------- MODULE issue306_case_arm_count_oldsmt_stest --------------

\* https://github.com/tlaplus/tlapm/issues/306
\* Variant of issue306_case_second_arm_oldsmt_stest in which the two CASE
\* expressions have different numbers of arms.  The theorem is false:
\* under ~p and q the left side is 0 and the right side is 3.

EXTENDS Naturals, TLAPS

THEOREM ASSUME NEW p, NEW q, ~p, q
        PROVE  (CASE p -> 1 [] OTHER -> 0)
                 = (CASE p -> 1 [] q -> 3 [] OTHER -> 0)
BY SMT

========================================================================
flags: --debug oldsmt
known: https://github.com/tlaplus/tlapm/issues/306
