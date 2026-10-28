------------- MODULE issue306_case_second_arm_oldsmt_stest --------------

\* https://github.com/tlaplus/tlapm/issues/306
\* The old SMT encoding takes two CASE expressions whose first arms match
\* to be equal.  The theorem is false: under ~p and q the left side is 2
\* and the right side is 3.

EXTENDS Naturals, TLAPS

THEOREM ASSUME NEW p, NEW q, ~p, q
        PROVE  (CASE p -> 1 [] q -> 2 [] OTHER -> 0)
                 = (CASE p -> 1 [] q -> 3 [] OTHER -> 0)
BY SMT

=========================================================================
flags: --debug oldsmt
known: https://github.com/tlaplus/tlapm/issues/306
