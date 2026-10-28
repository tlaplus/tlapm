------------- MODULE issue300_negative_exponent_oldsmt_stest --------------

\* https://github.com/tlaplus/tlapm/issues/300
\* For a non-zero integer n, n ^ (-1) is the real number 1/n (Specifying
\* Systems, Fig. 18.5b), which is not an integer for, e.g., n = 2.  The
\* theorem is false.

EXTENDS Integers, TLAPS

THEOREM ASSUME NEW n \in Int, n # 0
        PROVE  n ^ (-1) \in Int
BY Z3

===========================================================================
flags: --debug oldsmt
known: https://github.com/tlaplus/tlapm/issues/300
