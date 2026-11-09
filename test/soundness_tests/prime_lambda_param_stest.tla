------------- MODULE prime_lambda_param_stest --------------

\* The hypothesis is true: H(LAMBDA a : c) is c = c.  The goal is
\* 1 + x' = 2 + x', so the theorem is false: it fails for x' = 0.

EXTENDS Naturals, TLAPS

VARIABLE x

H(F(_)) == F(1) = F(2)

THEOREM ASSUME \A c : H(LAMBDA a : c)
        PROVE  H(LAMBDA a : a + x)'
BY Isa

============================================================
known: https://github.com/tlaplus/tlapm/issues/new
