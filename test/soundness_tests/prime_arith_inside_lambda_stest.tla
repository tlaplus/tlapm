------------- MODULE prime_arith_inside_lambda_stest --------------

\* False. Substituting x for a makes the left side (x + 1)' and the
\* right side x + 1. The prime on the sum must be preserved.

EXTENDS Naturals, TLAPS

VARIABLE x

H(F(_)) == F(x)

THEOREM H(LAMBDA a : (a + 1)') = H(LAMBDA a : a + 1)
BY Isa

============================================================
\* related: prime_inside_lambda_param_stest
