------------- MODULE prime_tuple_inside_lambda_stest --------------

\* False: substituting x for a makes the LHS <<x'>> and the RHS <<x>>,
\* which need not be equal. The prime is on the tuple inside the LAMBDA,
\* so it must be preserved when the parameter a is replaced by x.

EXTENDS TLAPS

VARIABLE x

H(F(_)) == F(x)

THEOREM H(LAMBDA a : <<a>>')
      = H(LAMBDA a : <<a>>)
BY Isa

============================================================
\* related: prime_inside_lambda_param_stest
