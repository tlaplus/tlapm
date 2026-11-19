------------- MODULE prime_inside_lambda_param_stest --------------

\* The theorem expands to x' = x, which is false when x changes.
\* The prime is inside the LAMBDA body, so it must be preserved when
\* the parameter a is replaced by the state variable x.

EXTENDS TLAPS

VARIABLE x

H(F(_)) == F(x)

THEOREM H(LAMBDA a : a') = H(LAMBDA a : a)
BY Isa

============================================================
\* related: prime_lambda_param_stest
