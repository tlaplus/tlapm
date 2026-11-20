------------- MODULE prime_lambda_smt_test --------------

\* The left side expands to <<1, x>>', so the theorem is valid.

EXTENDS TLAPS

VARIABLE x

H(F(_)) == F(1)

THEOREM H(LAMBDA a : <<a, x>>)' = <<1, x'>>
BY SMT

============================================================
stderr: status:(proved|failed)
stderr: prover:smt
nostd*: Unexpected error
nostd*: Unexpected exception
nostd*: ending abnormally
\* H stays hidden, so SMT times out. A backend crash is a failure.
