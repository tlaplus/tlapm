------------- MODULE prime_lambda_commute_smt_test --------------

\* Commuting the outer prime must preserve a and prime the free variable x.
\* Keep H unexpanded so normalization encounters the LAMBDA.

EXTENDS TLAPS

VARIABLE x

H(F(_)) == F(1)

THEOREM H(LAMBDA a : <<a, x>>)' = H(LAMBDA a : <<a, x'>>)
BY SMT

============================================================
stderr: status:proved
stderr: prover:smt
nostderr: status:failed
nostd*: Unexpected error
nostd*: Unexpected exception
nostd*: ending abnormally
