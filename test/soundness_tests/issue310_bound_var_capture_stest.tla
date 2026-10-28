------------- MODULE issue310_bound_var_capture_stest --------------

\* https://github.com/tlaplus/tlapm/issues/310
\* The print that names abstracted terms renders a bound variable exactly
\* like a constant of the same name.  For the constant k, P(k) expands to
\* \E k : w = k, which prints like Q, so [](P(k)) and []Q become the same
\* opaque constant.  The theorem is false: Q is valid, while [](P(k))
\* fails for any behavior in which w is never k.

VARIABLE w

P(z) == \E k : w = z
Q    == \E k : w = k

THEOREM ASSUME NEW k PROVE []Q => [](P(k))
BY DEF P, Q

====================================================================
known: https://github.com/tlaplus/tlapm/issues/310
