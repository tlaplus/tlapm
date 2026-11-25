------------- MODULE issue310_bound_var_capture_arity_zenon_stest --------------

\* The theorem is false for k = 2 and w = <<1, 2>> forever.  Q(k)
\* holds because the first component may be any value, while P(k, k)
\* requires both components to equal 2.

EXTENDS TLAPS

VARIABLE w

P(z, u) == \E k : w = <<z, u>>
Q(u)    == \E k : w = <<k, u>>

THEOREM ASSUME NEW k PROVE [](Q(k)) => [](P(k, k))
BY Zenon DEF P, Q

=============================================================================
known: https://github.com/tlaplus/tlapm/issues/310