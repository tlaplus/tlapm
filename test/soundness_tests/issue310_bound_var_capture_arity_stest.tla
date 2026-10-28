------------- MODULE issue310_bound_var_capture_arity_stest --------------

\* https://github.com/tlaplus/tlapm/issues/310
\* Variant of issue310_bound_var_capture_stest in which both abstracted
\* terms mention the constant k, so they keep the same arity even once
\* abstractions take their free variables as arguments (#309).  For the
\* constant k, P(k, k) expands to \E k : w = <<k, k>>, which prints like
\* Q(k).  The theorem is false: with k = 2 and w = <<1, 2>> forever,
\* [](Q(k)) holds and [](P(k, k)) does not.

VARIABLE w

P(z, u) == \E k : w = <<z, u>>
Q(u)    == \E k : w = <<k, u>>

THEOREM ASSUME NEW k PROVE [](Q(k)) => [](P(k, k))
BY DEF P, Q

==========================================================================
known: https://github.com/tlaplus/tlapm/issues/310
