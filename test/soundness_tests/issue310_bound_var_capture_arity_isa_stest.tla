------------- MODULE issue310_bound_var_capture_arity_isa_stest --------------

EXTENDS TLAPS

VARIABLE w

P(z, u) == \E k : w = <<z, u>>
Q(u)    == \E k : w = <<k, u>>

THEOREM ASSUME NEW k PROVE [](Q(k)) => [](P(k, k))
BY Isa DEF P, Q

=============================================================================
known: https://github.com/tlaplus/tlapm/issues/310
