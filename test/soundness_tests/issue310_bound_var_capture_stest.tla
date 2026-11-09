------------- MODULE issue310_bound_var_capture_stest --------------

VARIABLE w

P(z) == \E k : w = z
Q    == \E k : w = k

THEOREM ASSUME NEW k PROVE []Q => [](P(k))
BY DEF P, Q

====================================================================
known: https://github.com/tlaplus/tlapm/issues/310
