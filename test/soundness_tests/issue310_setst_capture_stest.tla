------------- MODULE issue310_setst_capture_stest --------------

EXTENDS TLAPS

VARIABLE w

P(z, u) == {k \in w : k = z} = {u}
Q(u)    == {k \in w : k = k} = {u}

THEOREM ASSUME NEW k PROVE [](P(k, k)) => [](Q(k))
BY SMT DEF P, Q

===============================================================
known: https://github.com/tlaplus/tlapm/issues/310
