------------- MODULE issue310_setof_capture_stest --------------

EXTENDS TLAPS

VARIABLE w

P(z, u) == {z : k \in w} = {u}
Q(u)    == {k : k \in w} = {u}

THEOREM ASSUME NEW k PROVE [](P(k, k)) => [](Q(k))
BY SMT DEF P, Q

===============================================================
known: https://github.com/tlaplus/tlapm/issues/310