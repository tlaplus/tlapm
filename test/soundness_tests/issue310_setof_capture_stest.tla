------------- MODULE issue310_setof_capture_stest --------------

\* The theorem is false for k = 1 and w = {1, 2} forever.  P(k, k)
\* compares {1} with {1}, while Q(k) compares {1, 2} with {1}.

EXTENDS TLAPS

VARIABLE w

P(z, u) == {z : k \in w} = {u}
Q(u)    == {k : k \in w} = {u}

THEOREM ASSUME NEW k PROVE [](P(k, k)) => [](Q(k))
BY SMT DEF P, Q

===============================================================
known: https://github.com/tlaplus/tlapm/issues/310