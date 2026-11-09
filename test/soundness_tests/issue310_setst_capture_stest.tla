------------- MODULE issue310_setst_capture_stest --------------

\* The theorem is false for k = 1 and w = {1, 2} forever.  P(k, k)
\* selects only 1 from w, while Q(k) selects all of w, which is not {1}.

EXTENDS TLAPS

VARIABLE w

P(z, u) == {k \in w : k = z} = {u}
Q(u)    == {k \in w : k = k} = {u}

THEOREM ASSUME NEW k PROVE [](P(k, k)) => [](Q(k))
BY SMT DEF P, Q

===============================================================
known: https://github.com/tlaplus/tlapm/issues/310
