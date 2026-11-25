------------- MODULE issue310_fcn_capture_stest --------------

\* The theorem is false for k = 1 and w = {1, 2} forever.  P(k, k)
\* compares two constant functions with value 1, while Q(k) compares
\* the identity function with a function that maps 2 to 1.

EXTENDS TLAPS

VARIABLE w

P(z, u) == [k \in w |-> z] = [v \in w |-> u]
Q(u)    == [k \in w |-> k] = [v \in w |-> u]

THEOREM ASSUME NEW k PROVE [](P(k, k)) => [](Q(k))
BY SMT DEF P, Q

=============================================================
known: https://github.com/tlaplus/tlapm/issues/310
