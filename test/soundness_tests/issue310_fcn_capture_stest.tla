------------- MODULE issue310_fcn_capture_stest --------------

EXTENDS TLAPS

VARIABLE w

P(z, u) == [k \in w |-> z] = [v \in w |-> u]
Q(u)    == [k \in w |-> k] = [v \in w |-> u]

THEOREM ASSUME NEW k PROVE [](P(k, k)) => [](Q(k))
BY SMT DEF P, Q

=============================================================
known: https://github.com/tlaplus/tlapm/issues/310
