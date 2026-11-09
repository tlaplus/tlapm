------------- MODULE issue310_choose_capture_stest --------------

\* Let w = {1, 2} forever and let k be the element that CHOOSE does
\* not select from w.  P(k, k) selects k uniquely, while Q(k) selects
\* the other element, so the theorem is false.

EXTENDS TLAPS

VARIABLE w

P(z, u) == (CHOOSE k \in w : k = z) = u
Q(u)    == (CHOOSE k \in w : k = k) = u

THEOREM ASSUME NEW k PROVE [](P(k, k)) => [](Q(k))
BY SMT DEF P, Q

=================================================================
known: https://github.com/tlaplus/tlapm/issues/310
