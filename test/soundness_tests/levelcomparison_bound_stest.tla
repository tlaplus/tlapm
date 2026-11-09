------------- MODULE levelcomparison_bound_stest --------------

\* \A c : c = c is valid.  \A d : c = d is false: not every value equals
\* c.

EXTENDS TLAPS

LEMMA L == \A c : c = c
OBVIOUS

THEOREM ASSUME NEW c PROVE \A d : c = d
BY L, LevelComparison

============================================================
known: https://github.com/tlaplus/tlapm/issues/new
