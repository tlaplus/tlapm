------------- MODULE levelcomparison_assumptions_stest --------------

\* ASSUME FALSE PROVE FALSE is valid.  It does not prove FALSE, and the
\* theorem FALSE is not valid.

EXTENDS TLAPS

LEMMA L == ASSUME FALSE PROVE FALSE
OBVIOUS

THEOREM FALSE
BY L, LevelComparison

============================================================
known: https://github.com/tlaplus/tlapm/issues/new
