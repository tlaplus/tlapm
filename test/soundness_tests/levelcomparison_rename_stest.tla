------------- MODULE levelcomparison_rename_stest --------------

\* c = 1 does not imply d = 1.  The theorem is false for c # d.

EXTENDS TLAPS

THEOREM ASSUME NEW c, NEW d, c = 1 PROVE d = 1
BY LevelComparison

============================================================
known: https://github.com/tlaplus/tlapm/issues/new
