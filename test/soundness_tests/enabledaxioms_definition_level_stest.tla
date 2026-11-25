------------- MODULE enabledaxioms_definition_level_stest --------------

\* ENABLED (x' = 1) is TRUE and ENABLED FALSE is FALSE, so the goal is
\* TRUE <=> FALSE.  The theorem is false.

EXTENDS TLAPS

VARIABLE x

B == (x' = 1) <=> FALSE

THEOREM ASSUME B PROVE ENABLED (x' = 1) <=> ENABLED FALSE
BY ENABLEDaxioms DEF B

============================================================
known: https://github.com/tlaplus/tlapm/issues/new
