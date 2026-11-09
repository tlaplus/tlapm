------------- MODULE enabledaxioms_pragma_name_stest --------------

\* ENABLED (x' = 1) is TRUE and ENABLED FALSE is FALSE, so the goal is
\* TRUE <=> FALSE.  The assumption x' # 1 does not make the goal true.

EXTENDS TLAPS

VARIABLE x

MyAxioms == TRUE (*{ by (prover:"enabledaxioms") }*)

THEOREM ASSUME (x' = 1) <=> FALSE PROVE ENABLED (x' = 1) <=> ENABLED FALSE
BY MyAxioms

============================================================
known: https://github.com/tlaplus/tlapm/issues/new
