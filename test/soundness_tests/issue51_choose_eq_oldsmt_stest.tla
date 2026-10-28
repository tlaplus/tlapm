------------- MODULE issue51_choose_eq_oldsmt_stest --------------

\* https://github.com/tlaplus/tlapm/issues/51
\* The old SMT encoding rewrote X = CHOOSE v : P(v) to
\* (\E v : P(v)) => P(X).  In a goal, that proves X equal to the chosen
\* value for any X.  The theorem is false: CHOOSE v : TRUE is a single
\* value, and X need not be it.  The rule is disabled since 0f37dbf.

EXTENDS TLAPS

THEOREM ASSUME NEW X PROVE X = CHOOSE v : TRUE
BY SMT

==================================================================
flags: --debug oldsmt
