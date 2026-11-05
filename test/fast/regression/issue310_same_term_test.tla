------------- MODULE issue310_same_term_test --------------

\* https://github.com/tlaplus/tlapm/issues/310
\* Control for the naming of abstracted terms: the same term occurring in
\* a hypothesis and in the goal, mentioning both a bound variable and a
\* constant, must get the same name.

VARIABLE w

THEOREM ASSUME NEW k, [](\E j : w = <<j, k>>) PROVE [](\E j : w = <<j, k>>)
OBVIOUS

===========================================================
