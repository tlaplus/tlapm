------------- MODULE issue69_instantiated_strong_fairness_stest --------------

\* https://github.com/tlaplus/tlapm/issues/69
\* Strong fairness variant of the lemma XY!Fair <=> WF_(XY!vars)(XY!Next)
\* in issue69_instantiated_fairness_stest.  In I!Fair, ENABLED binds x' and
\* y' before the substitution x <- z, y <- z, whereas in SF_(I!vars)(I!Next)
\* it binds z' after.  For z = 0 forever, I!Fair is FALSE and
\* SF_(I!vars)(I!Next) is TRUE, so the theorem is false.

EXTENDS Integers, TLAPS

VARIABLE z

---- MODULE Inner ----
EXTENDS Integers
VARIABLES x, y
Next == x' = x + 1 /\ y' = y - 1
vars == <<x, y>>
Fair == SF_vars(Next)
====

I == INSTANCE Inner WITH x <- z, y <- z

THEOREM I!Fair <=> SF_(I!vars)(I!Next)
BY DEF I!Fair

==============================================================================
