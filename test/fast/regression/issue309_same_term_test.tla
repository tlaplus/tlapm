------------- MODULE issue309_same_term_test --------------

\* https://github.com/tlaplus/tlapm/issues/309
\* Control for the abstraction of terms under a binder: the same
\* quantified ENABLED in a hypothesis and in the goal must still match
\* once abstractions take their bound variables as arguments.

VARIABLE x

THEOREM ASSUME \E t : ENABLED (x = t /\ x' = t)
        PROVE  \E t : ENABLED (x = t /\ x' = t)
OBVIOUS

==========================================================
