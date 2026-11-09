------------- MODULE issue309_same_term_test --------------

VARIABLE x

THEOREM ASSUME \E t : ENABLED (x = t /\ x' = t)
        PROVE  \E t : ENABLED (x = t /\ x' = t)
OBVIOUS

==========================================================
