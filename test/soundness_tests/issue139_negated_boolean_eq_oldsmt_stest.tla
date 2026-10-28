------------- MODULE issue139_negated_boolean_eq_oldsmt_stest --------------

\* https://github.com/tlaplus/tlapm/issues/139
\* Old SMT encoding variant of issue139_negated_boolean_eq_stest.  x is not
\* known to be a Boolean, so ~(x = TRUE) does not imply that x equals
\* FALSE.  The theorem is false for any x that is not a Boolean.
\* FALSE is written as 1 = 2
\* because the old encoding emits an ill-sorted query for x = FALSE, which
\* Z3 rejects without deciding it.

EXTENDS TLAPS

VARIABLE x

THEOREM ~(x = TRUE) <=> (x = (1 = 2))
BY SMT

============================================================================
flags: --debug oldsmt
