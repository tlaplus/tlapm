------------- MODULE issue139_negated_boolean_eq_stest --------------

\* https://github.com/tlaplus/tlapm/issues/139
\* x is not known to be a Boolean, so ~(x = TRUE) does not imply
\* x = FALSE.  The theorem is false for any x that is not a Boolean.
\* The old SMT encoding in release 1.5.0 and earlier proves it.

VARIABLE x

THEOREM ~(x = TRUE) <=> (x = FALSE)
OBVIOUS

=====================================================================
