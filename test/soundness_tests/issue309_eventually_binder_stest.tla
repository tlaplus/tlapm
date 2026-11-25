------------- MODULE issue309_eventually_binder_stest --------------

\* https://github.com/tlaplus/tlapm/issues/309
\* Same defect as issue309_enabled_binder_smt_stest, with a temporal body
\* <>(x = t) under the binder instead of ENABLED.  The theorem is false:
\* the behavior x = 1 forever satisfies <>(x = 1), but not <>(x = 2).

VARIABLE x

THEOREM (\E t : <>(x = t)) => (\A t : <>(x = t))
OBVIOUS

====================================================================
