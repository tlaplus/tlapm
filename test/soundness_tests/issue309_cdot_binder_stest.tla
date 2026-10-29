------------- MODULE issue309_cdot_binder_stest --------------

\* https://github.com/tlaplus/tlapm/issues/309
\* Same defect as issue309_enabled_binder_smt_stest, with \cdot under the
\* binder instead of ENABLED.  The theorem is false:
\* (x = t) \cdot (x' = t) is equivalent to x = t /\ x' = t, which holds
\* for some t but not for all t.

VARIABLE x

THEOREM (\E t : (x = t) \cdot (x' = t)) => (\A t : (x = t) \cdot (x' = t))
OBVIOUS

==============================================================
