------------- MODULE issue309_enabled_binder_zenon_stest --------------

\* https://github.com/tlaplus/tlapm/issues/309
\* Zenon variant of issue309_enabled_binder_smt_stest.

EXTENDS TLAPS

VARIABLE x

THEOREM (\E t : ENABLED (x = t /\ x' = t)) => (\A t : ENABLED (x = t /\ x' = t))
BY Zenon

=======================================================================
