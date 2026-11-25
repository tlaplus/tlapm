------------- MODULE issue309_enabled_binder_isa_stest --------------

\* https://github.com/tlaplus/tlapm/issues/309
\* Isabelle variant of issue309_enabled_binder_smt_stest.

EXTENDS TLAPS

VARIABLE x

THEOREM (\E t : ENABLED (x = t /\ x' = t)) => (\A t : ENABLED (x = t /\ x' = t))
BY Isa

=====================================================================
