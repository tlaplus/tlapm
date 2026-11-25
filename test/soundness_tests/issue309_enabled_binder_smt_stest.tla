------------- MODULE issue309_enabled_binder_smt_stest --------------

\* https://github.com/tlaplus/tlapm/issues/309
\* An ENABLED under a binder is abstracted as a nullary constant, so the
\* bound variable t is dropped and (\E t : c) => (\A t : c) is proved.
\* The theorem is false: ENABLED (x = t /\ x' = t) is equivalent to
\* x = t, which holds for some t but not for all t.

EXTENDS TLAPS

VARIABLE x

THEOREM (\E t : ENABLED (x = t /\ x' = t)) => (\A t : ENABLED (x = t /\ x' = t))
BY SMT

=====================================================================
