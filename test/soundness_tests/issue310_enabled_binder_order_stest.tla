------------- MODULE issue310_enabled_binder_order_stest --------------

\* ENABLED (x = a /\ x' = b) is equivalent to x = a.  The antecedent
\* is true by choosing a = x, while the consequent is false because it
\* requires x = a for every a.

EXTENDS TLAPS

VARIABLE x

THEOREM (\E a : \A b : ENABLED (x = a /\ x' = b))
     => (\E b : \A a : ENABLED (x = a /\ x' = b))
BY SMT

======================================================================
known: https://github.com/tlaplus/tlapm/issues/310
