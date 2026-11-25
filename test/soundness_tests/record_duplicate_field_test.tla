------------- MODULE record_duplicate_field_test --------------

\* tlapm must reject a record with a duplicate field, as SANY does, or
\* the back-ends conclude that the field equals both values.  The
\* theorem implies 1 = 2.

THEOREM [a |-> 1, a |-> 2].a = 1 /\ [a |-> 1, a |-> 2].a = 2
OBVIOUS

============================================================
result: 3
stderr: a field occurs more than once in a record
\* related to: https://github.com/tlaplus/tlapm/issues/213
