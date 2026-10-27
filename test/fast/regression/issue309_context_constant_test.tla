------------- MODULE issue309_context_constant_test --------------

\* https://github.com/tlaplus/tlapm/issues/309
\* An abstracted term must also be a function of the constants it mentions
\* from the context, not only of variables bound around it.  Here
\* <>(x = a) and <>(x = b) must become h(a) and h(b) for the same h, so
\* that a = b gives their equivalence.  It currently fails because both
\* are nullary constants with distinct names.

VARIABLE x

THEOREM ASSUME NEW a, NEW b, a = b PROVE <>(x = a) => <>(x = b)
OBVIOUS

==================================================================
