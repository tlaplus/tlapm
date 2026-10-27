------------- MODULE issue309_instantiate_test --------------

\* https://github.com/tlaplus/tlapm/issues/309
\* An abstracted term under a binder must be a function of the bound
\* variable, so that instantiating the binder works.  Here <>(x = t) must
\* become h(t) and <>(x = c) must become h(c) for the same h.  It
\* currently fails because both are nullary constants with distinct
\* names.

VARIABLE x

THEOREM ASSUME NEW c, \A t : <>(x = t) PROVE <>(x = c)
OBVIOUS

=============================================================
