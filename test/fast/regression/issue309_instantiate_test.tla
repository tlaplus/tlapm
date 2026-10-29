------------- MODULE issue309_instantiate_test --------------

\* https://github.com/tlaplus/tlapm/issues/309
\* An abstracted term under a binder must be a function of the bound
\* variable, so that instantiating the binder works.  Here <>(x = t) must
\* become h(t) and <>(x = c) must become h(c) for the same h.  It
\* currently fails because the two instances are abstracted apart.

VARIABLE x

THEOREM ASSUME NEW c, \A t : <>(x = t) PROVE <>(x = c)
OBVIOUS

=============================================================
\* This obligation is unproved while instances of one term are abstracted
\* apart.  https://github.com/tlaplus/tlapm/issues/309
stderr: status:failed
nostderr: status:proved
nostderr: ending abnormally
