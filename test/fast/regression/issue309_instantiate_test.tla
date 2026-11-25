------------- MODULE issue309_instantiate_test --------------

VARIABLE x

THEOREM ASSUME NEW c, \A t : <>(x = t) PROVE <>(x = c)
OBVIOUS

=============================================================
\* This obligation is unproved while the two instances are distinct
\* nullary constants.  https://github.com/tlaplus/tlapm/issues/309
stderr: status:failed
nostderr: status:proved
nostderr: ending abnormally
