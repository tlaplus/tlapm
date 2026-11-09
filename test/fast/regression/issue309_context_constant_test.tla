------------- MODULE issue309_context_constant_test --------------

VARIABLE x

THEOREM ASSUME NEW a, NEW b, a = b PROVE <>(x = a) => <>(x = b)
OBVIOUS

==================================================================
\* This obligation is unproved while the two instances are distinct
\* nullary constants.  https://github.com/tlaplus/tlapm/issues/309
stderr: status:failed
nostderr: status:proved
nostderr: ending abnormally
