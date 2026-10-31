---- MODULE instance_constant_primed_definition_test ----

\* A primed definition also makes the instancee nonconstant, even when
\* the constant parameter itself is used unprimed in Id.
---- MODULE M ----
CONSTANT c
Id == c
Primed == c'
====

VARIABLE x

I == INSTANCE M WITH c <- x

====
\* Known bug: TLAPM accepts this invalid INSTANCE, which SANY rejects.
\* https://github.com/tlaplus/tlapm/issues/213
\* Record the current acceptance; update this expectation when fixed.
result: 0
stderr: All 0 obligation proved.
nostderr: ending abnormally
