---- MODULE instance_constant_state_substitution_test ----

\* An unprimed constant parameter can be replaced by a state expression
\* when its uses impose no constant-level constraint.
---- MODULE M ----
CONSTANT c
Id == c
====

VARIABLE x

I == INSTANCE M WITH c <- x

THEOREM I!Id = x
BY DEF I!Id

\* A constant theorem does not make the module nonconstant.
---- MODULE WithTheorem ----
CONSTANT c
Id == c
THEOREM Identity == Id = c
<1>1. Id = c
  BY DEF Id
<1> QED
  BY <1>1
====

VARIABLE y

J == INSTANCE WithTheorem WITH c <- y

THEOREM J!Id = y
BY J!Identity

====
