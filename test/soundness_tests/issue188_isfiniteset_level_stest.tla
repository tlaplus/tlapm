------------- MODULE issue188_isfiniteset_level_stest --------------

\* https://github.com/tlaplus/tlapm/issues/188
\* Inv is a state predicate, but a wrong level for IsFiniteSet made it
\* constant, so Inv' was identified with Inv.  The theorem is false: it
\* fails for a step from v = {} to v = Nat.

EXTENDS FiniteSets

VARIABLE v

Inv == IsFiniteSet(v)

THEOREM ASSUME Inv PROVE Inv'
OBVIOUS

====================================================================
