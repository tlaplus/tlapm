---- MODULE capisfinite_test ----

EXTENDS TLAPS, FiniteSets

THEOREM ASSUME NEW a,
               NEW b
        PROVE ( IsFiniteSet(a) \/ IsFiniteSet(b) ) => IsFiniteSet(a \cap b)
    OBVIOUS

====
