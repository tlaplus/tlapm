--------------- MODULE LevelComparisonCONSTANT_Module_Scope_test ---------------
(* Test that module-scope `CONSTANT` declarations and associated assumptions
are not usable via the proof directive `LevelComparison`.

Previously, this was an error, due to the constants being renamed within the
scope of their declaration. This was equivalent to universal instantiation
of a bound constant *within* the scope of the universal quantifier that
binds it.
*)
EXTENDS Naturals, TLAPS


CONSTANT n


ASSUMPTION nType == n \in Nat


THEOREM
    ASSUME CONSTANT k
    PROVE k \in Nat
BY nType, LevelComparison

================================================================================
stderr: obligations failed
