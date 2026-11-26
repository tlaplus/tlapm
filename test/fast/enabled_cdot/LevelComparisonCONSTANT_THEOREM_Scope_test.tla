-------------- MODULE LevelComparisonCONSTANT_THEOREM_Scope_test ---------------
(* Test that theorem-scope `CONSTANT` declarations and associated assumptions
are not usable via the proof directive `LevelComparison` when they do not
appear inside a nested sequent (in the assumptions).
*)
EXTENDS Naturals, TLAPS


THEOREM
    ASSUME
        CONSTANT k,
        TRUE,
        CONSTANT w,
        ASSUME TRUE
        PROVE w \in Nat
    PROVE k \in Nat
BY LevelComparison

================================================================================
stderr: obligations failed
