-------------------- MODULE LevelComparisonSTATE_Scope_test --------------------
(* Test that `STATE` declarations and associated assumptions are unusable via
the proof directive `LevelComparison` when they do not appear inside a nested
sequent (in the assumptions).
*)
EXTENDS Naturals, TLAPS


THEOREM
    ASSUME STATE P, P
    PROVE TRUE
<1>1. ASSUME STATE Q
      PROVE Q
    BY LevelComparison
<1> QED

================================================================================
stderr: obligations failed
