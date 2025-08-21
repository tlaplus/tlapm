------------------------- MODULE LevelComparison_test --------------------------
(* Tests for the proof directive LevelComparison. *)
EXTENDS Integers, TLAPS


VARIABLE x


(* A theorem about an action-level operator A. *)
THEOREM ActionLevel ==
    ASSUME
        ACTION A
    PROVE
        <<A>>_x => A
OBVIOUS


(* The theorem ActionLevel with action A substituted by a state-level operator
P. The proof cites the theorem ActionLevel and uses the proof directive
LevelComparison to substitute P for A. The proof directive LevelComparison
checks that the substituted operator P has level at most that of the operator
A that it replaces.

The proof directive LevelComparison works for theorems of this form,
where a formula appears only in the consequent (PROVE) of the sequent, and only
declarations appear in the hypotheses (ASSUME). Any non-nested sequent can be
brought in this form by using implication.
*)
THEOREM
    ASSUME
        STATE P
    PROVE
        <<P>>_x => P
PROOF
BY ActionLevel, LevelComparison


(* A temporal operator. *)
Prop(u) == ([]u) => (<>[]u)


(* A theorem about the operator Prop, with argument a temporal-level operator P.
*)
THEOREM TemporalLevel ==
    ASSUME
        TEMPORAL P
    PROVE
        Prop(P)
BY PTL DEF Prop


(* The theorem TemporalLevel with operator P renamed to Q. The renaming is
checked by using the proof directive LevelComparison, which checks that Q
substitutes an operator of the same or higher level (in this case same level,
and impossible to have an operator of expression level higher than temporal).
*)
THEOREM
    ASSUME
        TEMPORAL Q
    PROVE
        Prop(Q)
BY TemporalLevel, LevelComparison


(* The theorem TemporalLevel with the temporal-level operator P substituted by
a state-level operator P. The substitution is checked using the proof directive
LevelComparison, which checks that P substitutes an operator of the same or
higher expression level (in this case higher level).
*)
THEOREM
    ASSUME
        STATE P
    PROVE
        Prop(P)
BY TemporalLevel, LevelComparison


(* The theorem TemporalLevel with the temporal-level operator P substituted by
a constant-level operator P. The substitution is checked by using the proof
directive LevelComparison, ensuring that P substitutes an operator of the same
or higher expression level (in this case higher level).
*)
THEOREM
    ASSUME
        CONSTANT P
    PROVE
        Prop(P)
BY TemporalLevel, LevelComparison

--------------------------------------------------------------------------------

THEOREM
    ASSUME
        ASSUME CONSTANT n, n \in Nat
        PROVE n \in Int,
        CONSTANT n,
        n \in Nat
    PROVE n \in Int
BY LevelComparison


THEOREM
    ASSUME
        ASSUME STATE P, STATE Q, P = Q
        PROVE P.a = Q.a
    PROVE TRUE
<1>1. ASSUME STATE A, STATE B, A = B
      PROVE A.a = B.a
    BY LevelComparison
<1> QED

================================================================================
