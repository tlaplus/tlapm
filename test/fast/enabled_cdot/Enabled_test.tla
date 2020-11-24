---------------------------- MODULE Enabled_test -------------------------------
(* Unit tests for expanding `ENABLED`. *)
EXTENDS TLAPS


VARIABLE x, y, z

P(u) == u'
Q == y
R == x'


THEOREM
    (x = TRUE)  =>  ENABLED x
PROOF
    BY ExpandENABLED


THEOREM
    ENABLED (x')
PROOF
    BY ExpandENABLED


THEOREM
    ENABLED R
PROOF
    BY ExpandENABLED DEF R


THEOREM
    ENABLED R
PROOF
    BY ExpandENABLED, AutoUSE


THEOREM
    ENABLED P(x)
PROOF
    BY ExpandENABLED DEF P


THEOREM
    ENABLED P(x)
PROOF
    BY ExpandENABLED, AutoUSE


THEOREM
    ENABLED (P(x) \/ Q)
PROOF
    BY ExpandENABLED DEF P


THEOREM
    ENABLED (P(x) \/ Q)
PROOF
    BY ExpandENABLED, AutoUSE

--------------------------------------------------------------------------------

Yunprimed == y
F == ENABLED (z' /\ Yunprimed)
G == /\ Yunprimed
     /\ \E zprime, yprime:  zprime /\ yprime


THEOREM EnabledEliminationWithUnexpanded ==
    F = G
PROOF
    BY ExpandENABLED DEF F, G, Yunprimed
    (* This proof is sound with the operator Yunprimed expanded or not. *)


THEOREM
    F = G
PROOF
    BY ExpandENABLED, AutoUSE DEF F, G


--------------------------------------------------------------------------------

THEOREM
   ASSUME
       NEW A,
       A <=> ENABLED Yunprimed
   PROVE
       A <=> ENABLED (z' /\ y)
PROOF
    BY ExpandENABLED DEF Yunprimed

--------------------------------------------------------------------------------

A == (x \in BOOLEAN) /\ (x' = ~ x)
B == ENABLED (x \in BOOLEAN /\ << A >>_x)
BwithAexpanded ==
    ENABLED /\ x \in BOOLEAN
            /\ x' = ~ x
            /\ x' # x


THEOREM
    A => B
PROOF
    BY ExpandENABLED DEF A, B


THEOREM
    A => B
PROOF
    BY ExpandENABLED, AutoUSE DEF A, B


THEOREM
    B <=> BwithAexpanded
PROOF
    BY ExpandENABLED DEF A, B, BwithAexpanded


THEOREM
    B <=> BwithAexpanded
PROOF
    BY ExpandENABLED, AutoUSE DEF B, BwithAexpanded

--------------------------------------------------------------------------------

THEOREM
    (ENABLED (y /\ x')) = ENABLED (x' /\ y)
PROOF
    BY ExpandENABLED

--------------------------------------------------------------------------------

C == x' = x
D == ENABLED C


THEOREM
    C => D
PROOF
    BY ExpandENABLED DEF C, D


--------------------------------------------------------------------------------


THEOREM
    (ENABLED y /\ x') => ENABLED (y /\ x')
PROOF
    BY ExpandENABLED


THEOREM
    ((ENABLED y) /\ x')  <=>  ENABLED y /\ x'
PROOF
    BY ExpandENABLED

================================================================================
