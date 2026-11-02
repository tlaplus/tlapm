----------------------------- MODULE Consensus ------------------------------
EXTENDS FiniteSetTheorems, TLAPS

CONSTANT Value

VARIABLE chosen

Init == chosen = {}
Next == /\ chosen = {}
        /\ \E v \in Value : chosen' = {v}
Spec == Init /\ [][Next]_chosen

-----------------------------------------------------------------------------

Inv == /\ chosen \subseteq Value
       /\ IsFiniteSet(chosen)
       /\ Cardinality(chosen) \leq 1

-----------------------------------------------------------------------------

THEOREM Invariance == Spec => []Inv
<1>1 Init => Inv
  BY FS_EmptySet DEFS Init, Inv
<1>2. Inv /\ [Next]_chosen => Inv'
  BY FS_Singleton, Z3 DEFS Next, Inv
<1>3 QED
  PROOF BY <1>1,<1>2,PTL DEF Spec

=============================================================================
