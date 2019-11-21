----------------------------- MODULE consensus_test ------------------------------
EXTENDS Sets, TLAPS

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
  BY CardinalityZero, SMT DEFS Init, Inv
<1>2. Inv /\ [Next]_chosen => Inv'
  BY CardinalityOne, SMT DEFS Next, Inv
<1>3 QED
  PROOF OMITTED

=============================================================================
