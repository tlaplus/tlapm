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
  \* BY CardinalityOne, SMT DEFS Next, Inv
  <2>1. Inv /\ UNCHANGED chosen => Inv'
    BY SMT DEF Inv
  <2>2. Inv /\ Next => Inv'
    BY CardinalityOne, SMT DEF Next, Inv
  <2> QED BY SMT, <2>1, <2>2
<1>3 QED
  PROOF OMITTED

=============================================================================
