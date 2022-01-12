-------------------- MODULE SimpleExampleWF_Flag --------------------
EXTENDS TLAPS
VARIABLE x
Init == x = FALSE
Next == ~x /\ x' = TRUE
Live == WF_x(Next)
Spec == Init /\ [][Next]_x /\ Live
--------------------------------------------
TypeOK == x \in BOOLEAN
LEMMA SpecTypeOK == Spec => []TypeOK
  <1>1. Init => TypeOK BY DEF Init, TypeOK
  <1>2. TypeOK /\ [Next]_x => TypeOK' BY DEF TypeOK, Next
  <1>3. QED BY <1>1, <1>2, PTL DEF Spec


LeadsToX == <>x
THEOREM SpecLeadsToX == Spec => LeadsToX
  <1>1. Spec => [](<>x \/ <><<Next>>_x)
        <2>1. x \/ ENABLED <<Next>>_x BY ExpandENABLED DEF Next
        <2>2. WF_x(Next) => (<>x \/ <><<Next>>_x) BY <2>1, PTL
        <2>3. QED BY <2>1, <2>2, PTL DEF Spec, Live
  <1>2. ASSUME TypeOK, ~x, <<Next>>_x PROVE x' BY <1>2 DEF Next
  <1>3. QED BY <1>1, <1>2, SpecTypeOK, PTL DEF LeadsToX


LeadsToStableX == <>[]x
THEOREM SpecLeadsToStableX == Spec => LeadsToStableX
  <1>1. Spec => [](x => []x)
        <2>1. Init => (x => []x) BY DEF Init
        <2>2. x /\ [Next]_x => x' BY DEF Next
        <2>3. QED BY <2>1, <2>2, PTL DEF Spec
  <1>2. QED BY <1>1, SpecLeadsToX, PTL DEF LeadsToStableX, LeadsToX
  
=============================================================================
\* Modification History
\* Last modified Wed Jan 12 16:11:04 EET 2022 by karolis
\* Created Sat Jan 08 20:57:08 EET 2022 by karolis
