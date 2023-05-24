-------------------- MODULE SimpleExampleWF_Flag --------------------
(*
This is a trivial example, showing how to use Weak Fairness in
proofs. Lets assume we have a flag x, that is off, and later it
becomes on (e.g. some decision is made). We want to prove, that
this is eventually done. The general scheme here is to show that:

  - always either we have <>x or <><<Next>>_x;
  - moreover if we execute <<Next>>_x, x becomes on.
  - From this it follows, that <>x is satisfied.

To prove <>x \/ <><<Next>>_x we have to consider the fairness
condition. More details on this are provided in the proof.
This proof is simple in this case because x \in BOOLEAN, thus
either the target is reached, or the Next action is enabled.

The module SimpleExampleWF_Max provides an example, where an
induction is required to show P \/ ENABLED <<A>>_vars.
*)
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
        (*
        Since x \in BOOLEAN, we either have x, or <<Next>>_x is
        enabled because it is precondition is ~x. That simplifies
        this example a lot. The example with the Max function has
        a non-boolean variable, thus the proof becomes more involved.
        *)
        <2>1. x \/ ENABLED <<Next>>_x BY ExpandENABLED DEF Next
        (*
        The next statement follows trivially, because
        WF_x(Next) = []( ([] ENABLED <<Next>>_x) => <><<Next>>_x)
                   = [](~([] ENABLED <<Next>>_x) \/ <><<Next>>_x) 
                   = []( (<>~ENABLED <<Next>>_x) \/ <><<Next>>_x)
                   = []( (<>x                  ) \/ <><<Next>>_x)
        *)
        <2>2. WF_x(Next) => [](<>x \/ <><<Next>>_x) BY <2>1, PTL
        (*
        The Spec implies WF_x(Next), thus the goal is proven. 
        *)
        <2>3. QED BY <2>2 DEF Spec, Live
  <1>2. ASSUME TypeOK, ~x, <<Next>>_x PROVE x' BY <1>2 DEF Next
  <1>3. QED BY <1>1, <1>2, SpecTypeOK, PTL DEF LeadsToX


LeadsToStableX == <>[]x
THEOREM SpecLeadsToStableX == Spec => LeadsToStableX
  <1>1. Spec => [](x => []x)
        <2>1. x /\ [Next]_x => x' BY DEF Next
        <2>2. QED BY <2>1, PTL DEF Spec
  <1>2. QED BY <1>1, SpecLeadsToX, PTL DEF LeadsToStableX, LeadsToX
  
=============================================================================
\* Modification History
\* Last modified Thu Jan 13 17:17:31 EET 2022 by karolis
\* Created Sat Jan 08 20:57:08 EET 2022 by karolis
