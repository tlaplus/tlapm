------------------------------- MODULE EWD840 -------------------------------
EXTENDS Naturals, NaturalsInduction, TLAPS

CONSTANT N
ASSUME NAssumption == N \in Nat \ {0}

VARIABLES active, color, tpos, tcolor

Nodes == 0 .. N-1
Color == {"white", "black"}

TypeOK ==
  /\ active \in [Nodes -> BOOLEAN]    \* status of nodes (active or passive)
  /\ color \in [Nodes -> Color]       \* color of nodes
  /\ tpos \in Nodes                    \* token position
  /\ tcolor \in Color                  \* token color

(* Initially the token is at node 0, and it is black. There
   are no constraints on the status and color of the nodes. *)
Init ==
  /\ active \in [Nodes -> BOOLEAN]
  /\ color \in [Nodes -> Color]
  /\ tpos = 0
  /\ tcolor = "black"

(* Node 0 may initiate a probe when it has the token and when
   it is black or the token color is black. It passes
   a white token to node N-1 and paints itself white. *)
InitiateProbe ==
  /\ tpos = 0
  /\ tcolor = "black" \/ color[0] = "black"
  /\ tpos' = N-1
  /\ tcolor' = "white"
  /\ active' = active
  /\ color' = [color EXCEPT ![0] = "white"]

(* An inactive node different from 0 that possesses the token
   may pass it to node i-1 under the following circumstances:
   - node i is inactive or
   - node i is colored black or
   - the token is black.
   Note that the last two conditions will result in an
   inconclusive round, since the token will be black.
   The token will be stained if node i is black, otherwise
   its color is unchanged. Node i will be made white. *)
PassToken(i) ==
  /\ tpos = i
  /\ ~ active[i] \/ color[i] = "black" \/ tcolor = "black"
  /\ tpos' = i-1
  /\ tcolor' = IF color[i] = "black" THEN "black" ELSE tcolor
  /\ active' = active
  /\ color' = [color EXCEPT ![i] = "white"]

(* An active node i may activate another node j by sending it
   a message. If j>i (hence activation goes against the direction
   of the token being passed), then node i becomes black. *)
SendMsg(i) ==
  /\ active[i]
  /\ \E j \in Nodes \ {i} :
        /\ active' = [active EXCEPT ![j] = TRUE]
        /\ color' = [color EXCEPT ![i] = IF j>i THEN "black" ELSE @]
  /\ UNCHANGED <<tpos, tcolor>>

(* Any active node may become inactive at any moment. *)
Deactivate(i) ==
  /\ active[i]
  /\ active' = [active EXCEPT ![i] = FALSE]
  /\ UNCHANGED <<color, tpos, tcolor>>

(* Actions controlled by termination detection algorithm *)
Controlled ==
  \/ InitiateProbe
  \/ \E i \in Nodes \ {0} : PassToken(i)

(* Remaining actions, corresponding to environment transitions *)
Environment == \E i \in Nodes : Deactivate(i) \/ SendMsg(i)

Next == Controlled \/ Environment

vars == <<active, color, tpos, tcolor>>

Fairness == WF_vars(Controlled)

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------

(***************************************************************************)
(* Non-invariants for validating the specification.                        *)
(***************************************************************************)
NeverBlack == \A i \in Nodes : color[i] # "black"

NeverChangeColor == [][ \A i \in Nodes : UNCHANGED color[i] ]_vars

(***************************************************************************)
(* Main safety property: if there is a white token at node 0 then every    *)
(* node is inactive.                                                       *)
(***************************************************************************)
allInactive == \A i \in Nodes : ~ active[i]

terminationDetected ==
  /\ tpos = 0 /\ tcolor = "white"
  /\ color[0] = "white" /\ ~ active[0]

TerminationDetection ==
  terminationDetected => allInactive

(***************************************************************************)
(* Liveness property: termination is eventually detected.                  *)
(***************************************************************************)
Liveness ==
  allInactive ~> terminationDetected

(***************************************************************************)
(* The following property says that eventually all nodes will terminate    *)
(* assuming that from some point onwards no messages are sent. It is       *)
(* undesired, but verified for the fairness condition WF_vars(Next).       *)
(* This motivates weakening the fairness condition to WF_vars(Controlled). *)
(***************************************************************************)
AllNodesTerminateIfNoMessages ==
  <>[][~ \E i \in Nodes : SendMsg(i)]_vars
  => <>(\A i \in Nodes : ~ active[i])

-----------------------------------------------------------------------------
(***************************************************************************)
(* The formal proof of the safety property, based on Dijkstra's invariant. *)
(***************************************************************************)
Inv ==
  \/ P0:: \A i \in Nodes : tpos < i => ~ active[i]
  \/ P1:: \E j \in 0 .. tpos : color[j] = "black"
  \/ P2:: tcolor = "black"

USE NAssumption

(* TypeOK is an inductive invariant *)
LEMMA TypeCorrect == Spec => []TypeOK
<1>. USE DEF TypeOK, Nodes, Color
<1>1. Init => TypeOK
  BY DEF Init
<1>2. TypeOK /\ [Next]_vars => TypeOK'
(* FIXME: Although each of the steps below is proved instantly,
   the attempt to prove the assertion all at once fails??
  BY DEF Next, vars, Controlled, Environment, InitiateProbe,
         PassToken, SendMsg, Deactivate
*)
  <2> SUFFICES ASSUME TypeOK,
                      [Next]_vars
               PROVE  TypeOK'
    OBVIOUS
  <2>1. CASE InitiateProbe
    BY <2>1 DEF InitiateProbe
  <2>2. ASSUME NEW i \in Nodes \ {0},
               PassToken(i)
        PROVE  TypeOK'
    BY <2>2 DEF PassToken
  <2>3. ASSUME NEW i \in Nodes,
               Deactivate(i)
        PROVE  TypeOK'
    BY <2>3 DEF Deactivate
  <2>4. ASSUME NEW i \in Nodes,
               SendMsg(i)
        PROVE  TypeOK'
    BY <2>4 DEF SendMsg
  <2>5. CASE UNCHANGED vars
    BY <2>5 DEF vars
  <2>6. QED
    BY <2>1, <2>2, <2>3, <2>4, <2>5 DEF Controlled, Environment, Next
<1>3. QED
  BY <1>1, <1>2, PTL DEF Spec



THEOREM Spec => []TerminationDetection
(* Dijkstra's invariant implies correctness *)
<1>1 Inv => TerminationDetection
  BY  DEF Inv, TerminationDetection, terminationDetected, Nodes
(* Dijkstra's invariant is (trivially) established by the initial condition *)
<1>2 Init => Inv
  BY DEF Init, Inv
(* Dijkstra's invariant is inductive relative to the type invariant *)
<1>3 TypeOK /\ Inv /\ [Next]_vars => Inv'
  BY DEF Inv, TypeOK, Next, vars, Controlled, Environment,
         InitiateProbe, PassToken, SendMsg, Deactivate, Nodes, Color
<1> QED  BY <1>1, <1>2, <1>3, TypeCorrect, PTL DEF Spec


(* If the one-line proof of step <1>1 above is too obscure,
    here is a more detailed, hierarchical proof of the same property. *)
LEMMA Inv_implies_Termination == Inv => TerminationDetection
<1>1. ASSUME tpos = 0,
             tcolor = "white",
             color[0] = "white",
             ~ active[0],
             Inv
      PROVE  \A i \in Nodes : ~ active[i]

(* first of all, let's establish which case of the invariant we're in: *)
    <2>1. ~ Inv!P2 (* = ~ tcolor = "black" *)
        BY <1>1
    <2>2. ~ Inv!P1 (* = ~ \E j \in 0 .. tpos : color[j] = "black" *)
        BY <1>1
    <2>3. Inv!P0  (* = \A i \in Nodes : tpos < i => ~ active[i] *)
        BY Inv, <2>1, <2>2 DEF Inv

    <2>.  TAKE i \in Nodes

    <2>4. CASE i = 0  BY <2>4, <1>1

    <2>5. CASE i \in 1 .. N-1
        <3>1. tpos < i  BY tpos=0, <2>5
        <3>. QED  BY <3>1, <2>3

    <2>. QED  BY <2>4, <2>5 DEF Nodes

<1>. QED
  BY <1>1 DEF TerminationDetection, terminationDetected

-----------------------------------------------------------------------------
(***************************************************************************)
(* The liveness proof.                                                     *)
(* We have to show that after all nodes have terminated, node 0 will       *)
(* eventually detect termination. In order for this to happen, the token   *)
(* will have to perform up to 3 rounds of the ring. The first round simply *)
(* takes it back to node 0, the second round paints all nodes white,       *)
(* while the token may be black, and the third round verifies that all     *)
(* nodes are still white, so the token returns white.                      *)
(* The proof becomes a little simpler if we set it up as a proof by        *)
(* contradiction and assume that termination will never be declared.       *)
(* In particular, node 0 will then always pass on the token.               *)
(* The formula BSpec gathers all boxed formulas used in the proof.         *)  
(***************************************************************************)
BSpec == /\ []TypeOK 
         /\ [](~terminationDetected) 
         /\ [][Next]_vars
         /\ WF_vars(Controlled)

(***************************************************************************)
(* We first establish the enabledness conditions of the action for which   *)
(* fairness is asserted.                                                   *)
(***************************************************************************)

ControlledEnabled == 
\/ /\ tpos = 0
   /\ tcolor = "black" \/ color[0] = "black"
\/ \E i \in Nodes \ {0} :
      /\ tpos = i
      /\ ~ active[i] \/ color[i] = "black" \/ tcolor = "black"

LEMMA EnabledControlled ==
  ASSUME TypeOK
  PROVE  ENABLED <<Controlled>>_vars <=> ControlledEnabled
<1>1. InitiateProbe <=> <<InitiateProbe>>_vars
  BY DEF InitiateProbe, vars, TypeOK
<1>2. \A i \in Nodes \ {0} : PassToken(i) <=> <<PassToken(i)>>_vars
  <2>. SUFFICES ASSUME NEW i \in Nodes \ {0}
                PROVE  PassToken(i) => <<PassToken(i)>>_vars
    OBVIOUS
  <2>. QED
    BY DEF PassToken, vars, TypeOK
<1>3. Controlled <=> <<Controlled>>_vars
  BY <1>1, <1>2 DEF Controlled
<1>4. (ENABLED Controlled) <=> ENABLED <<Controlled>>_vars
  BY <1>3, ENABLEDrules
<1>5. ENABLED Controlled
      <=> \/ ENABLED InitiateProbe
          \/ \E i \in Nodes \ {0} : ENABLED PassToken(i)
  <2>1. Controlled <=>
        InitiateProbe \/ (\E i \in Nodes \ {0} : PassToken(i))
    BY DEF Controlled
  <2>2. (ENABLED Controlled) <=>
        ENABLED (InitiateProbe \/ (\E i \in Nodes \ {0} : PassToken(i)))
    BY <2>1, ENABLEDrules
  <2>3. ENABLED (InitiateProbe \/ (\E i \in Nodes \ {0} : PassToken(i)))
        <=> ENABLED InitiateProbe
            \/ ENABLED \E i \in Nodes \ {0} : PassToken(i)
    BY ENABLEDaxioms
  <2>4. (ENABLED \E i \in Nodes \ {0} : PassToken(i))
        <=> \E i \in Nodes \ {0} : ENABLED PassToken(i)
    BY ENABLEDaxioms
  <2>. QED
    BY <2>2, <2>3, <2>4
<1>6. ControlledEnabled!1 <=> ENABLED InitiateProbe
  BY ExpandENABLED, Zenon DEF InitiateProbe, TypeOK
<1>7. \A i \in Nodes \ {0} : ControlledEnabled!2!(i) <=> ENABLED PassToken(i)
  BY ExpandENABLED, Zenon DEF PassToken, TypeOK
<1>. QED 
  BY <1>4, <1>5, <1>6,<1>7 DEF ControlledEnabled

(***************************************************************************)
(* If all nodes are inactive, the token must eventually arrive at node 0.  *)
(***************************************************************************)
LEMMA TerminationRound1 ==
  BSpec => (allInactive ~> (allInactive /\ tpos = 0))
<1>. DEFINE P(n) == allInactive /\ n \in Nodes /\ tpos = n
            Q == P(0)
            R(n) == BSpec => [](P(n) => <>Q)
<1>1. \A n \in Nat : R(n)
  <2>1. R(0)
    BY PTL
  <2>2. ASSUME NEW n \in Nat
        PROVE  R(n) => R(n+1)
    <3>. DEFINE Pn == P(n)  Pn1 == P(n+1)
    <3>. USE DEF TypeOK, allInactive, Nodes
    <3>1. TypeOK /\ Pn1 /\ [Next]_vars => Pn1' \/ Pn'
      BY DEF Next, vars, Controlled, Environment, InitiateProbe, PassToken, Deactivate, SendMsg
    <3>2. TypeOK /\ Pn1 /\ <<Controlled>>_vars => Pn'
      BY DEF Controlled, InitiateProbe, PassToken, vars
    <3>3. TypeOK /\ Pn1 => ENABLED <<Controlled>>_vars
      BY EnabledControlled DEF ControlledEnabled
    <3>. HIDE DEF Pn1
    <3>4. R(n) => (BSpec => [](Pn1 => <>Q))
      BY <3>1, <3>2, <3>3, PTL DEF BSpec
    <3>. QED  BY <3>4 DEF Pn1
  <2>. HIDE DEF R
  <2>. QED  \* BY <2>1, <2>2, NatInduction
<1>2. BSpec => []((\E n \in Nat : P(n)) => <>Q)
  <2>. HIDE DEF P, Q
  <2>1. BSpec => [](\A n \in Nat : P(n) => <>Q)
    BY <1>1
  <2>2. (\A n \in Nat : P(n) => <>Q) <=> ((\E n \in Nat : P(n)) => <>Q)
    OBVIOUS
  <2>. QED  BY <2>1, <2>2, PTL
<1>3. TypeOK => (allInactive => \E n \in Nat : P(n))
  BY DEF allInactive, TypeOK, Nodes
<1>. QED  BY <1>2, <1>3, TypeCorrect, PTL DEF BSpec

(***************************************************************************)
(* Moreover, if all nodes are inactive and the token is at node 0 but      *)
(* termination cannot be detected, it will eventually return to node 0     *)
(* in a state where all nodes are white.                                   *)
(***************************************************************************)
allWhite == \A i \in Nodes : color[i] = "white"

LEMMA TerminationRound2 ==
  BSpec => ((allInactive /\ tpos = 0)
           ~> (allInactive /\ tpos = 0 /\ allWhite))
<1>. DEFINE P(n) == /\ allInactive /\ n \in Nodes /\ tpos = n
                    /\ color[0] = "white" 
                    /\ \A m \in n+1 .. N-1 : color[m] = "white"
            Q == P(0)
            R(n) == BSpec => [](P(n) => <>Q)
<1>1. BSpec => ((allInactive /\ tpos = 0) ~> \E n \in Nat : P(n))
  <2>. DEFINE S == allInactive /\ tpos = 0
              T == P(N-1)
  <2>. USE DEF TypeOK, allInactive, Nodes
  <2>1. TypeOK /\ S /\ [Next]_vars => S' \/ T'
    BY DEF Next, vars, Controlled, Environment, InitiateProbe, PassToken, Deactivate, SendMsg
  <2>2. TypeOK /\ S /\ <<Controlled>>_vars => T'
    BY DEF Controlled, InitiateProbe, PassToken, vars
  <2>3. TypeOK /\ ~terminationDetected /\ S => ENABLED <<Controlled>>_vars
    BY EnabledControlled DEF ControlledEnabled, terminationDetected, Color
  <2>4. T => \E n \in Nat : P(n)
    OBVIOUS
  <2>. HIDE DEF T
  <2>5. QED  BY <2>1, <2>2, <2>3, <2>4, PTL DEF BSpec
<1>2. \A n \in Nat : R(n)
  <2>1. R(0)
    BY PTL
  <2>2. ASSUME NEW n \in Nat
        PROVE  R(n) => R(n+1)
    <3>. DEFINE Pn == P(n)  Pn1 == P(n+1)
    <3>. USE DEF TypeOK, allInactive, Nodes
    <3>1. TypeOK /\ Pn1 /\ [Next]_vars => Pn1' \/ Pn'
      BY DEF Next, vars, Controlled, Environment, InitiateProbe, PassToken, Deactivate, SendMsg
    <3>2. TypeOK /\ Pn1 /\ <<Controlled>>_vars => Pn'
      BY DEF Controlled, InitiateProbe, PassToken, vars
    <3>3. TypeOK /\ Pn1 => ENABLED <<Controlled>>_vars
      BY EnabledControlled DEF ControlledEnabled
    <3>. HIDE DEF Pn1
    <3>4. R(n) => (BSpec => [](Pn1 => <>Q))
      BY <3>1, <3>2, <3>3, PTL DEF BSpec
    <3>. QED  BY <3>4 DEF Pn1
  <2>. HIDE DEF R
  <2>. QED  \* BY <2>1, <2>2, NatInduction
<1>3. BSpec => []((\E n \in Nat : P(n)) => <>Q)
  <2>. HIDE DEF P, Q
  <2>1. BSpec => [](\A n \in Nat : P(n) => <>Q)
    BY <1>2
  <2>2. (\A n \in Nat : P(n) => <>Q) <=> ((\E n \in Nat : P(n)) => <>Q)
    OBVIOUS
  <2>. QED  BY <2>1, <2>2, PTL
<1>4. Q => allInactive /\ tpos = 0 /\ allWhite
  BY DEF allWhite, Nodes
<1>. QED  BY <1>1, <1>3, <1>4, PTL

(***************************************************************************)
(* Finally, if all nodes are inactive and white, and the token is at       *)
(* node 0, eventually a white token will be at node 0 while all nodes are  *)
(* still white.                                                            *)
(***************************************************************************)
LEMMA TerminationRound3 ==
  BSpec => (allInactive /\ tpos = 0 /\ allWhite) ~> terminationDetected
<1>. DEFINE P(n) == /\ allInactive /\ n \in Nodes /\ tpos = n
                    /\ allWhite /\ tcolor = "white"
            Q == P(0)
            R(n) == BSpec => [](P(n) => <>Q)
<1>1. BSpec => ((allInactive /\ tpos = 0 /\ allWhite) ~> \E n \in Nat : P(n))
  <2>. DEFINE S == allInactive /\ tpos = 0 /\ allWhite
              T == P(N-1)
  <2>. USE DEF TypeOK, allInactive, Nodes, allWhite
  <2>1. TypeOK /\ S /\ [Next]_vars => S' \/ T'
    BY DEF Next, vars, Controlled, Environment, InitiateProbe, PassToken, Deactivate, SendMsg
  <2>2. TypeOK /\ S /\ <<Controlled>>_vars => T'
    BY DEF Controlled, InitiateProbe, PassToken, vars
  <2>3. TypeOK /\ ~terminationDetected /\ S => ENABLED <<Controlled>>_vars
    BY EnabledControlled DEF ControlledEnabled, terminationDetected, Color
  <2>4. T => \E n \in Nat : P(n)
    OBVIOUS
  <2>. HIDE DEF T
  <2>5. QED  BY <2>1, <2>2, <2>3, <2>4, PTL DEF BSpec
<1>2. \A n \in Nat : R(n)
  <2>1. R(0)
    BY PTL
  <2>2. ASSUME NEW n \in Nat
        PROVE  R(n) => R(n+1)
    <3>. DEFINE Pn == P(n)  Pn1 == P(n+1)
    <3>. USE DEF TypeOK, allInactive, Nodes, allWhite
    <3>1. TypeOK /\ Pn1 /\ [Next]_vars => Pn1' \/ Pn'
      BY DEF Next, vars, Controlled, Environment, InitiateProbe, PassToken, Deactivate, SendMsg
    <3>2. TypeOK /\ Pn1 /\ <<Controlled>>_vars => Pn'
      BY DEF Controlled, InitiateProbe, PassToken, vars
    <3>3. TypeOK /\ Pn1 => ENABLED <<Controlled>>_vars
      BY EnabledControlled DEF ControlledEnabled
    <3>. HIDE DEF Pn1
    <3>4. R(n) => (BSpec => [](Pn1 => <>Q))
      BY <3>1, <3>2, <3>3, PTL DEF BSpec
    <3>. QED  BY <3>4 DEF Pn1
  <2>. HIDE DEF R
  <2>. QED  \* BY <2>1, <2>2, NatInduction
<1>3. BSpec => []((\E n \in Nat : P(n)) => <>Q)
  <2>. HIDE DEF P, Q
  <2>1. BSpec => [](\A n \in Nat : P(n) => <>Q)
    BY <1>2
  <2>2. (\A n \in Nat : P(n) => <>Q) <=> ((\E n \in Nat : P(n)) => <>Q)
    OBVIOUS
  <2>. QED  BY <2>1, <2>2, PTL
<1>4. Q => terminationDetected
  BY DEF allInactive, allWhite, terminationDetected, Nodes
<1>. QED  BY <1>1, <1>3, <1>4, PTL


(***************************************************************************)
(* The liveness property follows from the above lemmas by simple temporal  *)
(* reasoning.                                                              *)
(***************************************************************************)
THEOREM Live == Spec => Liveness
BY TypeCorrect, TerminationRound1, TerminationRound2, TerminationRound3, PTL
   DEF Spec, Fairness, BSpec, Liveness

=============================================================================
\* Modification History
\* Last modified Tue Feb 09 09:57:46 CET 2021 by merz
\* Last modified Fri May 30 23:04:12 CEST 2014 by shaolin
\* Last modified Wed May 21 11:36:56 CEST 2014 by jael
\* Created Mon Sep 09 11:33:10 CEST 2013 by merz
