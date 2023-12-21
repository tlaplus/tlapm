------------------------------- MODULE EWD840 -------------------------------
EXTENDS Naturals, TLAPS

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
terminationDetected ==
  /\ tpos = 0 /\ tcolor = "white"
  /\ color[0] = "white" /\ ~ active[0]

TerminationDetection ==
  terminationDetected => \A i \in Nodes : ~ active[i]

(***************************************************************************)
(* Liveness property: termination is eventually detected.                  *)
(***************************************************************************)
Liveness ==
  (\A i \in Nodes : ~ active[i]) ~> terminationDetected

(***************************************************************************)
(* The following property says that eventually all nodes will terminate    *)
(* assuming that from some point onwards no messages are sent. It is       *)
(* undesired, but verified for the fairness condition WF_vars(Next).       *)
(* This motivates weakening the fairness condition to WF_vars(Controlled). *)
(***************************************************************************)
AllNodesTerminateIfNoMessages ==
  <>[][~ \E i \in Nodes : SendMsg(i)]_vars
  => <>(\A i \in Nodes : ~ active[i])

(***************************************************************************)
(* Dijkstra's invariant                                                    *)
(***************************************************************************)
Inv ==
  \/ P0:: \A i \in Nodes : tpos < i => ~ active[i]
  \/ P1:: \E j \in 0 .. tpos : color[j] = "black"
  \/ P2:: tcolor = "black"

-----------------------------------------------------------------------------

(* TypeOK is an inductive invariant *)
LEMMA TypeOK_inv == Spec => []TypeOK
<1>. USE NAssumption DEF TypeOK, Nodes, Color
<1>1. Init => TypeOK
  BY DEF Init
<1>2. TypeOK /\ [Next]_vars => TypeOK'
(* FIXME: Although each of the steps below is proved instantly,
   the attempt to prove the assertion all at once fails??
  BY NAssumption DEF Next, vars, TypeOK, Nodes, Color, Controlled, Environment,
                     InitiateProbe, PassToken, SendMsg, Deactivate
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
<1> USE NAssumption  (* Type information about the constants will be needed ! *)

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

<1> QED
  BY <1>1, <1>2, <1>3, TypeOK_inv, PTL DEF Spec



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
        <3>1. tpos < i  BY tpos=0, <2>5, NAssumption
        <3>. QED  BY <3>1, <2>3

    <2>. QED  BY <2>4, <2>5 DEF Nodes

<1>. QED
  BY <1>1 DEF TerminationDetection, terminationDetected


=============================================================================
\* Modification History
\* Last modified Wed Jan 08 15:06:01 CET 2020 by merz
\* Last modified Fri May 30 23:04:12 CEST 2014 by shaolin
\* Last modified Wed May 21 11:36:56 CEST 2014 by jael
\* Created Mon Sep 09 11:33:10 CEST 2013 by merz
