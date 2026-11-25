------------- MODULE issue69_instantiated_fairness_stest --------------
\* https://github.com/tlaplus/tlapm/issues/69
\* The issue's modules XY and Z, with XY inlined.  ExpandENABLED replaces
\* ENABLEDrules, which never reached main.  The false lemma about XY!En is
\* dropped, since tlapm no longer proves it.
EXTENDS Integers, TLAPS

VARIABLE z

--------------------------------- MODULE XY ---------------------------------
EXTENDS Integers, NaturalsInduction, TLAPS
VARIABLES x,y

(***************************************************************************)
(* A simple specification with two integer variables x and y. Both         *)
(* variables are initially 0, and at each step x is incremented and        *)
(* y is decremented. We prove a few simple properties, and in particular   *)
(* a liveness property showing that the values of x and y diverge.         *)
(***************************************************************************)

Init == x=0 /\ y=0
Next == x'=x+1 /\ y'=y-1
vars == <<x,y>>
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

TypeOK == x \in Int /\ y \in Int

En == ENABLED <<Next>>_vars
Fair == WF_vars(Next)

THEOREM Type == Init /\ [][Next]_vars => []TypeOK
<1>1. Init => TypeOK
  BY DEF Init, TypeOK
<1>2. TypeOK /\ [Next]_vars => TypeOK'
  BY DEF Next, vars, TypeOK
<1>. QED  BY <1>1, <1>2, PTL

(***************************************************************************)
(* The next-state action is always enabled; the type-correctness           *)
(* condition ensures that the values of x and y change.                    *)
(***************************************************************************)
LEMMA Enabled == TypeOK => ENABLED <<Next>>_vars
<1>. SUFFICES ASSUME TypeOK
              PROVE  ENABLED <<Next>>_vars
  OBVIOUS
<1>1. <<Next>>_vars <=> Next
  BY DEF Next, vars, TypeOK
<1>2. (ENABLED <<Next>>_vars) <=> (ENABLED Next)
  BY ExpandENABLED DEF Next, vars, TypeOK
<1>3. ENABLED Next
  BY ExpandENABLED DEF Next
<1>. QED  BY <1>2, <1>3

(***************************************************************************)
(* For any natural number n, the value of x will eventually be at least n, *)
(* and the value of y at most -n.                                          *)
(***************************************************************************)
THEOREM Live == Spec => \A n \in Nat : <>(x >= n /\ y <= -n)
<1>. DEFINE P(n) == x >= n /\ y <= -n
            Q(n) == Spec => <>P(n)
<1>1. Q(0)
  <2>1. Init => P(0)
    BY DEF Init
  <2>. QED  BY <2>1, PTL DEF Spec
<1>2. ASSUME NEW n \in Nat
      PROVE  Q(n) => Q(n+1)
  <2>1. TypeOK /\ P(n) /\ [Next]_vars => P(n)' \/ P(n+1)'
    BY DEF TypeOK, Next, vars
  <2>2. TypeOK /\ P(n) /\ <<Next>>_vars => P(n+1)'
    BY DEF TypeOK, Next, vars
  <2>. QED  BY <2>1, <2>2, Type, Enabled, PTL DEF Spec
<1>3. \A n \in Nat : Q(n)
  <2>. HIDE DEF Q
  <2>. QED  BY <1>1, <1>2, NatInduction, Isa
<1>. QED  BY <1>3

=============================================================================

(***************************************************************************)
(* We define a boring specification with a single variable z that is       *)
(* initialized to 0 and never changes.                                     *)
(***************************************************************************)

Init == z=0
Next == FALSE
Spec == Init /\ [][Next]_z

(***************************************************************************)
(* We now instantiate the specification XY such that both variables x      *)
(* and y are substituted by the variable z.                                *)
(* The instantiated fairness condition is equivalent to the formula        *)
(*   []([](\E xp, yp: xp = z+1 /\ yp = z-1 /\ <<xp,yp>> # <<z,z>>)         *)
(*      => <><<z' = z+1 /\ z' = z-1>>_<<z,z>>)                             *)
(* Observe that the left-hand side of the implication is always true in    *)
(* the presence of the type correctness condition, whereas the right-hand  *)
(* side can never be true. Therefore the instantiated fairness condition   *)
(* is equivalent to FALSE, and so is XY!Spec.                              *)
(***************************************************************************)
XY == INSTANCE XY WITH x <- z, y <- z

LEMMA XY!Fair <=> WF_(XY!vars)(XY!Next)
BY DEF XY!Fair

(***************************************************************************)
(* In contrast, the instantiated next-state action is never enabled.       *)
(***************************************************************************)
LEMMA NotEnabled == XY!TypeOK => ~ ENABLED <<XY!Next>>_(XY!vars)
<1>. SUFFICES ASSUME XY!TypeOK, ENABLED <<XY!Next>>_(XY!vars)
              PROVE  FALSE
  OBVIOUS
<1>1. <<XY!Next>>_(XY!vars) => XY!Next
  OBVIOUS
<1>2. (ENABLED <<XY!Next>>_(XY!vars)) => (ENABLED XY!Next)
  BY ExpandENABLED DEF XY!Next, XY!vars
<1>3. (ENABLED XY!Next) => \E zz : zz = z+1 /\ zz = z-1
  BY ExpandENABLED DEF XY!Next, XY!vars
<1>. QED  BY <1>2, <1>3 DEF XY!TypeOK

(***************************************************************************)
(* TLAPS lets us prove that the boring specification implements the        *)
(* instantiated specification. As we have argued above, the instantiated   *)
(* specification is equivalent to FALSE, whereas Spec is not.              *)
(***************************************************************************)
THEOREM Wrong == Spec => XY!Spec
<1>1. Init => XY!Init
  BY DEF Init, XY!Init
<1>2. [Next]_z => [XY!Next]_(XY!vars)
  BY DEF Next, XY!Next, XY!vars
<1>3. Spec => WF_(XY!vars)(XY!Next)
  <2>. SUFFICES ASSUME []XY!TypeOK, []ENABLED <<XY!Next>>_(XY!vars)
                PROVE  FALSE
    BY <1>1, <1>2, XY!Type, PTL DEF Spec
  <2>. QED  BY NotEnabled, PTL
<1>. QED  BY <1>1, <1>2, <1>3, PTL DEF Spec, XY!Spec

(***************************************************************************)
(* Combining the above refinement theorem and the instantiated liveness    *)
(* theorem, we show an absurdity: for any natural number n, the value of   *)
(* z eventually is both at least n and at most -n.                         *)
(* Note that the theorem XY!Live is still valid because XY!Spec is         *)
(* equivalent to FALSE. The absurdity is a consequence of the wrong        *)
(* refinement theorem.                                                     *)
(***************************************************************************)
COROLLARY Absurd == Spec => \A n \in Nat : <>(z >= n /\ z <= -n)
BY Wrong, XY!Live

=============================================================================
