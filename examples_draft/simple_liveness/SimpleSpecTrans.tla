-------------------------- MODULE SimpleSpecTrans --------------------------
(***************************************************************************)
(* This module contains the TLA Coagulation of steps in the SimpleSpec     *)
(* proof.                                                                  *)
(***************************************************************************)
EXTENDS Integers, FiniteSets, FiniteSetTheorems, WellFoundedInduction, TLAPS

USE SMT, Zenon, Isa

TLA == TRUE
USE DEF TLA
CONSTANT Box(_)
Diamond(a) == ~ Box(~a)
LeadsTo(a, b) == Box(a => Diamond(b))

THEOREM BoxForallCommute ==
          ASSUME NEW S, NEW P(_)
          PROVE  (\A a \in S : Box(P(a))) <=> Box(\A a \in S : P(a))
PROOF OMITTED

THEOREM DiamondExistsCommute ==
          ASSUME NEW S, NEW P(_)
          PROVE  (\E a \in S : Diamond(P(a))) <=> Diamond(\E a \in S : P(a))
<1>1. (\A a \in S : Box(~P(a))) <=> Box(\A a \in S : ~P(a))
  BY BoxForallCommute, TLA
<1>2. QED
  BY <1>1, TLA DEF Diamond

THEOREM LeadsToDisjunctive ==
         ASSUME NEW S, NEW P, NEW Q(_)
         PROVE  LeadsTo(P, \E a \in S : Q(a)) <=> (\E a \in S : LeadsTo(P, Q(a)))
<1>1. (P => Diamond(\E a \in S : Q(a))) <=> (P =>  \E a \in S : Diamond(Q(a)))
  BY DiamondExistsCommute, TLA
<1>2. QED                                                                     PROOF
  (*************************************************************************)
  (* BY <1>1, PTL which (after expanding def of ~> and adding a [] in      *)
  (* front of <1>1) translates to                                          *)
  (*   load(pltl) ;                                                        *)
  (*   a1l := p -> F(eaq) ;                                                *)
  (*   a1r := p -> eadq ;                                                  *)
  (*   a1 := G(a1l <-> a1r) ;                                              *)
  (*   goal := G(p -> F(eaq)) <-> G(p -> eadq) ;                           *)
  (*   provable(a1 -> goal) ;                                              *)
  (* which LWB proves easily.                                              *)
  (*************************************************************************) OMITTED

LEMMA EALeadsTo ==
        ASSUME NEW  S, NEW  H(_), NEW  G
        PROVE  LeadsTo(\E c \in S : H(c), G) <=> (\A c \in S : LeadsTo(H(c), G))
<1> DEFINE P(c) == LeadsTo(H(c), G)
<1>1. ((\E c \in S : H(c)) => Diamond(G)) <=> (\A c \in S : H(c) => Diamond(G))
  BY TLA

<1>2. Box((\E c \in S : H(c)) => Diamond(G)) <=> Box(\A c \in S : H(c) => Diamond(G))
  PROOF
    (***********************************************************************)
    (* By PTL translation, the proof                                       *)
    (*     BY ONLY <1>1                                                    *)
    (* becomes                                                             *)
    (*   ([] <1>1) => <1>2                                                 *)
    (* which by ptl coalescing with                                        *)
    (*   ehc <- (\E c \in S : H(c))                                        *)
    (*   agc <- (\A c \in S : H(c) => <>G))                                *)
    (*   g <- G                                                            *)
    (* becomes                                                             *)
    (*   load(pltl) ;                                                      *)
    (*   a1 := G ( (ehc -> Fg) <-> ahc ) ;                                 *)
    (*   a2 := G (ehc -> Fg) <-> G ahc  ;                                  *)
    (*   provable(a1 -> a2) ;                                              *)
    (* which LWB handles easily.                                           *)
    (***********************************************************************)
    OMITTED
<1>3. Box(\A c \in S : H(c) => Diamond(G)) <=> (\A c \in S : Box(H(c) => Diamond(G)))
  BY BoxForallCommute, TLA
<1>4. QED
  BY <1>2, <1>3, TLA DEF LeadsTo

THEOREM LeadstoInduction ==
          ASSUME NEW  R, NEW  S, IsWellFoundedOn(R, S),
                 NEW  G, NEW  H(_),
                 \A c \in S : LeadsTo(H(c), G \/ \E d \in SetLessThan(c, R, S) : H(d))
          PROVE  LeadsTo(\E c \in S : H(c), G)
<1> SUFFICES ASSUME NEW c \in S
             PROVE  LeadsTo(H(c), G)
  <2> LeadsTo(\E c \in S : H(c), G) <=> \A c\in S : LeadsTo(H(c), G)
     BY EALeadsTo, TLA
  <2> QED
    BY TLA

<1> DEFINE P(x) == LeadsTo(Box(~G) /\ H(x), FALSE)

<1> SUFFICES P(c)                                                            PROOF
   (************************************************************************)
   (* BY PTL translates to                                                 *)
   (*   load(pltl) ;                                                       *)
   (*   pc := G(G(~g) & hc -> F(false)) ;                                  *)
   (*   provable(pc -> G(hc -> F(g))) ;                                    *)
   (* which LWB checks.                                                    *)
   (************************************************************************) OMITTED

<1>1. \A x \in S : (\A y \in SetLessThan(x, R, S) : P(y)) => P(x)
  <2> SUFFICES ASSUME NEW x \in S
               PROVE  (\A y \in SetLessThan(x, R, S) : P(y)) => P(x)
    BY TLA
  <2>1. LeadsTo(H(x), G \/ \E d \in SetLessThan(x, R, S) : H(d))
    BY TLA
  <2>2. LeadsTo(Box(~G) /\ H(x), \E d \in SetLessThan(x, R, S) : Box(~G) /\ H(d))
    (***********************************************************************) PROOF
    (* BY <2>1, PTL                                                        *)
    (*   which translates to                                               *)
    (*     load(pltl) ;                                                    *)
    (*     a1 := G G (hx -> g v ed) ;                                      *)
    (*     a2 := G ( (G ~ g) & hx -> (G ~ g) & ed) ;                      *)
    (*     provable(a1 -> a2) ;                                            *)
    (*   which LWB proves                                                  *)
    (***********************************************************************) OMITTED
  <2>3. \E d \in SetLessThan(x, R, S) : LeadsTo(Box(~G) /\ H(x), Box(~G) /\ H(d))
    <3> DEFINE L == Box(~G) /\ H(x)
               T == SetLessThan(x, R, S)
    <3>1. LeadsTo(L, \E d \in T : Box(~G) /\ H(d))
      BY <2>2, TLA
    <3> HIDE DEF L, T
    <3>2. \E d \in T : LeadsTo(L,  Box(~G) /\ H(d))
      BY ONLY <3>1, LeadsToDisjunctive, TLA
    <3>3. QED
      BY <3>2, TLA DEF L, T
  <2>4. (\A y \in SetLessThan(x, R, S) : P(y)) =>
           \E d \in SetLessThan(x, R, S) :
                        /\ LeadsTo(Box(~G) /\ H(x), Box(~G) /\ H(d))
                        /\ LeadsTo(Box(~G) /\ H(d), FALSE)
    BY <2>3, TLA
  <2>5. ASSUME NEW d
        PROVE  /\ LeadsTo(Box(~G) /\ H(x), Box(~G) /\ H(d))
               /\ LeadsTo(Box(~G) /\ H(d), FALSE)
               => LeadsTo(Box(~G) /\ H(x), FALSE)                             PROOF
    (***********************************************************************)
    (* BY ONLY PTL which translates to                                     *)
    (*   load(pltl) ;                                                      *)
    (*   h1 := G((G ~ g) & hx -> F((G ~ g) & hd)) ;                        *)
    (*   h2 := G((G ~ g) & hd -> F(false));                                *)
    (*   provable(h1 & h2 -> (G((G ~ g) & hx -> F(false)))) ;              *)
    (* which LWB proves.                                                   *)
    (***********************************************************************) OMITTED
  <2>6. QED
    BY <2>4, <2>5, TLA

<1> HIDE DEF P

<1>2. QED
  <2> DEFINE Foo(RR, SS) ==
             \A x \in SS :
                 (\A y \in SetLessThan(x, RR, SS) : P(y)) => P(x)
  <2>1.  ASSUME NEW RR, NEW SS,
                IsWellFoundedOn(RR, SS),
                Foo(RR, SS)
        PROVE  \A x \in SS : P(x)
    BY ONLY <2>1, WFInduction, TLA
  <2>2.  Foo(R, S) /\ IsWellFoundedOn(R, S)
    BY <1>1, TLA
  <2> HIDE DEF Foo
  <2>3.  QED
   BY ONLY <2>1, <2>2, TLA

CONSTANT Objects
VARIABLES exit, entry, pool
CONSTANT UC(_) (* UNCHANGED *), Enabled(_), Init, Add, Move, Remove, vars, Inv
Next == Add \/ Move \/ Remove

Square(A, v) == A \/ UC(v)
Angle(A, v) == A /\ ~ UC(v)
Weak(v, A) == Box(Diamond(~ Enabled(Angle(A,v)))) \/ Box(Diamond(Angle(A,v)))
Spec == Init /\ Box(Square(Next, vars)) /\ Weak(vars, Move) /\ Weak(vars, Remove)

THEOREM Invariance == Spec => Box(Inv)

-----------------------------------------------------------------------------
FiniteSubsets(S) == {T \in SUBSET S : IsFiniteSet(T)}
FiniteSubsetRel(S) == {T \in FiniteSubsets(S) \X FiniteSubsets(S) :
                         (T[1] \subseteq T[2]) /\ (T[1] # T[2]) }
THEOREM FiniteSubsetsWellFounded ==
           \A S : IsWellFoundedOn(FiniteSubsetRel(S), FiniteSubsets(S))
-----------------------------------------------------------------------------

THEOREM Liveness ==
          Spec => \A o \in Objects : LeadsTo((o \in entry), (o \in pool))

(***************************************************************************)
(* The following should be a []ASSUME/[]PROVE.                             *)
(***************************************************************************)
<1> SUFFICES ASSUME Box(Inv) /\ Box(Square(Next, vars))
                       /\ Weak(vars, Move) /\ Weak(vars, Remove),
                    NEW o \in Objects
             PROVE LeadsTo(o \in entry, o \in pool)
  BY Invariance DEF Spec
<1> DEFINE \* OE == o \in entry
           OX == o \in exit
           OP == o \in pool
<1>1. Inv /\ Square(Next, vars)                                               PROOF
  (*************************************************************************)
  (* BY PTL , which translates to                                          *)
  (*   a := G(inv) & G(next v ucvars) & wfm & wfr ;                        *)
  (*   provable(Ga -> inv & (next v ucvars)) ;                             *)
  (* which is proved by LWB.                                               *)
  (*************************************************************************)
  OMITTED

<1>2. ASSUME NEW B \in BOOLEAN, NEW c \in FiniteSubsets(Objects)
  PROVE  LET S == FiniteSubsets(Objects)
             R == FiniteSubsetRel(Objects)
             OE == (B => o \in entry)
             H(T) == OE /\ (exit = T)
             G == H({})
         IN LeadsTo(H(c), G \/ \E d \in SetLessThan(c, R, S) : H(d))
  <2> DEFINE S == FiniteSubsets(Objects)
             R == FiniteSubsetRel(Objects)
             OE == (B => o \in entry)
             H(T) == OE /\ (exit = T)
             G == H({})
  <2>a. IsWellFoundedOn(R, S)
    BY ONLY FiniteSubsetsWellFounded
  <2>1. CASE c = {}
    <3>1. G <=> H(c)
      PROOF (* BY ONLY <2>1, TLA *) OMITTED
    <3>2. QED                                                      PROOF
      (*****************************************************************)
      (* BY ONLY <3>1, PTL , which translates to                       *)
      (*   g := oe & exitempty ;                                       *)
      (*   hc := oe & exitc ;                                          *)
      (*   a1 := g <-> hc ;                                            *)
      (*   goal := G( hc -> (g v existsd)) ;                           *)
      (*   provable(G a1 -> goal ) ;                                   *)
      (* which LWB proves.                                             *)
      (*****************************************************************)
      OMITTED
  <2>2. CASE c # {}
    <3>1. LeadsTo(H(c), \E d \in SetLessThan(c, R, S) : H(d))
      (*****************************************************************)
      (* This is a WF1 proof.                                          *)
      (*****************************************************************)
      <4> DEFINE P == H(c)
                 Q == \E d \in SetLessThan(c, R, S) : H(d)
      <4>1. P /\ Remove => Q'
        <5> SUFFICES ASSUME P /\ Remove
                     PROVE  Q'
          OBVIOUS
        <5>1. PICK x \in exit : exit' = exit \ {x}
           PROOF (* BY DEF Remove *) OMITTED
        <5>2. IsFiniteSet(exit')
           PROOF (* BY <5>1,  <1>1, RemoveElementFromFiniteSet DEF Inv *) OMITTED
        <5>3. (exit' \subseteq exit) /\ (exit' # exit)
           PROOF (* BY <5>1*) OMITTED
        <5>4. exit' \in SetLessThan(c, R, S)
           PROOF (* BY <5>2, <5>3 DEF SetLessThan, FiniteSubsets, FiniteSubsetRel *) OMITTED
        <5>5. QED
           PROOF (* BY <5>1, <5>4  DEF Remove *) OMITTED
      <4>2. P => P' \/ Q'
        PROOF (* BY <4>1, <2>2, <1>1 DEF vars, Inv, Add, Move,  Next *) OMITTED
      <4>3. P /\ Angle(Remove, vars) => Q'
        BY <4>1 DEF Angle
      <4>4. P => Enabled(Angle(Remove, vars))                      PROOF
        (***************************************************************)
        (* BY <2>2 DEF ENABLED, which produces the following           *)
        (* obligation.                                                 *)
        (*   <5> P => \E exitp, poolp, entryp :                        *)
        (*               \E oo \in exit : /\ exitp  = exit \ {oo}      *)
        (*                                /\ poolp  = pool \cup {oo}   *)
        (*                                /\ entryp = entry            *)
        (*     BY <2>2                                                 *)
        (***************************************************************)
        OMITTED
      <4>5. QED                                                           PROOF
        (***************************************************************)
        (* BY <4>2, <4>3, <4>4, PTL DEF Weak, LeadsTo -- which         *)
        (* translates to                                               *)
        (*   The following are the assumptions from <1> SUFFICES...    *)
        (*     amove := move & (~ ucvars) ;                            *)
        (*     aremove := rmove & (~ ucvars) ;                         *)
        (*     wfm := (G F (~ eamove)) v (G F amove) ;                 *)
        (*     wfr := (G F (~ earemove)) v (G F aremove) ;             *)
        (*     ass := G(inv) & G(next v ucvars) & wfm & wfr ;          *)
        (*   p := oe & exitc ;                                         *)
        (*   a1 := p -> (X p) v (X q) ;                                *)
        (*   a2 := p & amove -> (X q) ;                                *)
        (*   a3 := p -> eamove ;                                       *)
        (*   goal := G(oe & exitc -> F q) ;                            *)
        (*   provable ((G ass) & (G a1) & (G a2) & (G a3) -> goal) ;   *)
        (* which LWB easily proves.                                    *)
        (***************************************************************)
   OMITTED
    <3>2. QED                                                       PROOF
      (*****************************************************************)
      (* BY ONLY <3>1, PTL , which translates to                       *)
      (*   a1 := G (oe & exitc -> F existsd) ;                         *)
      (*   goal := G(oe & exitc -> F ((oe & exitempty) v existsd)) ;   *)
      (*   provable( (G a1) -> goal) ;                                 *)
      (* which LWB proves.                                             *)
      (*****************************************************************)
      OMITTED
  <2>3. QED
    PROOF (* BY <2>1, <2>2, TLA *) OMITTED

<1> DEFINE OE == o \in entry
<1>3. LeadsTo(OE, OX)
  <2>1. LeadsTo(OE /\ ~(exit = {}), OE /\ (exit = {}))
    <3> DEFINE S == FiniteSubsets(Objects)
               R == FiniteSubsetRel(Objects)
               H(T) == OE /\ (exit = T)
               G == H({})
    <3>1. IsWellFoundedOn(R, S)
      BY ONLY FiniteSubsetsWellFounded
    <3>2. ASSUME NEW c \in S
          PROVE  LeadsTo(H(c), G \/ \E d \in SetLessThan(c, R, S) : H(d))
      BY <1>2, TLA
    <3> QED
      <4> HIDE DEF S, R, H, G
      <4>1. LeadsTo(\E c \in S : H(c), G)
        BY ONLY <3>1, <3>2, LeadstoInduction, TLA
      <4>2. OE /\ ~(exit = {}) => \E c \in S : H(c)                     PROOF
      (*********************************************************************)
      (* BY ONLY <1>1 DEF H, S, FiniteSubsets, Inv [Action Reasoning]      *)
      (*********************************************************************)
      OMITTED
      <4>3. QED                                                      PROOF
      (*********************************************************************)
      (* BY ONLY <4>1, <4>2, PTL DEF G, H, LeadsTo, which translates to    *)
      (*   a1 := G(existsc -> F(oe & exitempty)) ;                         *)
      (*   a2 := G((oe & ~ exitempty) -> F existsc) ;                      *)
      (*   goal := G((oe & ~ exitempty) -> F (oe & exitempty)) ;           *)
      (*   provable((Ga1) & G(a2) -> goal) ;                               *)
      (* which is proved by LWB.                                           *)
      (*********************************************************************)
      OMITTED
  <2>2. LeadsTo(OE /\ (exit = {}), OX)
    (***********************************************************************)
    (* This is a proof by WF1.                                             *)
    (***********************************************************************)
    <3> DEFINE P == OE /\ (exit = {})
    <3>1. P => P' \/ OX'                                                PROOF
      (*********************************************************************)
      (* BY ONLY <1>1 DEF Inv, Next, Add, Move, Remove, vars               *)
      (*  [Action reasoning]                                               *)
      (*********************************************************************)
      OMITTED
    <3>2. P /\ Angle(Move, vars) => OX'                                PROOF
      (*********************************************************************)
      (* BY ONLY <1>1 DEF Inv, Next, Move, vars [Action reasoning]         *)
      (*********************************************************************)
      OMITTED
    <3>3. P => Enabled(Angle(Move, vars))                              PROOF
      (*********************************************************************)
      (* BY DEF ENABLED [Action reasoning]                                 *)
      (*********************************************************************)
      OMITTED
    <3>4. QED                                                           PROOF
      (*********************************************************************)
      (* BY <3>1, <3>2, <3>3, PTL DEF Weak, LeadsTo -- which translates to *)
      (*   The following are the assumptions from <1> SUFFICES...          *)
      (*     amove := move & (~ ucvars) ;                                  *)
      (*     aremove := rmove & (~ ucvars) ;                               *)
      (*     wfm := (G F (~ eamove)) v (G F amove) ;                       *)
      (*     wfr := (G F (~ earemove)) v (G F aremove) ;                   *)
      (*     ass := G(inv) & G(next v ucvars) & wfm & wfr ;                *)
      (*   p := oe & ex ;                                                  *)
      (*   a1 := p -> (X p) v (X ox) ;                                     *)
      (*   a2 := p & amove -> (X ox) ;                                     *)
      (*   a3 := p -> eamove ;                                             *)
      (*   goal := G(oe & ex -> F ox) ;                                    *)
      (*   provable ((G ass) & (G a1) & (G a2) & (G a3) -> goal) ;         *)
      (* which LWB easily proves.                                          *)
      (*********************************************************************)
       OMITTED
  <2>3. QED                                                             PROOF
    (***********************************************************************)
    (* BY ONLY <2>1, <2>2, PTL DEF LeadsTo which is translated to:         *)
    (*   a1 := G(oe & (~xe) -> F(oe & xe)) ;                               *)
    (*   a2 := G(oe & xe -> F ox) ;                                        *)
    (*   goal := G( oe & (~xe) -> F(oe & xe));                             *)
    (*   provable((G a1) & (G a2) -> goal) ;                               *)
    (* which LWB proves.                                                   *)
    (***********************************************************************)
     OMITTED

<1>4. LeadsTo(Box(~OP) /\ OX, FALSE)
  <2>1. Box(~OP) /\ OX => Box(OX)
    <3>1. OX /\ ~OP' => OX'
      PROOF (* BY <1>1 DEF Inv, Next, Add, Remove, Move, vars *) OMITTED
    <3>2. QED                                                          PROOF
      (*********************************************************************)
      (* BY ONLY <3>1, PTL translates to                                   *)
      (*   a1 := ox & (~ X op) -> X ox ;                                   *)
      (*   goal := G(~ op) & ox -> G(ox) ;                                 *)
      (*   provable( (G a1) -> goal);                                      *)
      (*********************************************************************)
      OMITTED
  <2> DEFINE H(T) == (exit = T)
             G == H({})
  <2>2. Box(OX) => LeadsTo(TRUE, G)
    <3> SUFFICES ASSUME Box(OX)
                 PROVE  LeadsTo(TRUE, G)
      BY TLA
    <3> DEFINE S == FiniteSubsets(Objects)
               R == FiniteSubsetRel(Objects)
    <3>1. IsWellFoundedOn(R, S)
      BY ONLY FiniteSubsetsWellFounded
    <3>2. ASSUME NEW c \in S
          PROVE  LeadsTo(H(c), G \/ \E d \in SetLessThan(c, R, S) : H(d))
      BY <1>2, TLA
    <3> QED
      <4> HIDE DEF S, R, H, G
      <4>1. LeadsTo(\E c \in S : H(c), G)
        BY ONLY <3>1, <3>2, LeadstoInduction, TLA
      <4>2. \E c \in S : H(c)
        PROOF (* BY ONLY <1>1 DEF H, S, FiniteSubsets, Inv *) OMITTED
      <4>3. QED                                                      PROOF
      (*********************************************************************)
      (* BY ONLY <4>1, <4>2, PTL DEF G, H, LeadsTo, which translates to    *)
      (*   a1 := G(existsc -> F(exitempty)) ;                              *)
      (*   a2 := existsc ;                                                 *)
      (*   goal := G(true -> F(exitempty)) ;                               *)
      (*   provable((Ga1) & G(a2) -> goal) ;                               *)
      (* which is proved by LWB.                                           *)
      (*********************************************************************)
      OMITTED
  <2>3. G => ~OX
    PROOF (* OBVIOUS *) OMITTED
  <2>4. QED                                                             PROOF
    (***********************************************************************)
    (* BY ONLY <2>1, <2>2, <2>3, PTL, which translates to                  *)
    (*   a1 := G(~op) & ox -> G(ox) ;                                      *)
    (*   a2 := G(ox) -> G(true -> F g) ;                                   *)
    (*   a3 := g -> ~ox ;                                                  *)
    (*   goal := G(G(~op) & ox -> F(false)) ;                              *)
    (*   provable((G a1) & (G a2) & (G a3) -> goal) ;                      *)
    (* which LWB proves.                                                   *)
    (***********************************************************************)
    OMITTED

<1>5. QED                                                                     PROOF
  (*************************************************************************)
  (* BY ONLY <1>3, <1>4, PTL DEF LeadsTo , which translates to             *)
  (*   load(pltl) ;                                                        *)
  (*   a1 := G(oe -> F ox);                                                *)
  (*   a2 := G(G(~op) & ox -> F false);                                    *)
  (*   goal := G(oe -> F op);                                              *)
  (*   provable((G a1) & (G a2) -> goal);                                  *)
  (* which LWB proves                                                      *)
  (*************************************************************************)
  OMITTED
=============================================================================
\* Modification History
\* Last modified Wed Jul 03 07:38:12 PDT 2013 by lamport
\* Created Tue Jun 18 04:40:49 PDT 2013 by lamport
