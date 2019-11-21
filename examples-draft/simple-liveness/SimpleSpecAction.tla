-------------------------- MODULE SimpleSpecAction --------------------------
(***************************************************************************)
(* This module contains the proofs of the action steps in module           *)
(* simpleSpecTrans.tla.                                                    *)
(***************************************************************************)
EXTENDS Integers, FiniteSets, FiniteSetTheorems, WellFoundedInduction, TLAPS

CONSTANT Objects
VARIABLES exit, entry, pool

vars == <<pool, entry, exit>>

Init == /\ pool  = Objects
        /\ entry = {}
        /\ exit  = {}

Add == \E o \in pool : /\ pool'  = pool \ {o}
                       /\ entry' = entry \cup {o}
                       /\ exit'  = exit

Move == /\ exit   = {}
        /\ exit'  = entry
        /\ entry' = {}
        /\ pool'  = pool
        
Remove == \E o \in exit : /\ exit'  = exit \ {o}
                          /\ pool'  = pool \cup {o}
                          /\ entry' = entry

Next == Add \/ Move \/ Remove

Spec == Init /\ [][Next]_vars /\ WF_vars(Move) /\ WF_vars(Remove)

Inv == /\ pool \subseteq Objects
       /\ entry \subseteq Objects
       /\ exit  \subseteq Objects
       /\ IsFiniteSet(entry) 
       /\ IsFiniteSet(exit)



CONSTANT Enabled(_), Box(_)
Diamond(a) == ~ Box(~a)
LeadsTo(a, b) == Box(a => Diamond(b))

UC(v) == v' = v 
Square(A, v) == A \/ UC(v)
Angle(A, v) == A /\ ~ UC(v)
Weak(v, A) == Box(Diamond(~ Enabled(Angle(A,v)))) \/ Box(Diamond(Angle(A,v)))

USE DEF UC, Square, Angle

THEOREM Invariance == Spec => Box(Inv)

USE SMT, Zenon, Isa

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
  PROOF (* BY Invariance DEF Spec *) OMITTED
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
  
<1>x. ASSUME NEW B \in BOOLEAN, NEW c \in FiniteSubsets(Objects)
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
               BY DEF Remove 
            <5>2. IsFiniteSet(exit') 
               BY <5>1,  <1>1, RemoveElementFromFiniteSet DEF Inv
            <5>3. (exit' \subseteq exit) /\ (exit' # exit)  
               BY <5>1  
            <5>4. exit' \in SetLessThan(c, R, S)
               BY <5>2, <5>3 DEF SetLessThan, FiniteSubsets, FiniteSubsetRel 
            <5>5. QED
               BY <5>1, <5>4  DEF Remove 
          <4>2. P => P' \/ Q'
            BY <4>1, <2>2, <1>1 DEF vars, Inv, Add, Move,  Next 
          <4>3. P /\ Angle(Remove, vars) => Q'
            BY <4>1 
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

(* XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX *)
<1> DEFINE OE == o \in entry
<1>2. LeadsTo(OE, OX)
  <2>1. LeadsTo(OE /\ ~(exit = {}), OE /\ (exit = {}))
    <3> DEFINE S == FiniteSubsets(Objects)
               R == FiniteSubsetRel(Objects)
               H(T) == OE /\ (exit = T) 
               G == H({})
    <3>1. IsWellFoundedOn(R, S)
      BY ONLY FiniteSubsetsWellFounded 
    <3>2. ASSUME NEW c \in S
          PROVE  LeadsTo(H(c), G \/ \E d \in SetLessThan(c, R, S) : H(d))
      <4>1. CASE c = {}
        <5>1. G <=> H(c)
          PROOF (* BY ONLY <4>1 *) OMITTED
        <5>2. QED                PROOF OMITTED
      <4>2. CASE c # {}
        <5>1. LeadsTo(H(c), \E d \in SetLessThan(c, R, S) : H(d)) 
          (*****************************************************************)
          (* This is a WF1 proof.                                          *)
          (*****************************************************************)
          <6> DEFINE P == H(c)
                     Q == \E d \in SetLessThan(c, R, S) : H(d)
          <6>1. P /\ Remove => Q'
            <7> SUFFICES ASSUME P /\ Remove
                         PROVE  Q'
             OBVIOUS
            <7>1. PICK x \in exit : exit' = exit \ {x}
              BY DEF Remove
            <7>2. IsFiniteSet(exit') 
              BY <7>1,  <1>1, RemoveElementFromFiniteSet DEF Inv 
            <7>3. (exit' \subseteq exit) /\ (exit' # exit)  
              BY <7>1 
            <7>4. exit' \in SetLessThan(c, R, S)
              BY <7>2, <7>3 DEF SetLessThan, FiniteSubsets, FiniteSubsetRel
            <7>5. QED
              BY <7>1, <7>4  DEF Remove
          <6>2. P => P' \/ Q'
            BY <6>1, <4>2, <1>1 DEF vars, Inv, Add, Move,  Next  
          <6>3. P /\ Angle(Remove, vars) => Q'
            BY <6>1
          <6>4. P => Enabled(Angle(Remove, vars))
            (***************************************************************)
            (* BY <4>2 DEF ENABLED, which produces the following           *)
            (* obligation.                                                 *)
            (***************************************************************)
            <7> P => \E exitp, poolp, entryp :
                        \E oo \in exit : /\ exitp  = exit \ {oo}
                                         /\ poolp  = pool \cup {oo}
                                         /\ entryp = entry
              BY <4>2
             <7> QED PROOF OMITTED
          <6>5. QED     PROOF OMITTED
        <5>2. QED    PROOF OMITTED
      <4>3. QED
        BY <4>1, <4>2
    <3> QED
      <4> HIDE DEF S, R, H, G
      <4>1. LeadsTo(\E c \in S : H(c), G)
        PROOF (* BY ONLY <3>1, <3>2, LeadstoInduction *) OMITTED
      <4>2. OE /\ ~(exit = {}) => \E c \in S : H(c)
        BY ONLY <1>1 DEF H, S, FiniteSubsets, Inv 
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
    <3> USE <1>1
    <3>1. P => P' \/ OX'
      BY ONLY <1>1 DEF Inv, Next, Add, Move, Remove, vars
    <3>2. P /\ Angle(Move, vars) => OX'
      BY ONLY <1>1  DEF Inv, Next, Move, vars
    <3>3. P => Enabled(Angle(Move, vars))
      (*********************************************************************)
      (* BY DEF ENABLED, which produces the following obligation.          *)
      (*********************************************************************)
      <4> P => 
            \E exitp, entryp, poolp : /\ exit   = {}
                                      /\ exitp  = entry
                                      /\ entryp = {}
                                      /\ poolp  = pool
        OBVIOUS
       <4> QED PROOF OMITTED
    <3>4. QED
      PROOF OMITTED
  <2>3. QED                                                                   PROOF 
    (***********************************************************************)
    (* BY ONLY <2>1, <2>2, PTL DEF LeadsTo which is translated to:         *)
    (*   a1 := G(oe & (~xe) -> F(oe & xe)) ;                               *)
    (*   a2 := G(oe & xe -> F ox) ;                                        *)
    (*   goal := G( oe & (~xe) -> F(oe & xe));                             *)
    (*   provable((G a1) & (G a2) -> goal) ;                               *)
    (* which LWB proves.                                                   *)
    (***********************************************************************)
     OMITTED
<1>3. LeadsTo(Box(~OP) /\ OX, FALSE)
  <2> DEFINE H(T) == exit = T
             G == H({})
  <2>1. Box(~OP) /\ OX => Box(OX)
    <3>1. OX /\ ~OP' => OX'
      BY <1>1 DEF Inv, Next, Add, Remove, Move, vars
    <3>2. QED                                                          PROOF
      (*********************************************************************)
      (* BY ONLY <3>1, PTL translates to                                   *)
      (*   a1 := ox & (~ X op) -> X ox ;                                   *)
      (*   goal := G(~ op) & ox -> G(ox) ;                                 *)
      (*   provable( (G a1) -> goal);                                      *)
      (*********************************************************************)
      OMITTED
  <2>2. Box(OX) => LeadsTo(TRUE, G)
    <3> SUFFICES ASSUME Box(OX)
                 PROVE  LeadsTo(TRUE, G)
      PROOF (* BY TLA *) OMITTED
    <3> DEFINE S == FiniteSubsets(Objects)
               R == FiniteSubsetRel(Objects)
    <3>1. IsWellFoundedOn(R, S)
      BY ONLY FiniteSubsetsWellFounded 
    <3>2. ASSUME NEW c \in S
          PROVE  LeadsTo(H(c), G \/ \E d \in SetLessThan(c, R, S) : H(d))
      <4>1. CASE c = {}
        <5>1. G <=> H(c)
          BY ONLY <4>1 
        <5>2. QED                                                      PROOF
          OMITTED
      <4>2. CASE c # {}
        <5>1. LeadsTo(H(c), \E d \in SetLessThan(c, R, S) : H(d)) 
          (*****************************************************************)
          (* This is a WF1 proof.                                          *)
          (*****************************************************************)
          <6> DEFINE P == H(c)
                     Q == \E d \in SetLessThan(c, R, S) : H(d)
          <6>1. P /\ Remove => Q'
            <7> SUFFICES ASSUME P /\ Remove
                         PROVE  Q'
             OBVIOUS
            <7>1. PICK x \in exit : exit' = exit \ {x}
              BY DEF Remove
            <7>2. IsFiniteSet(exit') 
              BY <7>1,  <1>1, RemoveElementFromFiniteSet DEF Inv 
            <7>3. (exit' \subseteq exit) /\ (exit' # exit)  
              BY <7>1 
            <7>4. exit' \in SetLessThan(c, R, S)
              BY <7>2, <7>3 DEF SetLessThan, FiniteSubsets, FiniteSubsetRel
            <7>5. QED
              BY <7>1, <7>4  DEF Remove
          <6>2. P => P' \/ Q'
            BY <6>1, <4>2, <1>1 DEF vars, Inv, Add, Move,  Next  
          <6>3. P /\ Angle(Remove, vars) => Q'
            BY <6>1
          <6>4. P => Enabled(Angle(Remove, vars))
            (***************************************************************)
            (* BY <4>2 DEF ENABLED, which produces the following           *)
            (* obligation.                                                 *)
            (***************************************************************)
            <7> P => \E exitp, poolp, entryp :
                        \E oo \in exit : /\ exitp  = exit \ {oo}
                                         /\ poolp  = pool \cup {oo}
                                         /\ entryp = entry
              BY <4>2
             <7> QED PROOF OMITTED
          <6>5. QED                                                           PROOF
            OMITTED
        <5>2. QED                                                       PROOF
          OMITTED
      <4>3. QED
        PROOF (* BY <4>1, <4>2, TLA *) OMITTED
    <3> QED
      <4> HIDE DEF S, R, H, G
      <4>1. LeadsTo(\E c \in S : H(c), G)
        PROOF (* BY ONLY <3>1, <3>2, LeadstoInduction, TLA *) OMITTED
      <4>2. \E c \in S : H(c)
        BY ONLY <1>1 DEF H, S, FiniteSubsets, Inv 
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
    OBVIOUS
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
         
<1>4. QED                                                                     PROOF
  (*************************************************************************)
  (* BY ONLY <1>2, <1>3, PTL DEF LeadsTo , which translates to             *)
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
\* Last modified Thu Jun 20 05:25:30 PDT 2013 by lamport
\* Created Wed Jun 19 05:09:37 PDT 2013 by lamport
