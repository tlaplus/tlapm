----------------------------- MODULE SimpleSpec -----------------------------
(***************************************************************************)
(* This module is a test of writing formal liveness proofs.  It specifies  *)
(* a simple hardware scheme for implementing fair service.  There are      *)
(* three buckets, each of which can contain a set of objects, arranged     *)
(* like this:                                                              *)
(*   `.                                                                    *)
(*             ------           -------           ------                   *)
(*        .-->| pool |  ---->  | entry |  ---->  | exit | ---.             *)
(*        |    ------           -------           ------     |             *)
(*        |                                                  |             *)
(*         '-------------------------------------------------'        .'   *)
(*                                                                         *)
(* Objects start in `pool', and are put into `entry' by the Add action.    *)
(* When `exit' is empty, all objects in `entry' can be moved to `exit' by  *)
(* a Move action.  Objects in `exit' are moved back to `pool' by a Remove  *)
(* action.  The purpose of this exercise is to prove that weak fairness of *)
(* the Move and Remove actions imply that any object in Entry eventually   *)
(* winds up back in Pool.                                                  *)
(***************************************************************************)
EXTENDS Integers, FiniteSets, FiniteSetTheoremsLL, WellFoundedInduction, TLAPS

(***************************************************************************)
(* The following added because FiniteSetTheorems has changed since this    *)
(* module was written and checked.                                         *)
(***************************************************************************)

\*EmptySetFinite == TRUE
\*RemoveElementFromFiniteSet == TRUE
\*AddElementFiniteSet == TRUE


CONSTANT Objects  
  (*************************************************************************)
  (* The set of all objects.  We don't assume it to be finite.             *)
  (*************************************************************************)
  
(***************************************************************************)
(* The variables representing the set of objects in each bucket.           *)
(***************************************************************************)
VARIABLES pool, entry, exit

vars == <<pool, entry, exit>>

(***************************************************************************)
(* Initially, all objects are in pool.                                     *)
(***************************************************************************)
Init == /\ pool  = Objects
        /\ entry = {}
        /\ exit  = {}

(***************************************************************************)
(* The operation of moving an object from pool to entry.                   *)
(***************************************************************************)
Add == \E o \in pool : /\ pool'  = pool \ {o}
                       /\ entry' = entry \cup {o}
                       /\ exit'  = exit

(***************************************************************************)
(* The operation of moving all the objects from exit to pool.              *)
(***************************************************************************)
Move == /\ exit   = {}
        /\ exit'  = entry
        /\ entry' = {}
        /\ pool'  = pool

(***************************************************************************)
(* The operation of moving an object from exit to pool.                    *)
(***************************************************************************)        
Remove == \E o \in exit : /\ exit'  = exit \ {o}
                          /\ pool'  = pool \cup {o}
                          /\ entry' = entry

Next == Add \/ Move \/ Remove

Spec == Init /\ [][Next]_vars /\ WF_vars(Move) /\ WF_vars(Remove)

(***************************************************************************)
(* The invariant, essentially just stating type correctness.               *)
(***************************************************************************)
Inv == /\ pool  \subseteq Objects
       /\ entry \subseteq Objects
       /\ exit  \subseteq Objects
       /\ IsFiniteSet(entry) 
       /\ IsFiniteSet(exit)

(***************************************************************************)
(* The statement and proof that Inv is an invariant.                       *)
(***************************************************************************)
THEOREM Invariance == Spec => []Inv
<1>1. Init => Inv
  BY EmptySetFinite, SMT DEF Init, Inv
<1>2. Inv /\ [Next]_vars => Inv'
  <2>1. ASSUME Inv,
               NEW o \in pool,
               /\ pool'  = pool \ {o}
               /\ entry' = entry \cup {o}
               /\ exit'  = exit
        PROVE  Inv'
    <3>1. (pool \subseteq Objects)'
      BY <2>1, AddElementFiniteSet, RemoveElementFromFiniteSet, SMT DEF Inv, Next, vars, Add, Move, Remove
    <3>2. (entry \subseteq Objects)'
      BY <2>1, AddElementFiniteSet, RemoveElementFromFiniteSet, SMT DEF Inv, Next, vars, Add, Move, Remove
    <3>3. (exit  \subseteq Objects)'
      BY <2>1, AddElementFiniteSet, RemoveElementFromFiniteSet, SMT DEF Inv, Next, vars, Add, Move, Remove
    <3>4. IsFiniteSet(entry)'
      BY <2>1, AddElementFiniteSet, RemoveElementFromFiniteSet DEF Inv, Next, vars, Add, Move, Remove
    <3>5. IsFiniteSet(exit)'
      BY <2>1, AddElementFiniteSet, RemoveElementFromFiniteSet, SMT DEF Inv, Next, vars, Add, Move, Remove
    <3>6. QED
      BY <3>1, <3>2, <3>3, <3>4, <3>5 DEF Inv
    
  <2>2. ASSUME Inv,
               Move
        PROVE  Inv'
    BY <2>2, AddElementFiniteSet, RemoveElementFromFiniteSet, SMT DEF Inv, Next, vars, Add, Move, Remove
  <2>3. ASSUME Inv,
               NEW o \in exit,
               /\ exit'  = exit \ {o}
               /\ pool'  = pool \cup {o}
               /\ entry' = entry
        PROVE  Inv'
    BY <2>3, AddElementFiniteSet, RemoveElementFromFiniteSet, SMT DEF Inv, Next, vars, Add, Move, Remove
  <2>4. ASSUME Inv,
               UNCHANGED vars
        PROVE  Inv'
    BY <2>4, AddElementFiniteSet, RemoveElementFromFiniteSet, SMT DEF Inv, Next, vars, Add, Move, Remove
  <2>5. QED
    BY <2>1, <2>2, <2>3, <2>4 DEF Next, Add, Remove
<1>3. QED
  PROOF
  BY <1>1, <1>2, PTL DEF Spec

-----------------------------------------------------------------------------
(***************************************************************************)
(*                             LIVENESS                                    *)
(*                                                                         *)
(* This is how we hope liveness will be proved.  The proofs assume two     *)
(* "backends" LS4 and TLA.                                                 *)
(*                                                                         *)
(* LS4: This is a translation into a propositional temporal logic prover,  *)
(* such as the pltl theory of the Logical Workbench (LWB).  Coagulation is *)
(* done so that the only operators that are visible are [], <>, and the    *)
(* Boolean operators (/\ , => , ~, etc.).  It is assumed that ~> is        *)
(* translated into its definition in terms of [] and <>, but WF is not     *)
(* unless DEF WF is specified.  (DEF WF is not now accepted by the parser, *)
(* and some other syntax might be used instead.)                           *)
(*                                                                         *)
(* TLA: This is a translation in which coagulation is performed so the     *)
(* only visible operators are the temporal operators, Boolean operators,   *)
(* quantifiers over constants, and constant expressions.  The coagulated   *)
(* expression is then given to the ordinary backends (SMT, Zenon, etc.) as *)
(* usual.                                                                  *)
(*                                                                         *)
(* I also assume that DEF ENABLED causes each ENABLED expression to be     *)
(* replaced by the equivalent existential quantification, suitably         *)
(* coagulated.  (Again, this is not necessarily the final syntax.)         *)
(*                                                                         *)
(* The file SimpleSpecTrans.tla contains the statements and proofs in a    *)
(* form in which temporal operators are defined in terms of a primitive    *)
(* Box operator, that represents [] as a constant operator.  All the       *)
(* proofs that are BY TLA are written as ordinary proofs that have been    *)
(* checked by the TLAPS.  I tried to make the proof obligations checked in *)
(* this way equivalent to the ones that will be produced after the TLA     *)
(* coagulation.  I may have left some non-constant expressions exposed,    *)
(* but I doubt if they were of any use to the prover and the proofs will   *)
(* work when those expressions are suitably coagulated.  For each BY LS4   *)
(* proof, that file also contains the LWB input into which the obligation  *)
(* could be translated; and that input has been successfully checked with  *)
(* the LWB.  Ordinary action obligations from SimpleSpecTrans.tla have     *)
(* been checked in the file SimpleSpecAction.tla.  (SimpleSpecTrans.tla    *)
(* doesn't contain the definitions of the actions Add, Move, and Remove    *)
(* and the predicates Init and Inv.)                                       *)
(*                                                                         *)
(* Because TLAPS doesn't yet support []ASSUME / []PROVE, these are not     *)
(* written explicitly.  However, every ASSUME / PROVE with a temporal      *)
(* assumption or goal is actually a []ASSUME / []PROVE, and this fact was  *)
(* used in the LS4 translations to LWB.                                    *)
(***************************************************************************)
USE SMT, Zenon, Isa

TLA == TRUE

-----------------------------------------------------------------------------
(***************************************************************************)
(* Here are some useful properties of the temporal operator that are       *)
(* proved using BY TLA and a little action reasoning--except for the       *)
(* first, which is taken to be an axiom.  These properties should be in    *)
(* some library file--perhaps even in TLAPS.                               *)
(***************************************************************************)
THEOREM BoxForallCommute ==
           ASSUME NEW CONSTANT S, NEW TEMPORAL P(_)
           PROVE  (\A a \in S : [] P(a)) <=> [](\A a \in S : P(a))
PROOF OMITTED

THEOREM DiamondExistsCommute ==
          ASSUME NEW CONSTANT S, NEW TEMPORAL P(_)
          PROVE  (\E a \in S : <>(P(a))) <=> <>(\E a \in S : P(a))
<1>1. (\A a \in S : [](~P(a))) <=> [](\A a \in S : ~P(a))
  BY BoxForallCommute, TLA
<1>2. QED 
  BY <1>1, TLA (* DEF <> *)

(* I believe the QED step cannot be proved by PTL (TL) *)
(* SM: In fact, this is not a theorem at all. Trivializing P to TRUE, it 
   would imply 
   []<>(\E a \in S : Q(a)) <=> (\E a \in S : []<>Q(a))
   which is clearly invalid: the LHS asserts that infinitely often there
   is some a \in S for which Q(a) holds whereas the RHS claims that for
   some (fixed) a \in S, Q(a) holds infinitely often. This equivalence
   holds only for finite S and in that case requires a different proof
   by induction over finite sets.
*)
THEOREM LeadsToDisjunctive ==
         ASSUME NEW S, NEW TEMPORAL P, NEW TEMPORAL Q(_)
         PROVE  (P ~> (\E a \in S : Q(a))) <=> (\E a \in S : P ~> Q(a))
<1>1. (P => <>(\E a \in S : Q(a))) <=> (P =>  \E a \in S : <>(Q(a)))
  BY DiamondExistsCommute, TLA
<1>2. QED  
  BY <1>1, PTL


LEMMA EALeadsTo == 
        ASSUME NEW  S, NEW  H(_), NEW  G
        PROVE  (\E c \in S : H(c) ~> G) <=> (\A c \in S : H(c) ~> G)
<1> DEFINE P(c) == H(c) ~> G
<1>1. ((\E c \in S : H(c)) => <>(G)) <=> (\A c \in S : H(c) => <>(G))
  BY TLA 
<1>2. []((\E c \in S : H(c)) => <>(G)) <=> [](\A c \in S : H(c) => <>(G))
  BY <1>1, PTL
<1>3. [](\A c \in S : H(c) => <>(G)) <=> (\A c \in S : [](H(c) => <>(G))) 
  BY BoxForallCommute, TLA
<1>4. QED      
  BY <1>2, <1>3, TLA (* DEF ~> *) 

(***************************************************************************)
(* Here is the rule that I used to call the Lattice Rule.                  *)
(***************************************************************************)

THEOREM LeadstoInduction ==
          ASSUME NEW  R, NEW  S, IsWellFoundedOn(R, S),
                 NEW  TEMPORAL G, NEW  TEMPORAL H(_),
                 \A c \in S : H(c) ~> (G \/ \E d \in SetLessThan(c, R, S) : H(d))
          PROVE  (\E c \in S : H(c)) ~> G
<1> SUFFICES ASSUME NEW c \in S
             PROVE  H(c) ~> G
  <2> ((\E c \in S : H(c)) ~> G) <=> (\A c\in S : H(c) ~> G)
     BY EALeadsTo
  <2> QED
    OBVIOUS
    
<1> DEFINE P(x) == [](~G) /\ H(x) ~> FALSE

<1> SUFFICES P(c)    
  BY PTL 

<1>1. \A x \in S : (\A y \in SetLessThan(x, R, S) : P(y)) => P(x)
  <2> SUFFICES ASSUME NEW x \in S
               PROVE  (\A y \in SetLessThan(x, R, S) : P(y)) => P(x)        
    BY TLA
  <2>1. H(x) ~>  G \/ (\E d \in SetLessThan(x, R, S) : H(d))
    BY TLA
  <2>2. [](~G) /\ H(x) ~> []~G /\ (\E d \in SetLessThan(x, R, S) : H(d))
    BY <2>1, PTL 
  <2>3. \E d \in SetLessThan(x, R, S) : [](~G) /\ H(x) ~> [](~G) /\ H(d)
    <3> DEFINE L == [](~G) /\ H(x)
               T == SetLessThan(x, R, S)
    <3>1. L ~> (\E d \in T : [](~G) /\ H(d))
      BY <2>2, TLA
    <3> HIDE DEF L, T
    <3>2. \E d \in T : L ~> [](~G) /\ H(d)
      BY ONLY <3>1, LeadsToDisjunctive, TLA
    <3>3. QED
      BY <3>2 DEF L, T
  <2>4. (\A y \in SetLessThan(x, R, S) : P(y)) =>
           \E d \in SetLessThan(x, R, S) : 
                        /\ [](~G) /\ H(x) ~> [](~G) /\ H(d)
                        /\ [](~G) /\ H(d) ~> FALSE
    BY <2>3, TLA
  <2>5. ASSUME NEW d
        PROVE  /\ [](~G) /\ H(x) ~> [](~G) /\ H(d)
               /\ [](~G) /\ H(d) ~> FALSE
               => [](~G) /\ H(x) ~> FALSE     
     BY ONLY PTL 
  <2>6. QED
    BY <2>4, <2>5

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

-----------------------------------------------------------------------------
(***************************************************************************)
(* The proof of liveness uses the well-foundedness of the subset relation  *)
(* on finite sets.  This fact should be stated in a library file (probably *)
(* a file of definitions and facts about well-foundedness).  I just assume *)
(* it here.                                                                *)
(***************************************************************************)
FiniteSubsets(S) == {T \in SUBSET S : IsFiniteSet(T)}
FiniteSubsetRel(S) == {x \in FiniteSubsets(S) \X FiniteSubsets(S) :
                         (x[1] \subseteq x[2]) /\ (x[1] # x[2]) }
THEOREM FiniteSubsetsWellFounded ==
           \A S : IsWellFoundedOn(FiniteSubsetRel(S), FiniteSubsets(S))
PROOF OMITTED
-----------------------------------------------------------------------------

(***************************************************************************)
(* Here is the liveness result.                                            *)
(***************************************************************************)
THEOREM Liveness == Spec =>  \A o \in Objects : (o \in entry) ~> (o \in pool)

<1> SUFFICES ASSUME []Inv /\ [][Next]_vars /\ WF_vars(Move) /\ WF_vars(Remove),
                    NEW o \in Objects
             PROVE (o \in entry) ~> (o \in pool)
  BY Invariance DEF Spec
<1>1. Inv /\ [Next]_vars                                              
  BY PTL

(***************************************************************************)
(* Steps <1>3 and <1>4 use leads-to properties that are similar and have   *)
(* essentially the same proof.  Those two properties are both expressed as *)
(* the following property, for the two possible Boolean values of B.       *)
(***************************************************************************)
<1>2. ASSUME NEW B \in BOOLEAN, NEW c \in FiniteSubsets(Objects)
  PROVE  LET S == FiniteSubsets(Objects)
             R == FiniteSubsetRel(Objects)
             OE == (B => o \in entry) 
             H(T) == OE /\ (exit = T) 
             G == H({})
         IN H(c) ~> (G \/ \E d \in SetLessThan(c, R, S) : H(d))
  <2> DEFINE S == FiniteSubsets(Objects)
             R == FiniteSubsetRel(Objects)
             OE == (B => o \in entry) 
             H(T) == OE /\ (exit = T) 
             G == H({})
  <2>1. IsWellFoundedOn(R, S)
    BY ONLY FiniteSubsetsWellFounded
  <2>2. CASE c = {}
    <3>1. G <=> H(c)
      BY ONLY <2>2, TLA
    <3>2. QED                                                   
      BY ONLY <3>1, PTL
  <2>3. CASE c # {}
    <3>1. H(c) ~> (\E d \in SetLessThan(c, R, S) : H(d)) 
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
           BY <5>1, <1>1, RemoveElementFromFiniteSet DEF Inv 
        <5>3. (exit' \subseteq exit) /\ (exit' # exit)  
           BY <5>1  
        <5>4. exit' \in SetLessThan(c, R, S)
           BY <5>2, <5>3 DEF SetLessThan, FiniteSubsets, FiniteSubsetRel  
        <5>5. QED
           BY <5>1, <5>4  DEF Remove
      <4>2. P => P' \/ Q'
        BY <4>1, <2>3, <1>1 DEF vars, Inv, Add, Move,  Next 
      <4>3. P /\ <<Remove>>_vars => Q'
        BY <4>1 
      <4>4. P => ENABLED <<Remove>>_vars                      
        BY <2>3 (* DEF ENABLED *)
      <4>5. QED                                                           
        BY <4>2, <4>3, <4>4, PTL (* DEF WF *)
    <3>2. QED                                                    
      BY ONLY <3>1, PTL
  <2>4. QED
    BY <2>2, <2>3, TLA

<1> DEFINE OX == o \in exit
           OP == o \in pool

<1> DEFINE OE == o \in entry
<1>3. OE ~> OX
  <2>1. (OE /\ ~(exit = {})) ~> (OE /\ (exit = {}))
    <3> DEFINE S == FiniteSubsets(Objects)
               R == FiniteSubsetRel(Objects)
               H(T) == OE /\ (exit = T) 
               G == H({})
    <3>1. IsWellFoundedOn(R, S)
      BY ONLY FiniteSubsetsWellFounded
    <3>2. ASSUME NEW c \in S
          PROVE  H(c) ~> (G \/ \E d \in SetLessThan(c, R, S) : H(d))
      BY <1>2, TLA   
    <3> QED
      <4> HIDE DEF S, R, H, G
      <4>1. (\E c \in S : H(c)) ~> G
        BY ONLY <3>1, <3>2, LeadstoInduction, TLA
      <4>2. OE /\ ~(exit = {}) => \E c \in S : H(c) 
        BY ONLY <1>1 DEF H, S, FiniteSubsets, Inv
      <4>3. QED                                                      
        BY ONLY <4>1, <4>2, PTL DEF G, H
  <2>2. (OE /\ (exit = {})) ~> OX
    (***********************************************************************)
    (* This is a proof by WF1.                                             *)
    (***********************************************************************)
    <3> DEFINE P == OE /\ (exit = {})
    <3>1. P => P' \/ OX'  
      BY ONLY <1>1 DEF Inv, Next, Add, Move, Remove, vars 
    <3>2. P /\ <<Move>>_vars => OX' 
      BY ONLY <1>1 DEF Inv, Next, Move, vars 
    <3>3. P => ENABLED <<Move>>_vars                           
      (* BY DEF ENABLED *)
      OMITTED
    <3>4. QED                                                           
      BY <3>1, <3>2, <3>3, PTL (* DEF WF *)
  <2>3. QED                                                             
    BY ONLY <2>1, <2>2, PTL

<1>4. [](~OP) /\ OX ~> FALSE
  <2>1. [](~OP) /\ OX => [](OX)
    <3>1. OX /\ ~OP' => OX'
       BY <1>1 DEF Inv, Next, Add, Remove, Move, vars  
    <3>2. QED                                                          
      BY ONLY <3>1, PTL
  <2> DEFINE H(T) == (exit = T) 
             G == H({})
  <2>2. [](OX) => (TRUE ~> G)   
    <3> SUFFICES ASSUME [](OX)
                 PROVE  TRUE ~> G
      BY PTL
    <3> DEFINE S == FiniteSubsets(Objects)
               R == FiniteSubsetRel(Objects)
    <3>1. IsWellFoundedOn(R, S)
      BY ONLY FiniteSubsetsWellFounded 
    <3>2. ASSUME NEW c \in S
          PROVE  H(c) ~> (G \/ \E d \in SetLessThan(c, R, S) : H(d))
      BY <1>2, TLA
    <3> QED
      <4> HIDE DEF S, R, H, G
      <4>1. (\E c \in S : H(c)) ~> G
        BY ONLY <3>1, <3>2, LeadstoInduction, TLA 
      <4>2. \E c \in S : H(c)
        BY ONLY <1>1 DEF H, S, FiniteSubsets, Inv 
      <4>3. QED                                                      
        BY ONLY <4>1, <4>2, PTL DEF G, H (* ~> *) 
  <2>3. G => ~OX
    OBVIOUS
  <2>4. QED                                                             
     BY ONLY <2>1, <2>2, <2>3, PTL
              
<1>5. QED                                                                     
  BY ONLY <1>3, <1>4, PTL (* DEF ~> *)

=============================================================================
\* Modification History
\* Last modified Mon Mar 10 14:24:15 CET 2014 by doligez
\* Last modified Mon Mar 10 12:55:47 CET 2014 by doligez
\* Last modified Tue Dec 10 09:37:08 PST 2013 by lamport
\* Last modified Fri Dec 13 10:26:35 CET 2013 by merz
\* Last modified Tue Dec 10 16:18:41 CET 2013 by shaolin
\* Last modified Fri Dec 06 06:13:03 PST 2013 by lamport
\* Last modified Tue Oct 15 14:07:19 CEST 2013 by shaolin
\* Created Tue Jun 11 00:44:38 PDT 2013 by lamport
