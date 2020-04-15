-------------------------------- MODULE GFX_test ----------------------------
EXTENDS Integers, FiniteSets, TLAPS
  (*************************************************************************)
  (* Module Integers defines the standard operators on integers like + and *)
  (* the sets Int of integers and Nat of natural numbers.  (The TLAPS      *)
  (* prover has built-in knowledge of integers and does not use the        *)
  (* definitions in the module.) Module TLAPS asserts some theorems and    *)
  (* defines some "tactics" for use in proofs.                             *)
  (*************************************************************************)

CONSTANT Proc
ASSUME ProcFinite == IsFiniteSet(Proc)
  (*************************************************************************)
  (* We assume that Proc is a finite set, where the operator IsFiniteSet   *)
  (* is defined in the FiniteSets module.                                  *)
  (*************************************************************************)

NUnion(A) == UNION {A[i] : i \in Nat}
-----------------------------------------------------------------------------
(******
--algorithm GFX{
   variables A1 = [i \in Nat |-> {}], result = [i \in Proc |-> {}];
   process (Pr \in Proc) 
     variables known = {self}, notKnown = {} ;
     { a: known := known \cup NUnion(A1) ;
          notKnown := {i \in 0..(Cardinality(known)) : known # A1[i]} ;
          if (notKnown # {})
            { b: with (i \in notKnown) { A1[i] := known } ;
                 goto a
            }
          else {result[self] := known}
     }
}

*****)
\* BEGIN TRANSLATION
VARIABLES A1, result, pc, known, notKnown

vars == << A1, result, pc, known, notKnown >>

ProcSet == (Proc)

Init == (* Global variables *)
        /\ A1 = [i \in Nat |-> {}]
        /\ result = [i \in Proc |-> {}]
        (* Process Pr *)
        /\ known = [self \in Proc |-> {self}]
        /\ notKnown = [self \in Proc |-> {}]
        /\ pc = [self \in ProcSet |-> "a"]

a(self) == /\ pc[self] = "a"
           /\ known' = [known EXCEPT ![self] = known[self] \cup NUnion(A1)]
           /\ notKnown' = [notKnown EXCEPT ![self] = {i \in 0..(Cardinality(known'[self])) : known'[self] # A1[i]}]
           /\ IF notKnown'[self] # {}
                 THEN /\ pc' = [pc EXCEPT ![self] = "b"]
                      /\ UNCHANGED result
                 ELSE /\ result' = [result EXCEPT ![self] = known'[self]]
                      /\ pc' = [pc EXCEPT ![self] = "Done"]
           /\ A1' = A1

b(self) == /\ pc[self] = "b"
           /\ \E i \in notKnown[self]:
                A1' = [A1 EXCEPT ![i] = known[self]]
           /\ pc' = [pc EXCEPT ![self] = "a"]
           /\ UNCHANGED << result, known, notKnown >>

Pr(self) == a(self) \/ b(self)

Next == (\E self \in Proc: Pr(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION
------------------------------------------------------------------------------
snapshot == UNION {A1[i] : i \in Nat}
  (*************************************************************************)
  (* This definition was used in an earlier version of the algorithm, and  *)
  (* since the proof of this version was adapted from the proof of the     *)
  (* earlier one, references to it are still present in the proof.         *)
  (*************************************************************************)

(***************************************************************************)
(* The type-correctness invariant.                                         *)
(***************************************************************************)
TypeOK == /\ A1 \in [Nat -> SUBSET Proc]
          /\ result \in [Proc -> SUBSET Proc]
          /\ pc \in [Proc -> {"a", "b", "Done"}]
          /\ known \in [Proc -> SUBSET Proc]
          /\ notKnown \in [Proc -> SUBSET Nat]
          /\ \A p \in Proc : (pc[p] = "b") => (notKnown[p] # {})

Done(i) == result[i] # {}

(***************************************************************************)
(* The invariance of the following predicate captures the correctnes of    *)
(* the algorithm and is the key to proving that it the algorithm           *)
(* implements/refines its spec.                                            *)
(***************************************************************************)
GFXCorrect == \A i, j \in Proc :
                /\ Done(i) /\ Done(j)
                /\ Cardinality(result[i]) = Cardinality(result[j])
                => (result[i] = result[j])

------------------------------------------------------------------------------
(***************************************************************************)
(* We now define PA1 to be the set of all values that A1 could assume if   *)
(* some subset of processes that are ready to write wrote.                 *)
(***************************************************************************)
NotAProc == CHOOSE n : n \notin Proc
  (*************************************************************************)
  (* An arbitrary value that is not a process.                             *)
  (*************************************************************************)
  
ReadyToWrite(i, p) == /\ pc[p] = "b" 
                      /\ i \in notKnown[p]
  (*************************************************************************)
  (* True iff process p could write known[p] to A1[i] in its next step.    *)
  (*************************************************************************)
WriterAssignment == {f \in [Nat -> Proc \cup {NotAProc}] :
                        \A i \in Nat : 
                          (f[i] \in Proc) => /\ ReadyToWrite(i, f[i])
                                             /\ \A j \in Nat \ {i} :
                                                    f[j] # f[i] }
  (*************************************************************************)
  (* The set of functions f that assigns to each Nat i either a unique     *)
  (* process that is ready to write i, or NotAProc.                        *)
  (*************************************************************************)

PV(wa) == [i \in Nat |-> IF wa[i] = NotAProc THEN A1[i]  
                                             ELSE known[wa[i]] ]

PA1 == {PV(wa) : wa \in WriterAssignment}
------------------------------------------------------------------------------
(***************************************************************************)
(* We now complete the definition of the inductive invariant Inv.          *)
(*                                                                         *)
(* InvB is an uninteresting part of the invariant that asserts properties  *)
(* which are easily seen to be true by examining the code.                 *)
(***************************************************************************)
InvB == /\ \A i \in Nat : (A1[i] # {}) => (Cardinality(A1[i]) >= i)
        /\ \A p \in Proc :
             /\ (pc[p] = "b") => \A i \in notKnown[p] : i =< Cardinality(known[p])
             /\ p \in known[p] 
             /\ (result[p] # {}) <=> (pc[p] = "Done")
             /\ (result[p] # {}) => (result[p] = known[p])  

(***************************************************************************)
(* InvC is the interesting part of the inductive invariant that captures   *)
(* the essence of the algorithm.                                           *)
(***************************************************************************)
InvC == \A p \in Proc : 
           LET S == result[p]
               k == Cardinality(S) 
           IN  k > 0 => \A P \in PA1 : 
                           \/ Cardinality(UNION {P[i] : i \in Nat}) > k
                           \/ S \subseteq  UNION {P[i] : i \in Nat}

(***************************************************************************)
(* Inv is the complete inductive invariant.  Its invariance trivially      *)
(* implies the invariance of GFXCorrect.                                   *)
(***************************************************************************)
Inv == TypeOK /\ InvB /\ InvC /\ GFXCorrect
----------------------------------------------------------------------------
(***************************************************************************)
(* When we have a library of useful theorems about finite sets, we should  *)
(* be able to use it to prove the following simple results that are needed *)
(* for the proof.  Now, we just assume them.  The results are all obvious, *)
(* and they have been checked by TLC to make sure there are no silly       *)
(* errors in these TLA+ versions.                                          *)
(***************************************************************************)
THEOREM EmptySetCardinality == Cardinality({}) = 0
PROOF OMITTED

THEOREM PositiveCardinalityImpliesNonEmpty ==
  \A S : Cardinality(S) \in Nat /\ Cardinality(S) > 0 => S # {}
<1> SUFFICES ASSUME NEW S, Cardinality(S) \in Nat, Cardinality(S) > 0, S = {}
             PROVE  FALSE
  OBVIOUS
<1> QED
  BY EmptySetCardinality

THEOREM NonEmptySetCardinality == 
           \A S : IsFiniteSet(S) /\ S # {} => (Cardinality(S) > 0)
PROOF OMITTED

THEOREM SingletonCardinalty == \A x : Cardinality({x}) = 1
PROOF OMITTED

THEOREM SubsetFinite == 
            \A S : IsFiniteSet(S) => \A T \in SUBSET S : IsFiniteSet(T)
PROOF OMITTED
                                                                       
THEOREM CardType == \A S : IsFiniteSet(S) => Cardinality(S) \in Nat
PROOF OMITTED

THEOREM SubsetCardinality == 
           \A T : IsFiniteSet(T) => \A S \in SUBSET T :
                                       (S # T) => (Cardinality(S) < Cardinality(T))
PROOF OMITTED

THEOREM SubsetCardinality2 == 
           \A T : IsFiniteSet(T) => 
                    \A S \in SUBSET T :(Cardinality(S) =< Cardinality(T))
PROOF OMITTED

THEOREM IntervalFinite == \A i, j \in Int : IsFiniteSet(i..j)
PROOF OMITTED

THEOREM IntervalCardinality ==
  \A i,j \in Int : i <= j => Cardinality(i .. j) = j-i+1


THEOREM PigeonHolePrinciple ==
         \A S, T :
             /\ IsFiniteSet(S) /\ IsFiniteSet(T) 
             /\ Cardinality(T) < Cardinality(S)
             => \A f \in [S -> T] : 
                   \E x, y \in S : (x # y) /\ (f[x] = f[y])
PROOF OMITTED

(***************************************************************************)
(* The following is a simple corollary of Theorem PigeonHolePrinciple,     *)
(***************************************************************************)
COROLLARY InjectionCardinality ==
            \A S, T, f :
               /\ IsFiniteSet(S) /\ IsFiniteSet(T)
               /\ f \in [S -> T]
               /\ \A x, y \in S : x # y => f[x] # f[y]
               => Cardinality(S) =< Cardinality(T)
BY PigeonHolePrinciple, CardType, SMT
                  
(***************************************************************************)
(* The theorems above were checked for silly mistakes by having TLC check  *)
(* that with this definition, Test equals <<TRUE, ...  , TRUE>>.           *)
(***************************************************************************)
Test ==
<< 
   EmptySetCardinality, 
   \A S \in SUBSET (0..3) : NonEmptySetCardinality!(S),
   SingletonCardinalty!("abc"), 
   \A S \in SUBSET (0..3) : SubsetFinite!(S),
   \A S \in SUBSET (0..3) : CardType!(S),
   \A T \in SUBSET (0..3) : SubsetCardinality!(T),
   \A T \in SUBSET (0..3) : SubsetCardinality2!(T),
   \A i, j \in ((-4)..4) : IntervalFinite!(i, j),
   \A i, j \in ((-4)..4) : IntervalCardinality!(i, j),
   \A S, T \in SUBSET (0..3) : PigeonHolePrinciple!(S, T)
>>
------------------------------------------------------------------------------
LEMMA NotAProcProp == NotAProc \notin Proc
BY NoSetContainsEverything DEF NotAProc

USE DEF NUnion

(***************************************************************************)
(* The following theorem asserts the invariance of Inv.  This obviously    *)
(* implies the invariance of GFXCorrect.                                   *)
(***************************************************************************)
THEOREM Invariance == Spec => []Inv
<1>1. Init => Inv
  <2> USE DEF Init, Inv, TypeOK, ProcSet, ReadyToWrite, WriterAssignment, PV, PA1
  <2>1. Init => TypeOK
    BY SMT
  <2>2. Init => InvB
    <3>1. ASSUME Init 
          PROVE  InvB!1
      BY <3>1,  EmptySetCardinality, (* SingletonCardinalty,*) SMT DEF InvB
    <3>2. ASSUME Init 
          PROVE InvB!2
      <4>1. \A p \in Proc : Cardinality(known[p]) = 1
        BY <3>2, SingletonCardinalty  \* SMT fails on this
      <4>2. QED
        BY <3>2, <4>1, SMT DEF InvB
    <3>3. QED
      BY <3>1, <3>2 DEF InvB    
  <2>3. Init => InvC
    <3> SUFFICES ASSUME Init, NEW p \in Proc
                 PROVE  ~(Cardinality(result[p]) > 0)
      BY DEF InvC
    <3> QED
      BY EmptySetCardinality, SMT 
  <2>4. Init => GFXCorrect
    BY SMT DEF GFXCorrect 
  <2>5. QED
    BY <2>1, <2>2, <2>3, <2>4

<1>2. Inv /\ [Next]_vars => Inv'
  <2>1. Inv /\ UNCHANGED vars => Inv'
    <3> SUFFICES ASSUME Inv, vars' = vars
                 PROVE  Inv'
      OBVIOUS
    <3>1. TypeOK'
      BY SMT DEF Inv, TypeOK, ProcSet, ReadyToWrite, 
               WriterAssignment, PA1, PV, vars
    <3>2. InvB'
      BY SMT DEF Inv, TypeOK, InvB, PA1, PV, vars
    <3>3. InvC'
      <4> WriterAssignment' = WriterAssignment
        BY DEF WriterAssignment, ReadyToWrite, vars
      <4> QED
        BY DEF Inv, InvC, PA1, PV, vars \* SMT Failed
    <3>4. GFXCorrect'
      BY DEF Inv, GFXCorrect, Done, vars
    <3>5. QED
      BY <3>1, <3>2, <3>3, <3>4 DEF Inv
  <2>2. Inv /\ Next => Inv'
    <3> SUFFICES ASSUME Inv, Next
                 PROVE  Inv'
      OBVIOUS
    <3>1. IsFiniteSet(snapshot) /\ (snapshot \subseteq Proc)
      BY ONLY TypeOK, ProcFinite, SubsetFinite, SMT DEF Inv, TypeOK, snapshot 
    <3>2. \A p \in Proc : Cardinality(known[p]) \in Nat
      BY ProcFinite, SubsetFinite, CardType, SMT DEF Inv, TypeOK
    <3>3. TypeOK'
      <4> USE DEF Inv, TypeOK
      <4>1. ASSUME NEW p \in Proc, a(p)
            PROVE  TypeOK'
        <5>1. (A1 \in [Nat -> SUBSET Proc])'
          BY <4>1, <3>1, CardType, ProcFinite, SubsetFinite, Z3 DEF a
        <5>2. (result \in [Proc -> SUBSET Proc])'
          BY <4>1, known'[p] \in SUBSET Proc DEF a
        <5>3. (pc \in [Proc -> {"a", "b", "Done"}])'
          BY <4>1, <3>1, CardType, ProcFinite, SubsetFinite DEF a
        <5>4. (known \in [Proc -> SUBSET Proc])'
          BY <4>1, <3>1, CardType, ProcFinite, SubsetFinite, Z3 DEF a
        <5>5. (notKnown \in [Proc -> SUBSET Nat])'
          BY <4>1, <3>1, CardType, ProcFinite, SubsetFinite, Z3 DEF a
        <5>6. (\A p_1 \in Proc : (pc[p_1] = "b") => (notKnown[p_1] # {}))'
          BY <4>1, <3>1, CardType, ProcFinite, SubsetFinite DEF a
        <5>7. QED
          BY <5>1, <5>2, <5>3, <5>4, <5>5, <5>6 DEF TypeOK
      <4>2. ASSUME NEW p \in Proc, b(p)
            PROVE  TypeOK'
        BY <4>2, SMT DEF b
      <4>3 QED
        BY <2>1, <4>1, <4>2 DEF Next, Pr, ProcSet
    <3> USE DEF Inv, ProcSet \* , ReadyToWrite, PotentialValues, PA1
    <3>4. IsFiniteSet(snapshot') /\ (snapshot' \subseteq Proc)
      <4>1. snapshot' \subseteq Proc
        BY <3>3, ProcFinite, SubsetFinite, SMT DEF Inv, TypeOK, snapshot
      <4>2. IsFiniteSet(snapshot')
        BY <4>1, ProcFinite, SubsetFinite  DEF snapshot
      <4>3. QED
        BY <4>1, <4>2
    <3>5. \A p \in Proc : Cardinality(known'[p]) \in Nat
      BY <3>3, ProcFinite, SubsetFinite, CardType, SMT DEF Inv, TypeOK
    <3> DEFINE InvCI(q, P) == InvC!(q)!1!2!(P)
               Snapshot(P) == UNION {P[i] : i \in Nat}
    (***********************************************************************)
    (* The following step is used only in the proof of InvC' for a b(p)    *)
    (* action in the proof of <3>8.  It could probably also be used to     *)
    (* simplify the proof of one or more cases in the proof of InvC' for   *)
    (* an a(p) action.                                                     *)
    (***********************************************************************)
    <3>6. ASSUME NEW p \in Proc, NEW q \in Proc \ {p},
                 Cardinality(result'[q]) > 0,
                 \A qq \in Proc \ {p} : /\ known'[qq]  = known[qq]
                                        /\ notKnown'[qq]    = notKnown[qq]
                                        /\ pc'[qq]     = pc[qq]
                                        /\ result'[qq] = result[qq],
                 pc'[p] # "b",
                 NEW P \in PA1
          PROVE  InvCI(q, P)' 
      <4> DEFINE S == result[q]
                 k == Cardinality(result[q]) 
      <4>1. /\  IsFiniteSet(S')
            /\  k' \in Nat
        BY <3>3, ProcFinite, SubsetFinite, CardType, SMT DEF TypeOK               
      <4>2. S = S' /\ k = k' 
        BY <3>6, SMT DEF TypeOK
      <4>3. \A i \in Nat : ~ReadyToWrite(i, p)'
        BY <3>6 DEF ReadyToWrite
      <4>4. \A i \in Nat : {r \in Proc : ReadyToWrite(i, r)'} \subseteq 
                             {r \in Proc : ReadyToWrite(i, r)}
        BY <3>6, <4>3, SMT DEF ReadyToWrite, TypeOK
      <4>5. result[q] = result'[q]
        BY <3>6 DEF TypeOK
      <4>6. InvCI(q, P)
        BY <3>6 DEF InvC
      <4>7. CASE S \subseteq Snapshot(P)
        BY <4>7, <4>2, <4>1, <4>4, <4>3, <3>6, SMT DEF TypeOK
      <4>8. CASE Cardinality( UNION {P[i] : i \in Nat} ) > Cardinality(S)
        BY <4>2, <4>8
      <4>9. QED
        BY <4>6, <4>7, <4>8
    <3>7. ASSUME NEW p \in Proc, a(p)
          PROVE  Inv'
      <4> USE DEF Inv
      <4>1. InvB'
        <5>1. (\A i \in Nat : (A1[i] # {}) => (Cardinality(A1[i]) >= i))'
          BY <3>1, <3>2, <3>5, <3>7, Z3 DEF a, TypeOK, InvB
        <5>2. (\A p_1 \in Proc :
                 /\ (pc[p_1] = "b") => \A i \in notKnown[p_1] : i =< Cardinality(known[p_1])
                 /\ p_1 \in known[p_1]
                 /\ (result[p_1] # {}) <=> (pc[p_1] = "Done")
                 /\ (result[p_1] # {}) => (result[p_1] = known[p_1]))'
          <6> SUFFICES ASSUME NEW p_1 \in Proc
                       PROVE  (/\ (pc[p_1] = "b") => \A i \in notKnown[p_1] : i =< Cardinality(known[p_1])
                               /\ p_1 \in known[p_1]
                               /\ (result[p_1] # {}) <=> (pc[p_1] = "Done")
                               /\ (result[p_1] # {}) => (result[p_1] = known[p_1]))'
            OBVIOUS
          <6>1. ((pc[p_1] = "b") => \A i \in notKnown[p_1] : i =< Cardinality(known[p_1]))'
            <7> CASE p_1 = p
              BY <3>1, <3>2, <3>5, <3>7 DEF a, TypeOK, InvB
            <7> CASE p_1 # p
              BY <3>1, <3>2, <3>5, <3>7 DEF a, TypeOK, InvB
            <7> QED OBVIOUS
          <6>2. (p_1 \in known[p_1])'
            BY <3>1, <3>2, <3>5, <3>7, Z3 DEF a, TypeOK, InvB
          <6>3. ((result[p_1] # {}) <=> (pc[p_1] = "Done"))'
            <7> CASE p_1 = p
              BY <3>1, <3>2, <3>5, <3>7 DEF a, TypeOK, InvB
            <7> CASE p_1 # p
              BY <3>1, <3>2, <3>5, <3>7, pc'[p_1] = pc[p_1], result'[p_1] = result[p_1] DEF a, TypeOK, InvB
            <7> QED OBVIOUS
          <6>4. ((result[p_1] # {}) => (result[p_1] = known[p_1]))'
            BY <3>1, <3>2, <3>5, <3>7 DEF a, TypeOK, InvB
          <6>5. QED
            BY <6>1, <6>2, <6>3, <6>4
        <5>3. QED
          BY <5>1, <5>2 DEF InvB
      <4>2. InvC'
        <5> SUFFICES ASSUME NEW q \in Proc, Cardinality(result'[q]) > 0,
                            NEW P \in PA1'
                     PROVE  InvCI(q, P)'
            (***************************************************************)
            (* The goal is the body of the \A p \in Proc : quantifier with *)
            (* q substituted for p.                                        *)
            (***************************************************************)
          BY DEF InvC
        <5> (pc[p] = "a") /\ (A1' = A1)
          BY <3>7 DEF a
        <5> DEFINE S == result[q]
                   k == Cardinality(result[q])
                   InvA1q(Q) == \/ S \subseteq Snapshot(P)
                                \/ Cardinality( UNION {Q[i] : i \in Nat} ) > Cardinality(S)
        <5>1. /\  IsFiniteSet(S')
              /\  k' \in Nat
          BY <3>3(*TypeOK'*), ProcFinite, SubsetFinite, CardType, SMT DEF TypeOK   
        <5>2. \A r \in Proc :
                /\ IsFiniteSet(result[r])
                /\ IsFiniteSet(result'[r])
                /\ IsFiniteSet(known[r])
                /\ IsFiniteSet(known'[r])
                /\ Cardinality(result[r]) \in Nat
                /\ Cardinality(result'[r]) \in Nat
                /\ Cardinality(known[r]) \in Nat
                /\ Cardinality(known'[r]) \in Nat
          BY  <3>3(*TypeOK'*), ProcFinite, SubsetFinite, CardType, SMT DEF TypeOK     
        <5>3. CASE /\ known' = [known EXCEPT ![p] 
                                 = known[p] \cup UNION {A1[i] : i \in Nat}]
                   /\ notKnown' = 
                        [notKnown EXCEPT ![p] = 
                            {i \in 0..(Cardinality(known'[p])) : 
                                    known'[p] # A1[i]}]
                   /\ notKnown'[p] # {}
                   /\ pc' = [pc EXCEPT ![p] = "b"]
                   /\ UNCHANGED result
          <6>1. ASSUME NEW Q \in PA1
                PROVE  /\ IsFiniteSet(Snapshot(Q))
                       /\ Cardinality(Snapshot(Q)) \in Nat
            <7> PICK wa \in WriterAssignment : Q = PV(wa)
              BY DEF PA1
            <7>1. \A i \in Nat : wa[i] # NotAProc => wa[i] \in Proc
               BY DEF WriterAssignment
            <7>2. \A i \in Nat : PV(wa)[i] \in SUBSET Proc
              BY <7>1, <3>3(*TypeOK'*), SMT DEF PV, TypeOK
            <7>3. UNION {Q[j] : j \in Nat} \subseteq Proc
              BY <7>2, SMT 
            <7>4. IsFiniteSet(UNION {Q[j] : j \in Nat})
              BY <7>3, ProcFinite, SubsetFinite  \* SMT failed on this.
            <7>5. QED
              BY <7>4, CardType(*, SMT*)  \** sm: SMT fails here 
          <6>2. A1 \in PA1
            <7> DEFINE wa == [i \in Nat |-> NotAProc]
            <7>1. wa \in WriterAssignment
                BY SMT, NotAProcProp DEF WriterAssignment
            <7>2. PV(wa) = A1
              BY DEF TypeOK, PV
            <7>3. QED
             BY  <7>1, <7>2 DEF PA1
          <6>3. /\ p # q
                /\ S = S'
            <7>1. result'[q] # {}
              BY (k' > 0), <5>1, PositiveCardinalityImpliesNonEmpty
            <7>2. result'[p] = {}
              BY  <5>3, (* <8>1,*) <4>1(*InvB'*), SMT DEF TypeOK, InvB  \* sm: triviality check doesn't get InvB'
            <7>3. QED
              BY <7>1, <7>2, <5>3, SMT DEF TypeOK             
          <6>4. /\ IsFiniteSet(UNION {P[i] : i \in Nat})
                /\ Cardinality(UNION {P[i] : i \in Nat}) \in Nat
            <7> PICK wa \in WriterAssignment' : P = PV(wa)'
              BY DEF PA1
            <7>1. \A i \in Nat : wa[i] # NotAProc => wa[i] \in Proc
               BY DEF WriterAssignment
            <7>2. \A i \in Nat : PV(wa)'[i] \in SUBSET Proc
              BY <7>1, <3>3(*TypeOK'*), SMT DEF PV, TypeOK
            <7>3. UNION {P[j] : j \in Nat} \subseteq Proc
              BY <7>2, SMT 
            <7>4. IsFiniteSet(UNION {P[j] : j \in Nat})
              BY <7>3, ProcFinite, SubsetFinite  \* SMT failed on this.
            <7>5. QED
              BY <7>4, CardType \* SMT fails here
          <6>5. CASE P \in PA1
            <7> InvCI(q, P)
              BY <6>3, <6>5, <5>3, SMT DEF InvC
            <7> QED
              BY <5>3, <6>3
          <6>6. CASE P \notin PA1
            <7>1. PICK j \in Nat : P[j] = known'[p]
              <8> SUFFICES ASSUME \A i \in Nat : P[i] # known'[p]
                           PROVE  P \in PA1
                BY <6>6
              <8> PICK wa \in WriterAssignment' : P = PV(wa)'
                BY DEF PA1
              <8>1. \A i \in Nat : wa[i] # p
                BY NotAProcProp, SMT DEF PV
              <8>2. \A i \in Nat : PV(wa)' = PV(wa)
                BY <8>1, <5>3, SMT DEF TypeOK, PV, WriterAssignment  
                \* DEF PV added 31 May 2013
                \** DEF WriterAssignment added 2013-06-25
              <8>3. wa \in WriterAssignment
                <9>1. ASSUME NEW i \in Nat, wa[i] \in Proc 
                      PROVE  ReadyToWrite(i, wa[i])
                  <10>1. ReadyToWrite(i, wa[i])' => ReadyToWrite(i, wa[i])
                    BY <8>1, <5>3, wa[i] \in Proc, Z3 DEF TypeOK, ReadyToWrite
                    \** wa[i] \in Proc added 2013-06-25
                  <10>2. QED
                    BY <9>1, <10>1, SMT DEF WriterAssignment
                <9>2. QED
                  BY <9>1, SMT DEF WriterAssignment
              <8>4. QED
                BY <8>2, <8>3, SMT DEF PA1
            <7>2. Snapshot(A1) \subseteq known'[p]
              BY <5>3, SMT DEF snapshot, TypeOK
            <7>3. \/ Cardinality(Snapshot(A1)) > k
                  \/ S \subseteq Snapshot(A1)
              BY <6>2, <6>3 DEF InvC, TypeOK    \* SMT fails here
            <7>4. \/ Cardinality(P[j]) > k
                  \/ S \subseteq P[j]
              <8>1. CASE Cardinality(Snapshot(A1)) > k
                <9>1. IsFiniteSet(known[p])
                  BY ProcFinite, SubsetFinite, SMT DEF TypeOK
                <9>2. Cardinality(Snapshot(A1)) =< Cardinality(known'[p])
                  BY <9>1, <7>2, <5>2, SubsetCardinality2
                <9> Cardinality(known[p]) \in Nat
                  BY <9>1, CardType
                <9> Cardinality(Snapshot(A1)) \in Nat
                  BY <6>1, <6>2, CardType
                <9> k \in Nat
                  BY <6>3, <5>1
                <9>3. QED
                BY <5>2, <7>1, <9>2, <8>1, SMT 
              <8>2. CASE S \subseteq Snapshot(A1)
                BY <8>2, <6>1, <6>2, <7>1, <7>2, <7>3, CardType, 
                 ProcFinite, SubsetFinite, SubsetCardinality2, SMT DEF TypeOK
              <8>3. QED
                 BY <8>1, <8>2, <7>3              
            <7>5. P[j] \subseteq Snapshot(P)
              BY <5>1, <6>3 DEF TypeOK
            <7>6. QED
              <8>1. CASE Cardinality(P[j]) > k
                <9> /\ IsFiniteSet(Snapshot(P))
                    /\ Cardinality(Snapshot(P)) \in Nat
                    BY <6>4
                <9> /\ Cardinality(P[j]) \in Nat
                  BY <7>1, <3>3(*TypeOK'*), ProcFinite, SubsetFinite, CardType DEF TypeOK
                <9> /\ k \in Nat
                  BY ProcFinite, SubsetFinite, CardType DEF TypeOK
                <9> Cardinality(P[j]) =< Cardinality(Snapshot(P))
                  BY <7>5, <6>1, SubsetCardinality2, SMT
                <9> QED
                  BY <8>1, <7>1, <5>3, SMT DEF TypeOK
              <8>2. CASE S \subseteq P[j]
                BY <8>2, <7>5, <5>3, SMT DEF TypeOK
              <8>3. QED
                BY <8>1, <8>2, <7>4 
          <6>7. QED
            BY <6>5, <6>6
        <5>4. CASE /\ known' = [known EXCEPT ![p] 
                                 = known[p] \cup UNION {A1[i] : i \in Nat}]
                   /\ notKnown' = 
                        [notKnown EXCEPT ![p] = 
                            {i \in 0..(Cardinality(known'[p])) : 
                                 known'[p] # A1[i]}]
                   /\ notKnown'[p] = {}
                   /\ result' = [result EXCEPT ![p] = known'[p]]
                   /\ pc' = [pc EXCEPT ![p] = "Done"]
          <6>2. PA1' = PA1
            <7>1. ASSUME NEW i \in Nat, NEW r \in Proc
                  PROVE  ReadyToWrite(i, r)' = ReadyToWrite(i, r)
              BY <5>4, SMT DEF ReadyToWrite, TypeOK
            <7>2. WriterAssignment' = WriterAssignment
              BY <7>1, SMT DEF WriterAssignment
            <7>3. ASSUME NEW wa \in WriterAssignment, NEW i \in Nat,
                         wa[i] # NotAProc
                  PROVE  known'[wa[i]] = known[wa[i]]
              <8> USE <7>3
              <8>1. ReadyToWrite(i, wa[i])
                BY NotAProcProp, SMT DEF WriterAssignment
              <8>2. wa[i] # p
                BY <5>4, <8>1, SMT DEF ReadyToWrite
              <8>3. wa[i] \in Proc
                BY SMT DEF WriterAssignment 
              <8>4. QED
                BY <8>2, <8>3, <5>4, SMT DEF TypeOK
            <7>4. A1' = A1
              BY <5>4
            <7>5. QED
              <8> SUFFICES ASSUME NEW wa \in WriterAssignment,
                                  NEW i \in Nat
                           PROVE  PV(wa)[i] = PV(wa)[i]'
                <9> ASSUME NEW wa \in WriterAssignment
                    PROVE  /\ PV(wa) =  [i \in Nat |-> PV(wa)[i]]
                           /\ PV(wa)' = [i \in Nat |-> PV(wa)[i]]
                  BY DEF PV
                <9> QED
                  BY <7>2 DEF PA1
              <8>1. CASE wa[i] = NotAProc
                BY <8>1, <7>4 DEF PA1, PV
              <8>2. CASE wa[i] # NotAProc
                BY <8>2, <7>3 DEF PA1, PV
              <8>3. QED
                BY <8>1, <8>2
          <6>3. SUFFICES ASSUME p = q
                         PROVE  InvCI(q, P)'
            <7> SUFFICES ASSUME p # q
                         PROVE  InvCI(q, P)'
                OBVIOUS
            <7> SUFFICES ASSUME result'[q] # {}
                         PROVE  InvCI(q, P)'
              OBVIOUS
            <7> Cardinality(result'[q]) > 0
              BY <5>2, NonEmptySetCardinality, SMT
            <7> result'[q] = result[q]
              BY <5>4, SMT DEF TypeOK
            <7> InvCI(q, P)
              BY <6>2, SMT DEF InvC
            <7> QED
              BY <6>2, SMT 
          <6>4. /\ \A i \in 0..Cardinality(known'[p]) : known'[p] = A1[i]
                /\ known'[p] = NUnion(A1)
                /\ Cardinality(known'[p]) >= 0
            <7>1. \A i \in 0..Cardinality(known'[p]) : known'[p] = A1[i]
               <8> /\ notKnown'[p] = {i \in 0..Cardinality(known'[p]) : 
                                          known'[p] # A1[i]}
                   /\ notKnown'[p] = {}
                 BY <5>4, SMT DEF TypeOK
               <8> QED
                 OBVIOUS
            <7>2. Cardinality(known'[p]) >= 0
              BY <5>2, <4>1(*InvB'*), NonEmptySetCardinality, SMT DEF InvB   \** sm: triviality check 
            <7>3. known'[p] = A1[0]
              BY <5>2, <7>1, <7>2, SMT DEF TypeOK
            <7>4. NUnion(A1) \subseteq known'[p]
              BY <5>4 DEF NUnion, TypeOK
            <7>5. NUnion(A1) = known'[p]
              BY <7>3, <7>4 DEF NUnion
            <7>6. QED
              BY <7>1, <7>2, <7>5
          <6>5. CASE \E i \in 0..Cardinality(known'[p]) : P[i] = A1[i]
            <7>1. PICK i \in 0..Cardinality(known'[p]) : P[i] = A1[i]
              BY <6>5    \* sm: original proof, certainly a typo -- BY <6>4
            <7>2. A1[i] \subseteq NUnion(P)
              BY <7>1, SMT DEF NUnion, TypeOK
            <7>3. known'[p] \subseteq NUnion(P)
              BY <7>2, <6>4
            <7>4. result'[p] = known'[p]
              BY <5>4, SMT DEF TypeOK
            <7>5. QED
              BY <7>3, <7>4, <6>3
          <6>6. CASE \A i \in 0..Cardinality(known'[p]) : P[i] # A1[i]
            <7> PICK wa \in WriterAssignment : P = PV(wa)
              BY <6>2 DEF PA1
            <7>1. \A i \in 0..Cardinality(known'[p]) : /\ wa[i] # NotAProc
                                                       /\ P[i] = known[wa[i]]
              BY <6>6, SMT DEF PV
            <7>2. \A i \in 0..Cardinality(known'[p]) : /\ wa[i] \in Proc
                                                       /\ ReadyToWrite(i, wa[i])
              BY <7>1, NotAProcProp, SMT DEF WriterAssignment           
            <7>3. \A i, j \in 0..Cardinality(known'[p]) : i # j => wa[i] # wa[j]
              BY <5>2, <7>2, SMT DEF WriterAssignment
            <7>4. \A i \in 0..Cardinality(known'[p]) : wa[i] \in P[i]
              BY <7>1, <7>2, Z3 DEF InvB
            <7>6. /\ IsFiniteSet( UNION {P[i] : i \in Nat} )
                  /\ Cardinality( UNION {P[i] : i \in Nat} ) \in Nat
              <8>1. \A i \in Nat : wa[i] # NotAProc => wa[i] \in Proc
                 BY DEF WriterAssignment
              <8>2. \A i \in Nat : PV(wa)'[i] \in SUBSET Proc
                BY <8>1, <3>3(*TypeOK'*), SMT DEF PV, TypeOK
              <8>3. UNION {P[j] : j \in Nat} \subseteq Proc
                <9> SUFFICES ASSUME NEW j \in Nat PROVE P[j] \subseteq Proc
                  OBVIOUS
                <9>1. wa[j] = NotAProc \/ wa[j] \in Proc
                  BY SMT DEF WriterAssignment
                <9>2. QED
                BY <9>1, SMT DEF TypeOK, PV
              <8>4. IsFiniteSet(UNION {P[j] : j \in Nat})
                BY <8>3, ProcFinite, SubsetFinite  \* SMT failed on this.
              <8>5. QED
                BY <8>4, CardType   \*  SMT fails here
            <7>5. Cardinality( UNION {P[i] : i \in Nat} ) >= Cardinality(known'[p]) + 1
              <8> DEFINE C == Cardinality(known'[p])
                         SS == 0..C
                         TT == UNION {P[i] : i \in SS}
                         UU == UNION {P[i] : i \in Nat}
                         f == [i \in 0..C |-> wa[i]]
              <8> SUFFICES Cardinality(UU) >= C+1
                OBVIOUS
              <8>1. /\ C \in Nat
                    /\ SS \subseteq Nat
                    /\ IsFiniteSet(SS)
                    /\ Cardinality(SS) = C+1
                BY <5>2, IntervalCardinality, IntervalFinite, SMT   
              <8>2. /\ TT \subseteq  UU
                    /\ IsFiniteSet(UU)
                    /\ IsFiniteSet(TT)
                BY <7>6, <8>1, SubsetFinite, Z3 \* SMT used to work but now fails
              <8>3. f \in [SS -> TT]
                BY <7>4, SMT
              <8>4. \A x, y \in SS : (x # y) => (f[x] # f[y])
                BY <7>3, SMT
              <8> HIDE DEF SS, TT, UU, C, f
              <8>5. Cardinality(SS) =< Cardinality(TT)
                BY <8>1, <8>2, <8>3, <8>4, InjectionCardinality  \* SMT fails here
              <8>6. /\ Cardinality(TT) =< Cardinality(UU)
                    /\ Cardinality(UU) \in Nat
                    /\ Cardinality(TT) \in Nat
                BY <8>2, CardType, SubsetCardinality2, SMT
              <8>7. QED
                BY <8>1, <8>5, <8>6, SMT
            <7>7. QED
              <8> result'[p] = known'[p]
                BY <5>4, SMT DEF TypeOK
              <8> QED
                BY <5>2, <6>3, <7>5, <7>6, SMT 
          <6>7. QED
            BY <6>5, <6>6
        <5>5. QED
          BY <3>7, <5>3, <5>4 DEF a
      <4>3. GFXCorrect'
        <5>1. CASE UNCHANGED result
             (**************************************************************)
             (* This handles the IF/THEN case.                             *)
             (**************************************************************)
          BY <5>1, SMT DEF TypeOK, GFXCorrect, Done
        <5>2. CASE /\ known' = [known EXCEPT ![p] 
                                 = known[p] \cup UNION {A1[i] : i \in Nat}]
                   /\ notKnown' = 
                        [notKnown EXCEPT ![p] = 
                            {i \in 0..(Cardinality(known'[p])) : 
                                 known'[p] # A1[i]}]
                   /\ notKnown'[p] = {}
                   /\ result' = [result EXCEPT ![p] = known'[p]]
                   /\ pc' = [pc EXCEPT ![p] = "Done"]
                   /\ A1' = A1
              (*************************************************************)
              (* This is the IF/ELSE case (simplified).                    *)
              (*************************************************************)
          <6> SUFFICES ASSUME NEW q \in Proc, NEW r \in Proc,
                              q # r,
                              Done(q)' /\ Done(r)',
                              Cardinality(result'[q]) = Cardinality(result'[r])
                       PROVE  result'[q] = result'[r]
            BY DEF GFXCorrect
          <6>1. CASE p \notin {q, r} 
            <7>1. /\ result'[q] = result[q]
                  /\ result'[r] = result[r]
                  /\ Done(q)' = Done(q)
                  /\ Done(r)' = Done(r)
              BY <5>2, <6>1  DEF TypeOK, Done
            <7>2. QED
              BY <7>1, SMT DEF GFXCorrect, TypeOK
          <6>2. CASE p \in {q, r}
            <7> SUFFICES ASSUME NEW s \in Proc,
                                p # s,
                                Done(p)' /\ Done(s)',
                                Cardinality(result'[p]) = Cardinality(result'[s])
                         PROVE  result'[p] = result'[s]
               \* Zenon or Isabelle used to prove this in one step, but on
               \* 31 May 2013 it no longer did and the proof had to be decomposed.
               <8>1. CASE p = q
                  BY <8>1
               <8>2. CASE p = q
                  BY <8>2
               <8>3. QED
                 BY <8>1, <8>2, <6>2
                  
            <7>1. /\ result'[s] = result[s]
                  /\ Done(s)
              BY <5>2 DEF TypeOK, Done
            <7> DEFINE S == result[s]
                       k == Cardinality(result[s])
            <7>2. /\ k \in Nat 
                  /\ k > 0
              BY <7>1, ProcFinite, SubsetFinite, CardType, NonEmptySetCardinality, SMT DEF TypeOK, Done
            <7>3. \/ S \subseteq Snapshot(A1)
                  \/ Cardinality( UNION {A1[i] : i \in Nat} ) > Cardinality(S)
              <8>1. InvC!(s)!1!2
                BY <7>2, InvC DEF InvC
              <8>2. A1 \in PA1
                <9> DEFINE wa == [i \in Nat |-> NotAProc]
                <9>1. wa \in WriterAssignment
                    BY SMT, NotAProcProp DEF WriterAssignment
                <9>2. PV(wa) = A1
                  BY DEF TypeOK, PV
                <9>3. QED
                 BY  <9>1, <9>2 DEF PA1
              <8>3. QED
                BY <8>1, <8>2
            <7>4. result'[p] = A1[k]
              <8>1. result'[p] = known'[p]
                BY <5>2, SMT DEF TypeOK
              <8>2. k \in 0..Cardinality(known'[p])
                BY <8>1, <7>1, <7>2, SMT
              <8>3. \A i \in 0..Cardinality(known'[p]) : known'[p] = A1[i]
                BY <5>2, SMT DEF TypeOK
              <8>4. known'[p] = A1[k]
                BY <8>2, <8>3, SMT DEF TypeOK
              <8>5. QED
                BY <8>1, <8>4
            <7>5. result'[p] = UNION {A1[i] : i \in Nat}
              <8>1. UNION {A1[i] : i \in Nat} \subseteq result'[p]
                BY <5>2, <7>2 , SMT DEF TypeOK
              <8>2. result'[p] \subseteq UNION {A1[i] : i \in Nat} 
                BY <7>2, <7>4, SMT
              <8>3. QED
                BY <8>1, <8>2
            <7>6. Cardinality( UNION {A1[i] : i \in Nat} ) = k
              BY <7>1, <7>5
            <7>7. S \subseteq result'[p]
              BY <7>2, <7>3, <7>5, <7>6, SMT
            <7>8. IsFiniteSet(result'[p])
              BY <3>3(*TypeOK'*), ProcFinite, SubsetFinite, SMT DEF TypeOK 
            <7>9. S = result'[p]
              <8> (Cardinality(S) = k) /\ (Cardinality(result'[p]) = k)
                BY  <7>5, <7>6  \* SMT fails here
              <8> ~ (Cardinality(S) < Cardinality(result'[p]))
                 BY  <7>2, <7>5, <7>6, <7>7, <7>8, SubsetCardinality, SMT
              <8> QED
                BY  <7>2, <7>5, <7>6, <7>7, <7>8, SubsetCardinality, SMT
            <7>10. QED
              BY <7>1, <7>9               
          <6>3. QED
            BY <6>1, <6>2
       <5>3. QED
        BY <5>1, <5>2, <3>7 DEF a
      <4>4. QED
        BY <3>3, <4>1, <4>2, <4>3 DEF Inv
    <3>8. ASSUME NEW p \in Proc, b(p)
          PROVE  Inv'
      <4> USE b(p) DEF Inv
      <4>1. InvB'
        <5>1. InvB!1'
          BY DEF TypeOK, InvB, b
        <5>2. InvB!2'
          BY (*<3>1, <3>2, <3>5, <3>8,*) SMT DEF b, TypeOK, InvB   \* sm: SMT fails here when given unnecessary facts
        <5>3. QED
          BY <5>1, <5>2 DEF InvB
      <4>2. InvC'
        (*******************************************************************)
        (* Since b(p) just removes p from ReadyToWrite(nextwr[p]) and sets *)
        (* A1[i] to known[p], PA1' is a subset of PA1.  Since no other     *)
        (* relevant variables are changed, InvC!(q)!1!2(P) is left         *)
        (* unchanged for any P in PA1.                                     *)
        (*******************************************************************)
        <5> SUFFICES ASSUME NEW q \in Proc, Cardinality(result'[q]) > 0,
                            NEW P \in PA1'
                     PROVE  InvCI(q, P)'
            (***************************************************************)
            (* The goal is the body of the \A p \in Proc : quantifier with *)
            (* q substituted for p.                                        *)
            (***************************************************************)
          BY DEF InvC
        <5>1. P \in PA1
          (*****************************************************************)
          (* The following proof was copied with slight modification from  *)
          (* the proof for action d in RV3.                                *)
          (*****************************************************************)
          <6> PICK wa \in WriterAssignment' : P = PV(wa)'
            BY DEF PA1
          <6>1. ASSUME NEW  i \in Nat, NEW qa \in Proc,
                       ReadyToWrite(i, qa)'
                PROVE  ReadyToWrite(i, qa)
            <7> /\ pc'[qa] = "b" => pc[qa] = "b"
                /\ notKnown' = notKnown
              BY SMT DEF b, TypeOK
            <7> QED
              BY <6>1, SMT DEF ReadyToWrite
          <6>2. wa \in WriterAssignment
            BY <6>1, SMT DEF WriterAssignment
          <6>3. PICK j \in notKnown[p] : A1' = [A1 EXCEPT ![j] = known[p]]
            BY DEF b
          <6> j \in Nat
            BY DEF TypeOK 
          <6>4. CASE wa[j] # NotAProc
            <7>1. PV(wa)' = PV(wa)
              <8>1. SUFFICES ASSUME NEW i \in Nat
                             PROVE  PV(wa)'[i] = PV(wa)[i]
                BY DEF PV
              <8>2. CASE wa[i] # NotAProc 
                <9> known'[wa[i]] = known[wa[i]]
                  BY DEF b
                <9> QED
                  BY <8>2 DEF PV
              <8>3. CASE wa[i] = NotAProc
                 <9> i # j
                   BY <6>4, <8>3
                 <9> A1'[i] = A1[i]
                   BY <6>3, SMT DEF TypeOK
                 <9> QED
                   BY <8>3 DEF PV
              <8>4. QED
                BY <8>2, <8>3
            <7>2. QED
              BY <6>2, <7>1 DEF PA1
          <6>5. CASE wa[j] = NotAProc
            <7> DEFINE za == [wa EXCEPT ![j] = p]
            <7>1. za \in WriterAssignment
              <8>1. \A i \in Nat : wa[i] # p
                <9> \A i \in Nat : ~ReadyToWrite(i, p)'
                  BY SMT DEF b, TypeOK, ReadyToWrite
                <9> QED
                  BY SMT DEF WriterAssignment
              <8>2. ReadyToWrite(j, p)
                BY DEF b, ReadyToWrite
              <8>3. ASSUME NEW i \in Nat, NEW  k \in Nat \ {i}, wa[i] \in Proc 
                    PROVE  za[i] # za[k]
                <9> wa \in [Nat -> Proc \union {NotAProc}]
                  BY DEF WriterAssignment
                <9> CASE j \notin {i, k}
                  <10> wa[i] # wa[k]
                    BY <8>3, SMT DEF WriterAssignment
                  <10> za[i] = wa[i] /\ za[k] = wa[k]
                    OBVIOUS
                  <10> QED
                    BY <8>1, SMT 
                <9> CASE j \in {i, k}
                  BY <8>1, SMT
                <9> QED
                  OBVIOUS
              <8>4. QED
                BY <6>2, <8>2, <8>3, SMT DEF WriterAssignment
            <7>2. PV(wa)' = PV(za)
              <8>1. wa = [k \in Nat |-> wa[k]]
                  BY DEF WriterAssignment
              <8>2. SUFFICES ASSUME NEW i \in Nat
                             PROVE  PV(wa)'[i] = PV(za)[i]
                BY DEF PV
              <8>3. CASE wa[i] # NotAProc 
                <9>1. i # j
                  BY <6>5, <8>3
                <9>2. known'[wa[i]] = known[wa[i]]
                  BY <9>1 DEF b
                <9>3. PV(wa)'[i] = known'[wa[i]]
                  BY <8>3, SMT DEF PV
                <9>4. za[i] = wa[i]
                   BY <8>1, <9>1
                <9>5. PV(za)[i] = known[wa[i]]
                  BY <9>4, <8>3 DEF PV  
                <9>6. QED
                  BY <9>2, <9>3, <9>5
              <8>4. CASE wa[i] = NotAProc
                <9>1. CASE i # j
                  <10> A1'[i] = A1[i]
                    BY <9>1, <6>3, SMT DEF TypeOK
                  <10> wa[i] = za[i]
                    BY <8>1, <9>1 
                  <10> QED
                    BY <8>4, <9>1, <6>1, SMT DEF PV, WriterAssignment
                    \** 2013-06-25 DEF WriterAssignment missing
                <9>2. CASE i = j
                  <10>1. PV(wa)'[j] = A1[j]'
                    BY <9>2, <8>4 DEF PV
                  <10>2. za[j] = p
                    BY <8>1, <9>2
                  <10>3. PV(za)[j] = known[p]
                     BY <10>2, NotAProcProp, SMT DEF PV, WriterAssignment
                    \** 2013-06-25 DEF WriterAssignment missing
                  <10>4. A1'[j] = known[p]
                    BY <6>3, SMT DEF TypeOK
                  <10> HIDE DEF za
                  <10>5. QED
                    BY  <9>2, <10>1, <10>3, <10>4
                <9>3. QED
                  BY <9>1, <9>2
              <8>5. QED
                BY <8>3, <8>4
            <7>3. QED
              BY <7>1, <7>2 DEF PA1
          <6>6. QED
            BY <6>4, <6>5
        <5>2.    \A qq \in Proc \ {p} : /\ known'[qq]  = known[qq]
                                        /\ notKnown'[qq] = notKnown[qq]
                                        /\ pc'[qq]     = pc[qq]
                                        /\ result'[qq] = result[qq]
          BY <3>8, SMT DEF b, TypeOK
        <5>3. pc'[p] = "a"
          BY <3>8, SMT DEF TypeOK, b
        <5>4. q # p 
          <6>1. Cardinality(result'[q]) \in Nat
            BY <3>3(*TypeOK'*), ProcFinite, SubsetFinite, CardType, SMT DEF TypeOK  \* sm: failure of triviality check
          <6>2. result'[q] # {}
            BY <6>1, PositiveCardinalityImpliesNonEmpty
          <6>3. pc'[q] = "Done"
            BY  <6>2, <4>1(*InvB'*), SMT DEF TypeOK, InvB   \* sm: failure of triviality check
          <6>4. QED
            BY <6>3, <5>3
        <5> HIDE DEF PA1, InvCI
        <5>5. InvCI(q, P)'
          BY <5>1, <5>2, <5>3, <5>4, <3>6, SMT DEF TypeOK 
        <5>6. QED
          BY <5>5 DEF InvCI
      <4>3. GFXCorrect'
        BY <3>8 DEF b, TypeOK, GFXCorrect, Done
      <4>4. QED
        BY <3>3, <4>1, <4>2, <4>3
    <3> HIDE DEF Inv
    <3>9. QED
      BY <2>1, <3>7, <3>8 DEF Next, Pr, ProcSet
  <2>3. QED
    BY <2>1, <2>2

<1>3. QED                              
  (*************************************************************************)PROOF
  (* This follows from a <1>1, <1>2, and a simple TLA proof rule.          *)
  (*************************************************************************)OMITTED
------------------------------------------------------------------------------
(***************************************************************************)
(* The following theorem combined with theorem Invariance shows that the   *)
(* algorithm has the desired space complexity.                             *)
(***************************************************************************)
THEOREM Inv => \A i \in Nat :  (i > Cardinality(Proc)) =>  (A1[i] = {})
<1> SUFFICES ASSUME Inv, NEW i \in Nat, i > Cardinality(Proc)
             PROVE  A1[i] = {}
  OBVIOUS
<1> SUFFICES ~(Cardinality(A1[i]) \geq i)
  BY DEF Inv, InvB
<1>1. A1[i] \subseteq Proc
  BY DEF Inv, TypeOK
<1>2. /\ Cardinality(Proc) \in Nat
      /\ Cardinality(A1[i]) \in Nat
      /\ Cardinality(A1[i]) =< Cardinality(Proc)
 BY ProcFinite, SubsetFinite, CardType, SubsetCardinality2, SMT DEF Inv, TypeOK
<1>3. QED
  BY <1>2, SMT

------------------------------------------------------------------------------
(***************************************************************************)
(*                         The Refinement Proof                            *)
(***************************************************************************)
pcBar == [p \in Proc |-> IF pc[p] = "Done" THEN "Done" ELSE "A"]

(***************************************************************************)
(* For every symbol F defined in module GFXSpec, this defines PS!F to have *)
(* the same definition as F except with every defined constant and         *)
(* variable of GFXSpec replaced by the expression specified in the WITH    *)
(* clause.  Constants and variables not explicitly substituted for in the  *)
(* WITH clause are replaced by the symbols of the same name in module GFX. *)
(***************************************************************************)
PS == INSTANCE GFXSpec WITH pc <- pcBar

(***************************************************************************)
(* The following lemmas are the heart of the proof that algorithm GFX      *)
(* implements/refines algorithm GFXSpec.                                   *)
(***************************************************************************)
LEMMA InitImplication == Init => PS!Init
BY DEF Init, PS!Init, ProcSet, PS!ProcSet, pcBar

LEMMA StepSimulation ==  Inv /\ Inv' /\ [Next]_vars => [PS!Next]_PS!vars
<1> SUFFICES ASSUME Inv, Inv', [Next]_vars
             PROVE  [PS!Next]_PS!vars
  OBVIOUS
<1>1. CASE UNCHANGED vars 
  BY <1>1, SMT DEF vars, PS!vars, pcBar
<1>2. ASSUME NEW p \in Proc, a(p)
      PROVE  [PS!Next]_PS!vars
  <2> pc[p] = "a"
    BY <1>2 DEF a  
  <2>1. CASE /\ known' = [known EXCEPT ![p] 
                           = known[p] \cup UNION {A1[i] : i \in Nat}]
             /\ notKnown' = 
                  [notKnown EXCEPT ![p] = 
                      {i \in 0..(Cardinality(known'[p])) : known'[p] # A1[i]}]
             /\ notKnown'[p] # {}
             /\ pc' = [pc EXCEPT ![p] = "b"]
             /\ UNCHANGED result
             /\ A1' = A1
    <3> /\ result' = result
        /\ pc' = [pc EXCEPT ![p] = "b"]
        /\ pc \in [Proc -> {"a", "b", "Done"}]
        /\ pc[p] = "a"
       BY <2>1 DEF Inv, TypeOK
    <3> /\ pcBar \in [Proc -> {"A", "Done"}]
        /\ pcBar' \in [Proc -> {"A", "Done"}]
      BY DEF pcBar
    <3> SUFFICES ASSUME NEW q \in Proc
                 PROVE  pcBar[q]' = pcBar[q] 
      BY DEF PS!vars
    <3> QED
      BY DEF PS!vars, pcBar  \* SMT used to prove this but doesn't now
  <2>2. CASE /\ known' = [known EXCEPT ![p] 
                           = known[p] \cup UNION {A1[i] : i \in Nat}]
             /\ notKnown' = 
                  [notKnown EXCEPT ![p] = 
                      {i \in 0..(Cardinality(known'[p])) : known'[p] # A1[i]}]
             /\ notKnown'[p] = {}
             /\ result' = [result EXCEPT ![p] = known'[p]]
             /\ pc' = [pc EXCEPT ![p] = "Done"]
             /\ A1' = A1
    <3>1. \A x : Cardinality(x) = PS!Cardinality(x)
        BY DEF Cardinality, PS!Cardinality
    <3>2. pcBar[p] = "A"
      BY <2>2, SMT DEF TypeOK, pcBar
    <3>3. \E P \in { Q \in SUBSET Proc :
                      /\ p \in Q
                      /\ \A q \in Proc\{p}:
                            \/ Cardinality (result[q]) # Cardinality(Q)
                            \/ Q = result[q]
                    }:
               result' = [result EXCEPT ![p] = P]
      <4> DEFINE P == known'[p]
      <4> SUFFICES /\ P \in SUBSET Proc
                   /\ p \in P
                   /\ \A q \in Proc \ {p}:
                            \/ Cardinality (result[q]) # Cardinality(P)
                            \/ P = result[q]
        BY <2>2
      <4>1. P \in SUBSET Proc
        BY DEF TypeOK, Inv
      <4>2. p \in P
        BY DEF InvB, Inv
      <4>3. ASSUME NEW q \in Proc \ {p}
            PROVE  \/ Cardinality (result[q]) # Cardinality(P)
                   \/ P = result[q]
        <5>1. /\ Cardinality(P) \in Nat
              /\ Cardinality(result[q]) \in Nat
              /\ IsFiniteSet(P)
              /\ IsFiniteSet(result[q])
          BY ProcFinite, SubsetFinite, CardType, SMT DEF Inv, TypeOK 
        <5>2. /\ Cardinality(P) # 0
              /\ P # {}
          BY <4>2, <5>1, NonEmptySetCardinality, SMT DEF Done
        <5>3. CASE result[q] = {}
          BY  <5>2, <5>3, EmptySetCardinality,  SMT
        <5>4. CASE result[q] # {}
          <6>1. /\ result'[q] = result[q]
                /\ result'[p] = known'[p]
             BY <2>2, SMT DEF Inv, TypeOK   
          <6>2. QED
            BY <6>1, <5>2, <5>4, SMT DEF Inv, GFXCorrect, Done
        <5>5. QED
          BY <5>3, <5>4
      <4>4. QED
        BY <4>1, <4>2, <4>3
    <3>4. pcBar' = [pcBar EXCEPT ![p] = "Done"]
      <4> /\ pcBar \in [Proc -> {"A", "Done"}]
          /\ pcBar' \in [Proc -> {"A", "Done"}]
        BY DEF pcBar
      <4> SUFFICES ASSUME NEW q \in Proc
                   PROVE  pcBar[q]' = IF q = p THEN "Done"
                                               ELSE pcBar[q] 
        OBVIOUS
      <4> /\ pc' = [pc EXCEPT ![p] = "Done"]
          /\ pc \in [Proc -> {"a", "b", "Done"}]
        BY <2>2 DEF Inv, TypeOK
      <4> QED
        BY SMT DEF pcBar
    <3>5. QED 
      BY  <3>1, <3>2, <3>3, <3>4 DEF PS!A, PS!Next, PS!Pr
  <2>4. QED
    BY <2>1, <2>2, <1>2 DEF a

<1>3. ASSUME NEW p \in Proc, b(p)
      PROVE UNCHANGED PS!vars
  <2> SUFFICES ASSUME NEW q \in Proc
               PROVE  pcBar[q]' = pcBar[q] 
    <3> result' = result
      BY <1>3 DEF b
    <3> pcBar' = pcBar 
      BY DEF pcBar 
    <3> QED
     BY DEF PS!vars 
  <2>1. CASE q = p
    BY <1>3, SMT DEF PS!vars, pcBar, b, Inv, TypeOK
  <2>2. CASE q # p
    BY <1>3, SMT DEF PS!vars, pcBar, b, Inv, TypeOK
  <2>3. QED
    BY <2>1, <2>2
<1>4. QED
  BY <1>1, <1>2, <1>3 DEF Next, Pr

THEOREM Spec => PS!Spec
(***************************************************************************)PROOF
(* This theorem follows easily by simple TLA reasoning from Theorem        *)
(* Invariance and Lemmas InitImplication and StepSimulation.  However,     *)
(* since TLAPS does not yet do temporal reasoning, it can't check the      *)
(* proof, so there's no point writing it out.                              *)
(***************************************************************************)OMITTED
=============================================================================
\* Modification History
\* Last modified Fri Apr 17 12:16:54 CEST 2020 by doligez
\* Last modified Wed Jan 29 16:32:19 CET 2014 by merz
\* Last modified Wed Jan 29 16:29:57 CET 2014 by merz
\* Last modified Tue Jun 25 15:22:24 CEST 2013 by hernanv
\* Last modified Sat Jun 01 10:25:27 CEST 2013 by merz
\* Last modified Fri May 31 05:07:33 PDT 2013 by lamport
\* Last modified Thu Feb 14 18:15:21 CET 2013 by caroledelporte
\* Last modified Thu Feb 14 14:52:13 CET 2013 by caroledelporte
\* Last modified Wed Feb 13 13:37:38 PST 2013 by lamport
\* Last modified Thu Jan 03 11:57:19 CET 2013 by merz
\* Last modified Thu Jan 03 09:18:28 CET 2013 by merz
\* Created Wed Jun 20 01:57:10 PDT 2012 by lamport

