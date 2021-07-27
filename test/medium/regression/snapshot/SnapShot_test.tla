------------------------------- MODULE SnapShot_test ------------------------
EXTENDS Integers, FiniteSets, TLC, TLAPS

CONSTANT Proc, Val
ASSUME ProcFinite == IsFiniteSet(Proc)
ASSUME ValFinite == IsFiniteSet(Val)
  (*************************************************************************)
  (* The assumption that Val is a finite set isn't necessary, but it       *)
  (* simplifies the proof.                                                 *)
  (*************************************************************************)
-----------------------------------------------------------------------------
NUnion(A) == UNION {A[i] : i \in Nat}

(*********************************************************************
--algorithm SnapShot
{  variables  result = [p \in Proc |-> {}],
              A2 = [i \in Nat |-> {}], 
              A3 = [i \in Nat |-> {}],
     process (Pr \in Proc) 
     variables myVals = {},
               known = {},
               notKnown = {},
               lnbpart = 0,
               nbpart = 0,
               nextout = {}, \* This is a history variable, used only
                             \* for the proof
               out = {};
     { a: with ( P \in { Q \in SUBSET Proc :
                           /\ self \in Q
                           /\ \A p \in Proc \ {self}:
                                \/ Cardinality (result[p]) # Cardinality(Q)
                                \/ Q = result[p]
                        } )
             { result[self] := P };   
          A2[Cardinality(result[self])-1] := result[self];
       b: while( TRUE )
            {   with(v \in Val) {myVals := myVals \cup {v}};
                known := myVals \cup known;
                nbpart := Cardinality(NUnion(A2));
            
             c: lnbpart := nbpart;
                known := known \cup NUnion(A3) ;
                notKnown := {i \in 0..(nbpart-1) : known # A3[i]};
                if (notKnown # {}) { d: with (i \in notKnown) 
                                                   { A3[i] := known };
                                        goto c 
                                   }
                else if (nbpart = Cardinality(NUnion(A2))) 
                       { nextout := known };
                       
             e: nbpart := Cardinality(NUnion(A2));
                if (lnbpart = nbpart) {out := known }
                else { goto c }
            }
     }
}
*************************************************************************)
\* BEGIN TRANSLATION
VARIABLES result, A2, A3, pc, myVals, known, notKnown, lnbpart, nbpart, 
          nextout, out

vars == << result, A2, A3, pc, myVals, known, notKnown, lnbpart, nbpart, 
           nextout, out >>

ProcSet == (Proc)

Init == (* Global variables *)
        /\ result = [p \in Proc |-> {}]
        /\ A2 = [i \in Nat |-> {}]
        /\ A3 = [i \in Nat |-> {}]
        (* Process Pr *)
        /\ myVals = [self \in Proc |-> {}]
        /\ known = [self \in Proc |-> {}]
        /\ notKnown = [self \in Proc |-> {}]
        /\ lnbpart = [self \in Proc |-> 0]
        /\ nbpart = [self \in Proc |-> 0]
        /\ nextout = [self \in Proc |-> {}]
        /\ out = [self \in Proc |-> {}]
        /\ pc = [self \in ProcSet |-> "a"]

a(self) == /\ pc[self] = "a"
           /\ \E P \in { Q \in SUBSET Proc :
                           /\ self \in Q
                           /\ \A p \in Proc\{self}:
                                \/ Cardinality (result[p]) # Cardinality(Q)
                                \/ Q = result[p]
                        }:
                result' = [result EXCEPT ![self] = P]
           /\ A2' = [A2 EXCEPT ![Cardinality(result'[self])-1] = result'[self]]
           /\ pc' = [pc EXCEPT ![self] = "b"]
           /\ UNCHANGED << A3, myVals, known, notKnown, lnbpart, nbpart, 
                           nextout, out >>

b(self) == /\ pc[self] = "b"
           /\ \E v \in Val:
                myVals' = [myVals EXCEPT ![self] = myVals[self] \cup {v}]
           /\ known' = [known EXCEPT ![self] = myVals'[self] \cup known[self]]
           /\ nbpart' = [nbpart EXCEPT ![self] = Cardinality(NUnion(A2))]
           /\ pc' = [pc EXCEPT ![self] = "c"]
           /\ UNCHANGED << result, A2, A3, notKnown, lnbpart, nextout, out >>

c(self) == /\ pc[self] = "c"
           /\ lnbpart' = [lnbpart EXCEPT ![self] = nbpart[self]]
           /\ known' = [known EXCEPT ![self] = known[self] \cup NUnion(A3)]
           /\ notKnown' = [notKnown EXCEPT ![self] = {i \in 0..(nbpart[self]-1) : known'[self] # A3[i]}]
           /\ IF notKnown'[self] # {}
                 THEN /\ pc' = [pc EXCEPT ![self] = "d"]
                      /\ UNCHANGED nextout
                 ELSE /\ IF nbpart[self] = Cardinality(NUnion(A2))
                            THEN /\ nextout' = [nextout EXCEPT ![self] = known'[self]]
                            ELSE /\ TRUE
                                 /\ UNCHANGED nextout
                      /\ pc' = [pc EXCEPT ![self] = "e"]
           /\ UNCHANGED << result, A2, A3, myVals, nbpart, out >>

d(self) == /\ pc[self] = "d"
           /\ \E i \in notKnown[self]:
                A3' = [A3 EXCEPT ![i] = known[self]]
           /\ pc' = [pc EXCEPT ![self] = "c"]
           /\ UNCHANGED << result, A2, myVals, known, notKnown, lnbpart, 
                           nbpart, nextout, out >>

e(self) == /\ pc[self] = "e"
           /\ nbpart' = [nbpart EXCEPT ![self] = Cardinality(NUnion(A2))]
           /\ IF lnbpart[self] = nbpart'[self]
                 THEN /\ out' = [out EXCEPT ![self] = known[self]]
                      /\ pc' = [pc EXCEPT ![self] = "b"]
                 ELSE /\ pc' = [pc EXCEPT ![self] = "c"]
                      /\ out' = out
           /\ UNCHANGED << result, A2, A3, myVals, known, notKnown, lnbpart, 
                           nextout >>

Pr(self) == a(self) \/ b(self) \/ c(self) \/ d(self) \/ e(self)

Next == (\E self \in Proc: Pr(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION
-----------------------------------------------------------------------------
(***************************************************************************)
(* The definition of the invariant.                                        *)
(***************************************************************************)
PUnion(Q) == UNION {Q[p] : p \in Proc}

(***************************************************************************)
(* The type-correctness invariant.                                         *)
(***************************************************************************)
TypeOK == /\ result \in [Proc -> SUBSET Proc]
          /\ myVals \in [Proc -> SUBSET Val]
          /\ pc \in [Proc -> {"a", "b", "c", "d", "e"}] 
          /\ A2 \in [Nat -> SUBSET Proc]
          /\ A3 \in [Nat -> SUBSET Val]
          /\ known  \in [Proc -> SUBSET Val]
          /\ nbpart \in [Proc -> Nat]
          /\ lnbpart \in [Proc -> Nat]
          /\ notKnown \in [Proc ->  SUBSET Nat]
          /\ out \in [Proc -> SUBSET Val]
          /\ nextout \in [Proc ->  SUBSET Val]

(***************************************************************************)
(* Inv1 is a straightforward invariant.  Its invariance is fairly easy to  *)
(* see by examining the algorithm's code.                                  *)
(***************************************************************************)
Inv1 ==  /\ \A p \in Proc : 
             /\ known[p] \subseteq  PUnion(myVals) 
             /\ out[p] \subseteq nextout[p]
             /\ nextout[p] \subseteq known[p]
             /\ (pc[p] = "e") => (lnbpart[p] = nbpart[p])
             /\ nbpart[p] =< Cardinality(NUnion(A2))     
             /\ lnbpart[p] =< nbpart[p]
             /\ /\ pc[p] = "e" 
                /\ nbpart[p] = Cardinality(NUnion(A2))
                => (nextout[p] = known[p])
             /\ myVals[p] \subseteq known[p]
             /\ (myVals[p] # {}) => (pc[p] # "a")
             /\ (pc[p] # "a") => /\ p \in result[p]     
                                 /\ A2[Cardinality(result[p])-1] = result[p]           
         /\ NUnion(A3) \subseteq PUnion(myVals)    
         /\ \A i \in Nat : \/ A2[i] = {}
                           \/ \E p \in Proc : /\ pc[p] # "a"
                                              /\ i = Cardinality(result[p]) - 1
                                              /\ A2[i] = result[p] 

(***************************************************************************)
(* We now define invariant Inv2, which is the key to the algorithm's       *)
(* correctness.                                                            *)
(***************************************************************************)
NotAProc == CHOOSE n : n \notin Proc
  (*************************************************************************)
  (* An arbitrary value that is not a process.                             *)
  (*************************************************************************)
  
ReadyToWrite(i, p) == /\ pc[p] = "d" 
                      /\ i \in notKnown[p]
  (*************************************************************************)
  (* True iff process p is ready to write known[p] to A3[i].               *)
  (*************************************************************************)
  
WriterAssignment == {f \in [Nat -> Proc \cup {NotAProc}] :
                        \A i \in Nat : 
                          (f[i] \in Proc) => /\ ReadyToWrite(i, f[i])
                                             /\ \A j \in Nat \ {i} :
                                                    f[j] # f[i] }
  (*************************************************************************)
  (* The set of functions f that assign to each Nat i either a unique      *)
  (* process that is ready to write i or the value NotAProc.               *)
  (*************************************************************************)

PV(wa) == [i \in Nat |-> IF wa[i] = NotAProc THEN A3[i]  
                                             ELSE known[wa[i]]]
         
PA3 == {PV(wa) : wa \in WriterAssignment}
  (*************************************************************************)
  (* PA3 is the set of all values that A3 could assume if some subset of   *)
  (* processes that are ready to write wrote.                              *)
  (*************************************************************************)

Inv2 == \A p \in Proc : 
           \A P \in PA3 : nextout[p] \subseteq NUnion(P)

(***************************************************************************)
(* Inv is the complete inductive invariant.                                *)
(***************************************************************************)
Inv == TypeOK /\ Inv1 /\ Inv2
-----------------------------------------------------------------------------
(***************************************************************************)
(* The following are the same theorems assumed in module GFX.              *)
(***************************************************************************)
THEOREM EmptySetCardinality == Cardinality({}) = 0
PROOF OMITTED

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

THEOREM IntervalCardinality ==
          \A i, j \in Int : i =< j => /\ IsFiniteSet(i..(j-1))
                                      /\ Cardinality(i..(j-1)) = (j-i)
PROOF OMITTED

THEOREM PigeonHolePrinciple ==
         \A S, T :
             /\ IsFiniteSet(S) /\ IsFiniteSet(T) 
             /\ Cardinality(T) < Cardinality(S)
             => \A f \in [S -> T] : 
                   \E x, y \in S : (x # y) /\ (f[x] = f[y])
PROOF OMITTED

COROLLARY InjectionCardinality ==
            \A S, T, f :
               /\ IsFiniteSet(S) /\ IsFiniteSet(T)
               /\ f \in [S -> T]
               /\ \A x, y \in S : x # y => f[x] # f[y]
               => Cardinality(S) =< Cardinality(T)
  BY PigeonHolePrinciple, CardType, SMT
-----------------------------------------------------------------------------
LEMMA NotAProcProp == NotAProc \notin Proc
BY NoSetContainsEverything DEF NotAProc

LEMMA A2monotonic == ASSUME TypeOK, TypeOK', Inv1, NEW p \in Proc, a(p)
                     PROVE  /\ IsFiniteSet(NUnion(A2'))
                            /\ NUnion(A2) \subseteq NUnion(A2')
                            /\ Cardinality(NUnion(A2)) \in Nat
                            /\ Cardinality(NUnion(A2')) \in Nat
                            /\ Cardinality(NUnion(A2)) =< Cardinality(NUnion(A2')) 
<1>1. ASSUME NEW i \in Nat 
      PROVE  A2[i] \subseteq A2'[i]
  <2> DEFINE k == Cardinality(result'[p])
  <2>1. p \in result'[p]
    BY SMT DEF a, TypeOK
  <2>2. k \in Nat /\ k > 0 
    <3>1. IsFiniteSet(result'[p])
      BY SubsetFinite, ProcFinite, SMT DEF TypeOK
    <3>2. QED
      BY <2>1, <3>1, NonEmptySetCardinality, CardType, SMT
  <2>3. CASE i = k-1
    <3>1. CASE A2[i] = {}
      BY <3>1
    <3>2. CASE \E q \in Proc : /\ pc[q] # "a"
                               /\ i = Cardinality(result[q]) - 1
                               /\ A2[i] = result[q]
      <4>1. PICK q \in Proc : /\ pc[q] # "a"
                              /\ i = Cardinality(result[q]) - 1
                              /\ A2[i] = result[q]
        BY <3>2
      <4>2. A2'[i] = result'[p]
        BY <2>2, <2>3, SMT DEF a, TypeOK
      <4>3. result'[p] = result[q]
        <5>1. result'[p] \in { Q \in SUBSET Proc :
                               /\ p \in Q
                               /\ \A pp \in Proc \ {p}:
                                  \/ Cardinality (result[pp]) # Cardinality(Q)
                                  \/ Q = result[pp] }
           BY SMT DEF a, TypeOK
        <5>2. \A pp \in Proc \ {p}:
                 \/ Cardinality (result[pp]) # Cardinality(result'[p])
                 \/ result'[p] = result[pp] 
          BY <5>1
        <5>3. q # p
          BY <4>1 DEF a
        <5>4. Cardinality(result[q]) \in Nat
          BY ProcFinite, SubsetFinite, CardType, SMT DEF TypeOK
        <5>5. Cardinality(result[q]) = Cardinality(result'[p])
          BY <5>4, <4>1, <2>3, <2>2, SMT
        <5>6. result'[p] = result[q]
          BY <5>2, <5>3, <5>5
        <5>7. QED
          BY <4>1, <4>2, <5>6
      <4>4. QED
        BY  <4>1, <4>2, <4>3, SMT
    <3>3. QED
      BY <2>2, <2>3, <3>1, <3>2,  SMT DEF Inv1
  <2>4. CASE i # k-1
    BY <2>4, SMT DEF a, TypeOK
  <2>5. QED
    BY <2>3, <2>4
<1>2. NUnion(A2) \subseteq NUnion(A2')
  BY <1>1, SMT DEF NUnion
<1>3. IsFiniteSet(NUnion(A2'))
  BY ProcFinite, SubsetFinite, SMT DEF NUnion, TypeOK
<1>4. IsFiniteSet(NUnion(A2))
  BY <1>2, <1>3, SubsetFinite
<1>5. QED
  BY <1>2, <1>3, <1>4, CardType, SubsetCardinality2

THEOREM Invariance == Spec => []Inv
<1> USE DEF ProcSet, Pr
<1>1. Init => Inv
  <2> SUFFICES ASSUME Init PROVE Inv
    OBVIOUS
  <2> USE DEF Init, Inv
  <2>1. TypeOK
    BY SMT DEF TypeOK
  <2>2. Inv1
    <3>0. \A i \in Nat : Cardinality(A2[i]) \in {0, i+1}
      BY EmptySetCardinality, SMT DEF Inv1, NUnion, PUnion
    <3>1. \A p \in Proc : 
           /\ known[p] \subseteq  PUnion(myVals) 
           /\ out[p] \subseteq nextout[p]
           /\ nextout[p] \subseteq known[p]
           /\ (pc[p] = "e") => (lnbpart[p] = nbpart[p])
           /\ nbpart[p] =< Cardinality(NUnion(A2))     
           /\ lnbpart[p] =< nbpart[p]
           /\ /\ pc[p] = "e" 
              /\ nbpart[p] = Cardinality(NUnion(A2))
              => (nextout[p] = known[p])
           /\ myVals[p] \subseteq known[p]
           /\ (myVals[p] # {}) => (pc[p] # "a")
           /\ (pc[p] # "a") => /\ p \in result[p]     
                               /\ A2[Cardinality(result[p])-1] = result[p]   
      <4> SUFFICES ASSUME NEW p \in Proc
                   PROVE  /\ known[p] \subseteq  PUnion(myVals) 
                          /\ out[p] \subseteq nextout[p]
                          /\ nextout[p] \subseteq known[p]
                          /\ (pc[p] = "e") => (lnbpart[p] = nbpart[p])
                          /\ nbpart[p] =< Cardinality(NUnion(A2))     
                          /\ lnbpart[p] =< nbpart[p]
                          /\ /\ pc[p] = "e" 
                             /\ nbpart[p] = Cardinality(NUnion(A2))
                             => (nextout[p] = known[p])
                          /\ myVals[p] \subseteq known[p]
                          /\ (myVals[p] # {}) => (pc[p] # "a")
                          /\ (pc[p] # "a") => /\ p \in result[p]     
                                              /\ A2[Cardinality(result[p])-1] = result[p]
        OBVIOUS
      <4>1. known[p] \subseteq  PUnion(myVals)
        BY <3>0, EmptySetCardinality, SMT DEF Inv1, NUnion, PUnion
      <4>2. out[p] \subseteq nextout[p]
        BY <3>0, EmptySetCardinality, SMT DEF Inv1, NUnion, PUnion
      <4>3. nextout[p] \subseteq known[p]
        BY <3>0, EmptySetCardinality, SMT DEF Inv1, NUnion, PUnion
      <4>4. (pc[p] = "e") => (lnbpart[p] = nbpart[p])
        BY <3>0, EmptySetCardinality, SMT DEF Inv1, NUnion, PUnion
      <4>5. nbpart[p] =< Cardinality(NUnion(A2))
        <5> Cardinality(NUnion(A2)) = 0
           BY <3>0, EmptySetCardinality DEF Inv1, NUnion, PUnion
        <5> QED
          BY <3>0, Isa DEF Inv1, NUnion, PUnion
      <4>6. lnbpart[p] =< nbpart[p]
        BY <3>0, EmptySetCardinality, SMT DEF Inv1, NUnion, PUnion
      <4>7. /\ pc[p] = "e" 
            /\ nbpart[p] = Cardinality(NUnion(A2))
            => (nextout[p] = known[p])
        BY <3>0, EmptySetCardinality, SMT DEF Inv1, NUnion, PUnion
      <4>8. myVals[p] \subseteq known[p]
        BY <3>0, EmptySetCardinality, SMT DEF Inv1, NUnion, PUnion
      <4>9. (myVals[p] # {}) => (pc[p] # "a")
        BY <3>0, EmptySetCardinality, SMT DEF Inv1, NUnion, PUnion
      <4>10. (pc[p] # "a") => /\ p \in result[p]     
                              /\ A2[Cardinality(result[p])-1] = result[p]
        BY <3>0, EmptySetCardinality, SMT DEF Inv1, NUnion, PUnion
      <4>11. QED
        BY <4>1, <4>2, <4>3, <4>4, <4>5, <4>6, <4>7, <4>8, <4>9, <4>10      
    <3>2. NUnion(A3) \subseteq PUnion(myVals)
      BY <3>0, EmptySetCardinality, SMT DEF Inv1, NUnion, PUnion
    <3>3. \A i \in Nat : \/ A2[i] = {}
                         \/ \E p \in Proc : /\ pc[p] # "a"
                                            /\ i = Cardinality(result[p]) - 1
                                            /\ A2[i] = result[p]
      BY <3>0, EmptySetCardinality, SMT DEF Inv1, NUnion, PUnion
    <3>4. QED
      BY <3>1, <3>2, <3>3 DEF Inv1
  <2>3. Inv2
    BY SMT DEF Inv2
  <2>4. QED
    BY <2>1, <2>2, <2>3 

<1>2. Inv /\ [Next]_vars => Inv'
  <2> SUFFICES ASSUME Inv, [Next]_vars
               PROVE  Inv'
    OBVIOUS
  <2> USE DEF Inv
  <2>1. ASSUME NEW p \in Proc, pc[p] # "a"
        PROVE  p \in NUnion(A2)
    <3>1. p \in result[p]
      BY <2>1 DEF Inv1
    <3>2. /\ IsFiniteSet(result[p])
          /\ Cardinality(result[p]) \in Nat
      BY ProcFinite, SubsetFinite, CardType,  SMT DEF TypeOK
    <3>3. Cardinality(result[p]) - 1 \in Nat
      BY <3>1, <3>2, NonEmptySetCardinality, SMT
    <3>4. result[p] = A2[Cardinality(result[p])-1]
      BY <2>1 DEF Inv1
    <3>5. QED
      BY <3>1, <3>2, <3>3, <3>4 DEF NUnion
  <2>2. /\ IsFiniteSet(NUnion(A2))
        /\ Cardinality(NUnion(A2)) \in Nat  
    BY ProcFinite, SubsetFinite, CardType, SMT DEF TypeOK, NUnion
  <2>3. PA3 \subseteq [Nat -> SUBSET Val]
    <3> SUFFICES ASSUME NEW wa \in WriterAssignment
                 PROVE  PV(wa) \in [Nat -> SUBSET Val]
      BY DEF PA3
    <3>1. wa \in [Nat -> Proc \cup {NotAProc}]
      BY DEF WriterAssignment
    <3>2. /\ \A i \in Nat : A3[i] \in SUBSET Val
          /\ \A p \in Proc: known[p] \in SUBSET Val
      BY DEF TypeOK
    <3>3. QED
      BY <3>1, <3>2, SMT DEF PV
  <2>4. ASSUME vars' = vars
        PROVE  Inv'
    <3> USE <2>4
    <3>1. TypeOK'
      BY SMT DEF TypeOK, vars
    <3>2. Inv1'
      BY SMT DEF Inv1, vars
    <3>3. Inv2'
      <4> SUFFICES PA3' = PA3
        BY DEF Inv2, vars
      <4>1. ASSUME NEW wa
            PROVE  PV(wa) = PV(wa)'
        <5> A3' = A3 /\ known' = known
          BY DEF vars
        <5> QED
          BY DEF PV
      <4>2. WriterAssignment' = WriterAssignment
        BY SMT DEF WriterAssignment, ReadyToWrite, vars
      <4>3. QED
        BY <4>1, <4>2 DEF PA3
    <3>4. QED
      BY <3>1, <3>2, <3>3
  <2>5. ASSUME NEW p \in Proc, a(p)
        PROVE  Inv'
    <3> USE <2>5
    <3>1. TypeOK'
        BY Isa DEF TypeOK, a    \* SMT worked on 14 Feb 2013, SMT & Z3 timed out on 31 May 2013
    <3>2. Inv1'
      <4>1. p \in result'[p]
           BY SMT DEF TypeOK, a
      <4>2. /\ A2'[Cardinality(result'[p])-1] =  result'[p]
            /\ Cardinality(result'[p]) \in Nat
            /\ Cardinality(result'[p]) > 0
            /\ IsFiniteSet(result'[p])
        <5>1. /\ Cardinality(result'[p]) \in Nat
              /\ IsFiniteSet(result'[p])
          BY ProcFinite, SubsetFinite, CardType, TypeOK', SMT DEF TypeOK                
        <5>2. result'[p] # {}
          BY <4>1
        <5>3.  Cardinality(result'[p]) > 0
          BY <5>1, <5>2, NonEmptySetCardinality, SMT 
        <5>4. QED
          BY <5>1, <5>3, SMT DEF a, TypeOK    
      <4>3. ASSUME NEW q \in Proc
            PROVE  Inv1!1!(q)'
        <5>1. Inv1!1!(q)!1'
          BY SMT DEF Inv1, TypeOK, a
        <5>2. Inv1!1!(q)!2'
          BY SMT DEF Inv1, TypeOK, a
        <5>3. Inv1!1!(q)!3'
          BY SMT DEF Inv1, TypeOK, a
        <5>4. Inv1!1!(q)!4'
          BY SMT DEF Inv1, TypeOK, a          
        <5>5. Inv1!1!(q)!5'
          <6>1. /\ \A i \in Nat : Cardinality(A2[i]) \in Nat
                /\ Cardinality(NUnion(A2)) \in Nat
                /\ Cardinality(NUnion(A2')) \in Nat
                /\ nbpart'[q] \in Nat
            <7>1. nbpart'[q] \in Nat
               BY TypeOK' DEF TypeOK
            <7>2. \A i \in Nat : Cardinality(A2[i]) \in Nat
              BY ProcFinite, SubsetFinite, CardType, SMT DEF TypeOK
            <7>3. QED
              BY <7>1, <7>2, TypeOK', A2monotonic, SMT 
          <6>2. nbpart[q] =< Cardinality(NUnion(A2)) 
            BY SMT DEF Inv1
          <6>3. nbpart' = nbpart
            BY DEF a
          <6>4. QED
            BY <6>1, A2monotonic, TypeOK', <6>2, <6>3,  SMT
        <5>6. Inv1!1!(q)!6'
          BY SMT DEF Inv1, TypeOK, a
        <5>7. Inv1!1!(q)!7'
          <6>1. CASE q # p
            <7>1. /\ pc'[q] = pc[q]
                  /\ nextout'[q] = nextout[q]
                  /\ known'[q] = known[q]
              BY <6>1 DEF a, TypeOK
            <7>2. /\ nbpart'[q] = nbpart[q]
                  /\ nbpart[q] \in Nat
                  /\ nbpart'[q] \in Nat
              BY DEF a, TypeOK
            <7>3. nbpart[q]=< Cardinality(NUnion(A2)) 
              BY DEF Inv1
            <7>4. nbpart'[q] = Cardinality(NUnion(A2'))
              => nbpart[q] = Cardinality(NUnion(A2))
               BY A2monotonic, TypeOK', <7>1, <7>2, <7>3, SMT 
            <7>5 QED
              BY <7>1, <7>4 DEF Inv1, a 
          <6>2. CASE q = p
            BY <6>2, SMT DEF Inv1, TypeOK, a
          <6>3. QED
            BY <6>1, <6>2
        <5>8. Inv1!1!(q)!8'
          BY SMT DEF Inv1, TypeOK, a
        <5>9. Inv1!1!(q)!9'
          BY SMT DEF Inv1, TypeOK, a
        <5>10. Inv1!1!(q)!10'
          <6>3. CASE q # p
            <7>1. /\ pc'[q] = pc[q]
                  /\ result'[q] = result[q]
              BY <6>3 DEF a, TypeOK
            <7>2. SUFFICES ASSUME pc[q] # "a"
                           PROVE  A2'[Cardinality(result[q]) - 1] = result[q]
              BY <7>1, SMT DEF Inv1
            <7>3. \A qq \in Proc \ {p} :
                       \/ Cardinality (result[qq]) # Cardinality(result'[p])
                       \/ result'[p] = result[qq]
              BY SMT DEF a, TypeOK
            <7>4. CASE Cardinality (result[q]) # Cardinality(result'[p])
              <8>1. /\ IsFiniteSet(result[q])
                    /\ Cardinality(result[q]) \in Nat
                BY ProcFinite, SubsetFinite, CardType, SMT DEF TypeOK
              <8>2. q \in result[q]
                BY <7>2, SMT DEF Inv1
              <8>3. Cardinality(result[q]) - 1 \in Nat
                BY <8>1, <8>2, NonEmptySetCardinality, SMT
              <8>4. A2[Cardinality(result[q])-1] = result[q]
                BY <7>2, SMT DEF Inv1
              <8>5. Cardinality(result[q])-1 # Cardinality(result'[p])-1 
                BY <7>4, <8>1, <4>2, SMT
              <8>6. Cardinality(result'[p])-1 \in Nat
                 BY <4>2, SMT 
              <8>7. A2'[Cardinality(result[q])-1] = A2[Cardinality(result[q])-1]
                BY <8>3, <8>6, <8>5, SMT DEF a, TypeOK 
              <8>8. QED
                BY <8>4, <8>7
            <7>5. CASE result'[p] = result[q]
              <8>1. A2[Cardinality(result[q])-1] = result[q]
                BY <7>2, SMT DEF Inv1
              <8>2. QED
                BY <4>2, <8>1, <7>5, SMT
            <7>6. QED
              BY <7>3, <7>4, <7>5, <6>3, SMT
          <6>4. CASE q = p
            BY <4>1, <4>2, <6>4
          <6>5. QED
            BY <6>3, <6>4
        <5>11. QED
          BY <5>1, <5>2, <5>3, <5>4, <5>5, <5>6, <5>7, <5>8, <5>9, <5>10,
            SMT DEF Inv1
      <4>4. NUnion(A3') \subseteq PUnion(myVals') 
        BY SMT DEF Inv1, TypeOK, a
      <4>5. ASSUME NEW i \in Nat 
            PROVE  \/ A2'[i] = {}
                   \/ \E q \in Proc : /\ pc'[q] # "a"
                                      /\ i = Cardinality(result'[q]) - 1
                                      /\ A2'[i] = result'[q] 
        <5>1. CASE i = Cardinality(result'[p]) - 1
          <6>1. pc'[p] # "a"
            BY DEF a, TypeOK
          <6>2. A2'[i] = result'[p]
            BY <4>2, <5>1
          <6>3. QED
            BY <5>1, <6>1, <6>2
        <5>2. CASE i # Cardinality(result'[p]) - 1
          <6>1. A2'[i] = A2[i]
            BY <5>2, <4>2, SMT DEF a, TypeOK
          <6>2. CASE A2[i] = {}
            BY <6>1, <6>2
          <6>3. CASE \E q \in Proc : /\ pc[q] # "a"
                                     /\ i = Cardinality(result[q]) - 1
                                     /\ A2[i] = result[q] 
            <7>1. PICK q \in Proc : /\ pc[q] # "a"
                                    /\ i = Cardinality(result[q]) - 1
                                    /\ A2[i] = result[q] 
              BY <6>3
            <7>2. /\ pc'[q] = pc[q]
                  /\ result'[q] = result[q]
              BY <7>1 DEF a, TypeOK
            <7>3. A2'[i] = A2[i]
              BY <4>2, <5>2, SMT DEF TypeOK, a
            <7>4. QED
              BY <7>1, <7>2, <7>3, SMT 
          <6>4. QED
            BY <6>2, <6>3, SMT DEF Inv1
        <5>3. QED
          BY <5>1, <5>2
      <4>6. QED
        BY <4>3, <4>4, <4>5 DEF Inv1
    <3>3. Inv2'
      <4> SUFFICES PA3' = PA3
        BY DEF Inv2, a
      <4>1. ASSUME NEW wa
            PROVE  PV(wa) = PV(wa)'
        <5> A3' = A3 /\ known' = known
          BY DEF a
        <5> QED
          BY DEF PV
      <4>2. WriterAssignment' = WriterAssignment
        <5>1. ASSUME NEW q \in Proc 
              PROVE  (pc[q] = "d") = (pc'[q]="d")
          <6>1. pc[q] = "d" => p # q
             BY DEF a
          <6>2. pc'[q] = "d" => p # q
            BY DEF a, TypeOK
          <6>3. p # q => pc'[q]= pc[q]
            BY DEF a, TypeOK
          <6>4. QED
            BY <6>1, <6>2, <6>3 
        <5>2. \A i \in Nat, q \in Proc : ReadyToWrite(i, q) = ReadyToWrite(i, q)'
          BY <5>1, SMT DEF ReadyToWrite, a, TypeOK
          \** 2013-06-25 DEF TypeOK missing
        <5>3. QED
          BY <5>2, SMT DEF WriterAssignment
      <4>3. QED
        BY <4>1, <4>2 DEF PA3
    <3>4. QED
      BY <3>1, <3>2, <3>3
  <2>6. ASSUME NEW p \in Proc, b(p)
        PROVE  Inv'
    <3> USE <2>6
    <3>1. TypeOK'
      <4>1. TypeOK!1'
        BY SMT DEF TypeOK, b
      <4>2. TypeOK!2'
        BY SMT DEF TypeOK, b
      <4>3. TypeOK!3'
        BY SMT DEF TypeOK, b
      <4>4. TypeOK!4'
        BY SMT DEF TypeOK, b
      <4>5. TypeOK!5'
        BY SMT DEF TypeOK, b
      <4>6. TypeOK!6'
        BY SMT DEF TypeOK, b
      <4>7. TypeOK!7'
        BY <2>2, SMT DEF TypeOK, b
      <4>8. TypeOK!8'
        BY SMT DEF TypeOK, b
      <4>9. TypeOK!9'
        BY SMT DEF TypeOK, b
      <4>10. TypeOK!10'
        BY SMT DEF TypeOK, b
      <4>11. TypeOK!11'
        BY SMT DEF TypeOK, b
      <4>12. QED
        BY <4>1, <4>2, <4>3, <4>4, <4>5, <4>6, 
           <4>7, <4>8, <4>9, <4>10, <4>11, SMT DEF TypeOK
    <3>2. Inv1'
      <4>1. ASSUME NEW q \in Proc
            PROVE  Inv1!1!(q)'
        <5>1. Inv1!1!(q)!1'
          BY SMT DEF Inv1, TypeOK, b, PUnion
        <5>2. Inv1!1!(q)!2'
          BY SMT DEF Inv1, TypeOK, b
        <5>3. Inv1!1!(q)!3'
          BY SMT DEF Inv1, TypeOK, b
        <5>4. Inv1!1!(q)!4'
          BY SMT DEF Inv1, TypeOK, b
        <5>5. nbpart'[q] =< Cardinality(NUnion(A2'))
          <6>1. CASE q # p
            BY <6>1, SMT DEF b, TypeOK, Inv1
          <6>2. CASE q = p
            <7> nbpart'[q] = Cardinality(NUnion(A2))
              BY <6>2, SMT DEF b, TypeOK
            <7> QED
              BY TypeOK', <6>2, SMT DEF b, TypeOK
          <6>3. QED
            BY <6>1, <6>2
        <5>6. lnbpart'[q] =< nbpart'[q]
          <6>1. CASE q # p
            BY <6>1, SMT DEF b, TypeOK, Inv1
          <6>2. CASE q = p
            <7> /\ nbpart'[q] = Cardinality(NUnion(A2))
                /\ lnbpart'[q] = lnbpart[q]
              BY <6>2, SMT DEF b, TypeOK
            <7> /\ lnbpart[q] =< nbpart[q]
                /\ nbpart[q] =< Cardinality(NUnion(A2))
              BY DEF Inv1
            <7> /\ nbpart'[q] \in Nat
                /\ nbpart[q] \in Nat
                /\ lnbpart[q] \in Nat
             BY TypeOK' DEF TypeOK
            <7> QED
              BY SMT
          <6>3. QED
            BY <6>1, <6>2
        <5>7. Inv1!1!(q)!7'
          BY SMT DEF Inv1, TypeOK, b
        <5>8. Inv1!1!(q)!8'
          BY SMT DEF Inv1, TypeOK, b
        <5>9. Inv1!1!(q)!9'
          BY SMT DEF Inv1, TypeOK, b
        <5>10. Inv1!1!(q)!10'
          BY SMT DEF Inv1, TypeOK, b
        <5>11. QED
          BY <5>1, <5>2, <5>3, <5>4, <5>5, <5>6, <5>7, <5>8, <5>9, <5>10,
            SMT DEF Inv1
      <4>2. NUnion(A3') \subseteq PUnion(myVals') 
        BY SMT DEF TypeOK, Inv1, b, PUnion
      <4>3. Inv1!3'
        BY SMT DEF Inv1, TypeOK, b
      <4>4. QED
        BY <4>1, <4>2, <4>3 DEF Inv1
    <3>3. Inv2'
      <4> SUFFICES PA3' = PA3
        BY DEF Inv2, b
      <4>1. WriterAssignment' = WriterAssignment
        <5>1. ASSUME NEW q \in Proc 
              PROVE  (pc[q] = "d") = (pc'[q]="d")
          <6>1. pc[q] = "d" => p # q
             BY DEF b
          <6>2. pc'[q] = "d" => p # q
            BY DEF b, TypeOK
          <6>3. p # q => pc'[q]= pc[q]
            BY DEF b, TypeOK
          <6>4. QED
            BY <6>1, <6>2, <6>3 
        <5>2. \A i \in Nat, q \in Proc : ReadyToWrite(i, q) = ReadyToWrite(i, q)'
          BY <5>1, SMT  DEF ReadyToWrite, b, TypeOK
          \** 2013-06-25 DEF TypeOK missing
        <5>3. QED
          BY <5>2, SMT DEF WriterAssignment
      <4>2. ASSUME NEW wa \in WriterAssignment
            PROVE  PV(wa) = PV(wa)'
        <5>1. A3' = A3 
          BY DEF b
        <5>2. ASSUME wa \in WriterAssignment, NEW i \in Nat, wa[i] # NotAProc 
              PROVE known'[wa[i]] = known[wa[i]]
          <6>1. wa[i] \in Proc
            BY <5>2, SMT DEF WriterAssignment
          <6>2. ReadyToWrite(i, wa[i])
            BY  <5>2, <6>1, SMT DEF WriterAssignment
          <6>3. pc[wa[i]] = "d"
            BY <6>2 DEF ReadyToWrite
          <6>4. wa[i] # p
            BY <6>3 DEF b
          <6>5. QED
            BY <6>4, <6>1, SMT DEF TypeOK, b
            \** 2013-06-25 <6>1 missing
        <5>3. ASSUME NEW i \in Nat, wa \in WriterAssignment 
              PROVE  (IF wa[i] = NotAProc THEN A3[i] ELSE known[wa[i]]) =
                               (IF wa[i] = NotAProc THEN A3'[i] ELSE known'[wa[i]])
          <6>1. CASE wa[i] = NotAProc
            BY <5>1, <5>2, <6>1
          <6>2. CASE wa[i] # NotAProc
            BY <5>1, <5>2, <6>2
          <6>3. QED
            BY <6>1, <6>2
        <5>4. QED
          BY <5>3 DEF PV
      <4>3. QED
        BY <4>2, <4>1 DEF PA3
    <3>4. QED
      BY <3>1, <3>2, <3>3
  <2>7. ASSUME NEW p \in Proc, c(p)
        PROVE  Inv'
    <3> USE <2>7
    <3>1. TypeOK'
      BY SMT DEF TypeOK, c, NUnion
    <3>2. Inv1'
      <4>1. ASSUME NEW q \in Proc
            PROVE  Inv1!1!(q)'
        <5>1. known'[q] \subseteq PUnion(myVals')
          <6>1. CASE p # q
            BY <6>1, SMT DEF c, TypeOK, Inv1, PUnion
          <6>2. CASE p = q
            <7>1. known[p] \subseteq PUnion(myVals)
              BY DEF Inv1
            <7>2. NUnion(A3) \subseteq PUnion(myVals)
              BY SMT DEF c, Inv1
            <7>3. QED
              BY <6>2, <7>1, <7>2, SMT DEF c, TypeOK
          <6>3. QED
            BY <6>1, <6>2
        <5>2. Inv1!1!(q)!2'
          BY SMT DEF Inv1, TypeOK, c
        <5>3. Inv1!1!(q)!3'
          BY SMT DEF Inv1, TypeOK, c
        <5>4. Inv1!1!(q)!4'
          BY SMT DEF Inv1, TypeOK, c
        <5>5. Inv1!1!(q)!5'
          BY SMT DEF Inv1, TypeOK, c
        <5>6. Inv1!1!(q)!6'
          <6>1. CASE q # p
             BY <6>1, SMT DEF Inv1, TypeOK, c
          <6>2. CASE q = p
             BY <6>2, SMT DEF Inv1, TypeOK, c
          <6>3. QED
            BY <6>1, <6>2
        <5>7. Inv1!1!(q)!7'
          BY DEF Inv1, TypeOK, c
        <5>8. Inv1!1!(q)!8'
          BY SMT DEF Inv1, TypeOK, c
        <5>9. Inv1!1!(q)!9'
          BY SMT DEF Inv1, TypeOK, c
        <5>10. Inv1!1!(q)!10'
          BY SMT DEF Inv1, TypeOK, c
        <5>11. QED
          BY <5>1, <5>2, <5>3, <5>4, <5>5, <5>6, <5>7, <5>8, <5>9, <5>10,
            SMT DEF Inv1
      <4>2. NUnion(A3') \subseteq PUnion(myVals') 
        BY SMT DEF Inv1, TypeOK, c
      <4>3. Inv1!3'
        BY SMT DEF Inv1, TypeOK, c
      <4>4. QED
        BY <4>1, <4>2, <4>3 DEF Inv1
    <3>3. Inv2'
      <4> SUFFICES ASSUME NEW q \in Proc, NEW P \in PA3'
                   PROVE  nextout'[q] \subseteq NUnion(P)
        BY DEF Inv2 
      <4>1. CASE notKnown'[p] # {}
        <5>1. /\ pc[p] = "c"
              /\ lnbpart' = [lnbpart EXCEPT ![p] = nbpart[p]]
              /\ known' = [known EXCEPT ![p] = 
                             known[p] \cup UNION {A3[i] : i \in Nat}]
              /\ notKnown' = [notKnown EXCEPT ![p] = 
                               {i \in 0..(nbpart[p]-1) : 
                                   known'[p] # A3[i]}]
              /\ notKnown'[p] # {}
              /\ pc' = [pc EXCEPT ![p] = "d"]
              /\ UNCHANGED nextout
              /\ UNCHANGED << result, A2, A3, myVals, nbpart, out >>
           BY <4>1 DEF c, NUnion
        <5>2. CASE P \in PA3
          BY <5>1, <5>2, SMT DEF Inv2
        <5>3. CASE P \in PA3' \ PA3
          <6>1. PICK i \in Nat : 
                      /\ ReadyToWrite(i, p)'
                      /\ P[i] = known'[p]
                      /\ \E wa \in WriterAssignment' : /\ wa[i] = p
                                                       /\ P = PV(wa)'
            <7>1. PICK wa \in WriterAssignment' : /\ P = PV(wa)'
                                                  /\ PV(wa)' \in PA3'
                                                  /\ PV(wa)' \notin PA3
              BY <5>3 DEF PA3
            <7>2. CASE wa \notin WriterAssignment
              <8>1. PICK i \in Nat : /\ wa[i] \in Proc
                                     /\ ~ReadyToWrite(i, wa[i])
                                     /\ ReadyToWrite(i, wa[i])'
                BY <7>2, SMT DEF WriterAssignment
              <8>2. wa[i] = p
                BY <8>1, SMT  DEF c, TypeOK, ReadyToWrite
              <8>3. QED
                BY <8>1, <8>2, <7>1, NotAProcProp DEF PV
            <7>3. CASE wa \in WriterAssignment /\ PV(wa) # PV(wa)'
              <8>1. PICK i \in Nat : PV(wa)[i] # PV(wa)'[i]
                 <9> /\ PV(wa) = [i \in Nat |-> PV(wa)[i]]
                     /\ PV(wa)' = [i \in Nat |-> PV(wa)'[i]]
                   BY DEF PV
                 <9> QED
                   BY <7>3
              <8>2. wa[i] = p
                BY <8>1, SMT DEF c, TypeOK, PV, WriterAssignment
                \** 2013-06-25 DEF WriterAssignment missing
              <8>3. ReadyToWrite(i, p)'
                BY <8>2, SMT DEF WriterAssignment
              <8>4. PV(wa)'[i] = known'[wa[i]]
                BY <8>2, NotAProcProp  DEF PV
              <8>5. QED
                BY <8>2, <8>3, <8>4, <7>1
            <7>4. QED
              BY <7>1, <7>2, <7>3 DEF PA3
          <6> DEFINE Q == [P EXCEPT ![i] = A3[i]]
          <6>2. Q \in PA3
            <7>1. PICK wa \in WriterAssignment' : /\ wa[i] = p
                                                  /\ P = PV(wa)'
              BY <6>1
            <7> DEFINE za == [wa EXCEPT ![i] = NotAProc]
            <7>2. ASSUME NEW j \in Nat, j # i
                  PROVE  wa[j] # p  /\  PV(wa)'[j] = PV(wa)[j]
              <8>1. wa[j] # p
                BY <7>1, <7>2, SMT DEF WriterAssignment
              <8>2. QED
                BY <8>1, SMT DEF PV, c, TypeOK, WriterAssignment  
                \** 2013-06-25 DEF WriterAssignment missing
            <7>3. za \in WriterAssignment
              <8>1. wa \in [Nat -> Proc \cup {NotAProc}]
                BY DEF WriterAssignment
              <8>2. za \in [Nat -> Proc \cup {NotAProc}]
                BY <8>1
              <8> SUFFICES ASSUME NEW j \in Nat, za[j] \in Proc
                           PROVE  /\ ReadyToWrite(j, za[j])
                                  /\ \A k \in Nat \ {j} : za[k] # za[j] 
                BY <8>2 DEF WriterAssignment
              <8>4. CASE j = i
                BY <8>1, <8>4, NotAProcProp 
              <8>5. CASE j # i
                <9>1. za[j] = wa[j]
                  BY <8>1, <8>5
                <9>2. za[j] # p
                  BY <8>5, <9>1, <7>1, SMT DEF WriterAssignment
                <9>3. ReadyToWrite(j, za[j])
                  <10> ReadyToWrite(j, za[j])'
                    BY <9>1, SMT DEF WriterAssignment
                  <10> QED
                    BY <9>2, SMT DEF c, TypeOK, ReadyToWrite, WriterAssignment 
                    \** 2013-06-25 DEF WriterAssignment missing
                <9>4. ASSUME NEW k \in Nat \ {j}
                      PROVE  za[k] # za[j]
                  <10> CASE k = i
                     BY <8>1, NotAProcProp, SMT
                  <10> CASE k # i
                    BY <9>1, <9>4, <8>1, SMT DEF WriterAssignment
                  <10> QED
                     OBVIOUS
                <9>5. QED
                  BY <9>3, <9>4
              <8>6. QED
                BY <8>4, <8>5
            <7>4. Q = PV(za)
              <8> /\ PV(za) = [j \in Nat |-> PV(za)[j]]
                  /\ PV(wa)' = [j \in Nat |-> PV(wa)'[j]]
                BY Isa DEF PV
              <8> wa = [j \in Nat |-> wa[j]]
                BY DEF WriterAssignment
              <8> za = [j \in Nat |-> za[j]]
                OBVIOUS
              <8> PV(za)[i] = A3[i]
                BY NotAProcProp DEF PV
              <8> ASSUME NEW j \in Nat, j # i
                  PROVE  PV(za)[j] = PV(wa)[j]
                BY DEF PV
              <8> HIDE DEF za
              <8> QED
                 BY <7>1, <7>2, NotAProcProp
            <7>5. QED
              BY <7>3, <7>4 DEF PA3
          <6>3. nextout[q] \subseteq NUnion(Q)
            BY <6>2 DEF Inv2
          <6>4. A3[i] \subseteq known'[p]
            BY <5>1, SMT DEF TypeOK
          <6>5. Q[i] \subseteq P[i]
\*            BY <6>1, <6>2, <6>4, <2>3, SMT DEF PV \** TO FIX: translation error
            BY <6>1, <6>2, <6>4, <2>3, i \in DOMAIN P, SMT
            \** 2013-06-25 'i \in DOMAIN P' missing
          <6>6. NUnion(Q) \subseteq NUnion(P)
            <7> SUFFICES ASSUME NEW j \in Nat
                         PROVE  Q[j] \subseteq P[j]
              BY DEF NUnion
            <7> CASE j # i
              <8> P = [k \in Nat |-> P[k]]
                BY <5>3 DEF PA3, PV
              <8> QED
                OBVIOUS
            <7> QED
              BY <6>5
          <6>7. nextout'[q] = nextout[q]
            BY <5>1
          <6>8. QED
            BY <6>3, <6>6, <6>7
        <5>4 QED
          BY <5>2, <5>3
      <4>2. CASE /\ notKnown'[p] = {}
                 /\ nbpart[p] = Cardinality(NUnion(A2))
        <5>1. /\ pc[p] = "c"
              /\ lnbpart' = [lnbpart EXCEPT ![p] = nbpart[p]]
              /\ known' = [known EXCEPT ![p] = 
                             known[p] \cup UNION {A3[i] : i \in Nat}]
              /\ notKnown' = [notKnown EXCEPT ![p] = 
                                 {i \in 0..(nbpart[p]-1) : 
                                        known'[p] # A3[i]}]
              /\ notKnown'[p] = {}
              /\ nbpart[p] = Cardinality(NUnion(A2))
              /\ nextout' = [nextout EXCEPT ![p] = known'[p]]
              /\ pc' = [pc EXCEPT ![p] = "e"]
              /\ UNCHANGED << result, A2, A3, myVals, nbpart, out >>
          BY <4>2 DEF c, NUnion 
        <5>2. PA3' = PA3
          <6>1. ASSUME NEW i \in Nat, NEW r \in Proc
                PROVE  ReadyToWrite(i, r)' = ReadyToWrite(i, r)
            BY <5>1, SMT DEF ReadyToWrite, TypeOK
          <6>2. WriterAssignment' = WriterAssignment
            BY <6>1, SMT DEF WriterAssignment
          <6>3. ASSUME NEW wa \in WriterAssignment, NEW i \in Nat,
                       wa[i] # NotAProc
                PROVE  known'[wa[i]] = known[wa[i]]
            <7> USE <6>3
            <7>1. ReadyToWrite(i, wa[i])
              BY NotAProcProp, SMT DEF WriterAssignment
            <7>2. wa[i] # p
              BY <5>1, <7>1, SMT DEF ReadyToWrite
            <7>3. wa[i] \in Proc
              BY SMT DEF WriterAssignment 
            <7>4. QED
              BY <7>2, <7>3, <5>1, SMT DEF TypeOK
          <6>4. A3' = A3
            BY <5>1
          <6>5. QED
            <7> SUFFICES ASSUME NEW wa \in WriterAssignment,
                                NEW i \in Nat
                         PROVE  PV(wa)[i] = PV(wa)[i]'
              <8> ASSUME NEW wa \in WriterAssignment
                  PROVE  /\ PV(wa) =  [i \in Nat |-> PV(wa)[i]]
                         /\ PV(wa)' = [i \in Nat |-> PV(wa)[i]]
                BY DEF PV
              <8> QED
                BY <6>2 DEF PA3
            <7>1. CASE wa[i] = NotAProc
              BY <7>1, <6>4 DEF PA3, PV
            <7>2. CASE wa[i] # NotAProc
              BY <7>2, <6>3 DEF PA3, PV
            <7>3. QED
              BY <7>1, <7>2
        <5>3. SUFFICES ASSUME p = q
                       PROVE  nextout'[q] \subseteq NUnion(P)
          <6> SUFFICES ASSUME p # q
                       PROVE  nextout'[q] \subseteq NUnion(P)
              OBVIOUS
          <6> nextout'[q] = nextout[q]
            BY <5>1, SMT DEF TypeOK
          <6> QED
            BY <5>2 DEF Inv2
        <5>4. /\ \A i \in 0..(nbpart[p]-1) : known'[p] = A3[i]
              /\ known'[p] = NUnion(A3)
              /\ nbpart[p]-1 >= 0
          <6>1. \A i \in 0..(nbpart[p]-1) : known'[p] = A3[i]
             <7> /\ notKnown'[p] = {i \in 0..(nbpart[p]-1) : 
                                        known'[p] # A3[i]}
                 /\ notKnown'[p] = {}
               BY <5>1, SMT DEF TypeOK
             <7> QED
               OBVIOUS
          <6>2. nbpart[p]-1 >= 0
            <7>1. NUnion(A2) # {}
              BY <5>1, <2>1
            <7>2.  Cardinality(NUnion(A2)) > 0
              BY <2>2, <7>1, NonEmptySetCardinality, SMT
            <7>3. QED
              BY <2>2, <5>1, <7>2, SMT 
          <6>3. known'[p] = A3[0]
            BY <6>1, <6>2, SMT DEF TypeOK
          <6>4. NUnion(A3) \subseteq known'[p]
            BY <5>1 DEF NUnion, TypeOK
          <6>5. NUnion(A3) = known'[p]
            BY <6>3, <6>4 DEF NUnion
          <6>6. QED
            BY <6>1, <6>2, <6>5
        <5>5. CASE \E i \in 0..(nbpart[p]-1) : P[i] = A3[i]
          <6>1. PICK i \in 0..(nbpart[p]-1) : P[i] = A3[i]
            BY <5>5
          <6>2. A3[i] \subseteq NUnion(P)
            BY <6>1, SMT DEF NUnion, TypeOK
          <6>3. known'[p] \subseteq NUnion(P)
            BY <6>2, <5>4
          <6>4. nextout'[p] = known'[p]
            BY <5>1, SMT DEF TypeOK
          <6>5. QED
            BY <6>3, <6>4, <5>3
        <5>6. CASE \A i \in 0..(nbpart[p]-1) : P[i] # A3[i]
          <6> PICK wa \in WriterAssignment : P = PV(wa)
            BY <5>2 DEF PA3
          <6>1. \A i \in 0..(nbpart[p]-1) : /\ wa[i] # NotAProc
                                            /\ P[i] = known[wa[i]]
            BY <5>6, SMT DEF PV
          <6>2. \A i \in 0..(nbpart[p]-1) : /\ wa[i] \in Proc
                                            /\ ReadyToWrite(i, wa[i])
            <7>1. nbpart[p] \in Nat
              BY DEF TypeOK
            <7> SUFFICES ASSUME NEW i \in 0..(nbpart[p]-1)
                         PROVE  /\ wa[i] \in Proc
                                /\ ReadyToWrite(i, wa[i])
              OBVIOUS
            <7> i \in Nat
              BY <7>1, SMT
            <7>2. wa[i] \in Proc
              BY <6>1, SMT DEF WriterAssignment
            <7>3. QED
              BY <6>1, SMT DEF WriterAssignment
          <6>3. \A i, j \in 0..(nbpart[p]-1) : (i # j) => (wa[i] # wa[j])
           <7> nbpart[p] \in Nat
             BY DEF TypeOK
           <7> QED
             BY <6>1, <6>2, SMT DEF WriterAssignment
          <6> DEFINE S == {wa[i] : i \in 0..(nbpart[p]-1)}
          <6>4. Cardinality(S) = nbpart[p]
            <7> DEFINE T == 0..(nbpart[p]-1)
            <7>1. /\ IsFiniteSet(T)
                  /\ Cardinality(T) = nbpart[p]
                  /\ nbpart[p] \in Int
              BY IntervalCardinality, Z3 DEF TypeOK           
            <7>2. IsFiniteSet(S)
               <8>1. ASSUME NEW s \in S
                     PROVE  s \in Proc
                 <9>1. nbpart[p] \in Nat
                   BY DEF TypeOK 
                 <9>2. QED
                   BY <9>1, <6>1, Z3 DEF WriterAssignment   \* SMT worked on 14 Feb 2013, timed out on 31 May 2013
               <8>2. QED
                 BY <8>1, ProcFinite, SubsetFinite, SMT
            <7>3. Cardinality(S) =< nbpart[p]
              <8> DEFINE f == [s \in S |-> CHOOSE i \in T : s = wa[i]]
              <8>1. \A s \in S : /\ s = wa[f[s]]
                                 /\ f[s] \in T
                OBVIOUS
              <8>2. f \in [S ->T]
                 BY <8>1
              <8> HIDE DEF f, S, T
              <8>3. \A x, y \in S : x # y => f[x] # f[y]
                BY <8>1, SMT
              <8>4. QED
                BY <7>1, <7>2, <8>2, <8>3, InjectionCardinality, Z3
            <7>4. nbpart[p] =< Cardinality(S)
              <8> DEFINE f == [i \in T |-> wa[i]]
              <8>1. f \in [T -> S]
                BY SMT
              <8>2. \A x, y \in T : x # y => f[x] # f[y]
                BY <6>3
              <8>3. nbpart[p] \in Int
                BY Isa DEF TypeOK
              <8> HIDE DEF T, S, f
              <8>4. QED
                BY  <7>2, <8>1, <8>2, <7>1, InjectionCardinality, Z3
            <7>5. QED
              BY <7>2, <7>3, <7>4, CardType, Z3 DEF TypeOK  \** 2013-06-01: SMT fails
          <6>5. \A s \in S : /\ pc[s] = "d"
                             /\ s \in NUnion(A2)
            <7> SUFFICES ASSUME NEW s \in S PROVE s \in NUnion(A2) /\ pc[s] = "d"
              OBVIOUS
            <7>1. PICK i \in 0..(nbpart[p]-1) : s = wa[i]
              OBVIOUS
            <7>2. i \in Nat
              BY SMT DEF TypeOK
            <7>3. wa[i] \in Proc 
              BY <6>1, <7>1, <7>2, SMT DEF WriterAssignment
            <7>4. pc[s] = "d"
              BY <7>1, <7>3, SMT DEF WriterAssignment, ReadyToWrite
            <7>5. QED
              BY <7>4, <7>1, <7>3, <2>1 
          <6>6. Cardinality(S)= Cardinality(NUnion(A2))
            BY <6>4, <5>1
          <6>7. S = NUnion(A2)
            <7>1. S \subseteq NUnion(A2)
              BY <6>5, SMT
            <7>2. S # NUnion(A2) => Cardinality(S) < Cardinality(NUnion(A2))
              BY <7>1, <2>2, SubsetCardinality, SMT
            <7>3. QED
              BY  <2>2, <7>2, <6>6, SMT
          <6>8. p \in NUnion(A2)
            BY <2>1, <5>1 
          <6>9. QED
            BY <5>1, <6>8, <6>7, <6>5 
        <5>7. QED
          BY <5>5, <5>6
      <4>3. CASE /\ notKnown'[p] = {}
                 /\ nbpart[p] # Cardinality(NUnion(A2))
        <5>1. /\ pc[p] = "c"
              /\ lnbpart' = [lnbpart EXCEPT ![p] = nbpart[p]]
              /\ known' = [known EXCEPT ![p] = 
                             known[p] \cup UNION {A3[i] : i \in Nat}]
              /\ notKnown' = [notKnown EXCEPT ![p] = 
                                {i \in 0..(nbpart[p]-1) : 
                                     known'[p] # A3[i]}]
              /\ notKnown'[p] = {}
              /\ nbpart[p] # Cardinality(NUnion(A2))
              /\ UNCHANGED nextout
              /\ pc' = [pc EXCEPT ![p] = "e"]
              /\ UNCHANGED << result, A2, A3, myVals, nbpart, out >>
          BY <4>3 DEF c, NUnion 
        <5>2. PA3' = PA3
          (*****************************************************************)
          (* This proof copied from the proof of CASE <4>2.                *)
          (*****************************************************************)
          <6>1. ASSUME NEW i \in Nat, NEW r \in Proc
                PROVE  ReadyToWrite(i, r)' = ReadyToWrite(i, r)
            BY <5>1, SMT DEF ReadyToWrite, TypeOK
          <6>2. WriterAssignment' = WriterAssignment
            BY <6>1, SMT DEF WriterAssignment
          <6>3. ASSUME NEW wa \in WriterAssignment, NEW i \in Nat,
                       wa[i] # NotAProc
                PROVE  known'[wa[i]] = known[wa[i]]
            <7> USE <6>3
            <7>1. ReadyToWrite(i, wa[i])
              BY NotAProcProp, SMT DEF WriterAssignment
            <7>2. wa[i] # p
              BY <5>1, <7>1, SMT DEF ReadyToWrite
            <7>3. wa[i] \in Proc
              BY SMT DEF WriterAssignment 
            <7>4. QED
              BY <7>2, <7>3, <5>1, SMT DEF TypeOK
          <6>4. A3' = A3
            BY <5>1
          <6>5. QED
            <7> SUFFICES ASSUME NEW wa \in WriterAssignment,
                                NEW i \in Nat
                         PROVE  PV(wa)[i] = PV(wa)[i]'
              <8> ASSUME NEW wa \in WriterAssignment
                  PROVE  /\ PV(wa) =  [i \in Nat |-> PV(wa)[i]]
                         /\ PV(wa)' = [i \in Nat |-> PV(wa)[i]]
                BY DEF PV
              <8> QED
                BY <6>2 DEF PA3
            <7>1. CASE wa[i] = NotAProc
              BY <7>1, <6>4 DEF PA3, PV
            <7>2. CASE wa[i] # NotAProc
              BY <7>2, <6>3 DEF PA3, PV
            <7>3. QED
              BY <7>1, <7>2
        <5>3. QED
          BY <5>1, <5>2 DEF Inv2
       <4>4. QED
         BY <4>1, <4>2, <4>3
    <3>4. QED
      BY <3>1, <3>2, <3>3
  <2>8. ASSUME NEW p \in Proc, d(p)
        PROVE  Inv'
    <3> USE <2>8
    <3>1. TypeOK'
      BY SMT DEF TypeOK, d
    <3>2. Inv1'
      <4>1. ASSUME NEW q \in Proc
            PROVE  Inv1!1!(q)'
        <5>1. Inv1!1!(q)!1'
          BY SMT DEF Inv1, TypeOK, d
        <5>2. Inv1!1!(q)!2'
          BY SMT DEF Inv1, TypeOK, d
        <5>3. Inv1!1!(q)!3'
          BY SMT DEF Inv1, TypeOK, d
        <5>4. Inv1!1!(q)!4'
          BY SMT DEF Inv1, TypeOK, d
        <5>5. Inv1!1!(q)!5'
          BY SMT DEF Inv1, TypeOK, d
        <5>6. Inv1!1!(q)!6'
          BY SMT DEF Inv1, TypeOK, d
        <5>7. Inv1!1!(q)!7'
          BY SMT DEF Inv1, TypeOK, d
        <5>8. Inv1!1!(q)!8'
          BY SMT DEF Inv1, TypeOK, d
        <5>9. Inv1!1!(q)!9'
          BY SMT DEF Inv1, TypeOK, d
        <5>10. Inv1!1!(q)!10'
          BY SMT DEF Inv1, TypeOK, d
        <5>11. QED
          BY <5>1, <5>2, <5>3, <5>4, <5>5, <5>6, <5>7, <5>8, <5>9, <5>10,
            SMT DEF Inv1
      <4>2. NUnion(A3') \subseteq PUnion(myVals') 
        <5>1. PICK j \in notKnown[p] : A3' = [A3 EXCEPT ![j] = known[p]]
          BY DEF d
        <5> j \in Nat
          BY DEF TypeOK
        <5>2. A3'[j] = known[p]
          BY <5>1, SMT DEF TypeOK, Inv1
        <5>3. known[p] \subseteq PUnion(myVals)
          BY SMT DEF Inv1
        <5>4. \A i \in Nat : A3[i] \subseteq PUnion(myVals)
          BY SMT DEF TypeOK, Inv1, NUnion
        <5>5. ASSUME NEW i \in Nat
              PROVE  A3'[i] \subseteq PUnion(myVals)
          <6>1. CASE i # j
            BY <6>1, <5>4, <5>1, SMT DEF TypeOK
          <6>2. CASE i = j
            BY <6>1, <5>2, <5>3, SMT
          <6>3. QED
            BY <6>1, <6>2
        <5>6. myVals = myVals'
          BY DEF d
        <5>7. QED
          BY <5>5, <5>6, SMT DEF NUnion
      <4>3. Inv1!3'
        BY SMT DEF Inv1, TypeOK, d
      <4>4. QED
        BY <4>1, <4>2, <4>3 DEF Inv1
    <3>3. Inv2'
      <4> SUFFICES PA3' \subseteq PA3
        BY DEF d, Inv2
      <4> SUFFICES ASSUME NEW P \in PA3'
                   PROVE  P \in PA3
        OBVIOUS
      <4> PICK wa \in WriterAssignment' : P = PV(wa)'
        BY DEF PA3
      <4>1. ASSUME NEW  i \in Nat, NEW q \in Proc,
                   ReadyToWrite(i, q)'
            PROVE  ReadyToWrite(i, q)
        <5> /\ pc'[q] = "d" => pc[q] = "d"
            /\ notKnown' = notKnown
          BY SMT DEF d, TypeOK
        <5> QED
          BY <4>1, SMT DEF ReadyToWrite
      <4>2. wa \in WriterAssignment
        BY <4>1, SMT DEF WriterAssignment
      <4>3. PICK j \in notKnown[p] : A3' = [A3 EXCEPT ![j] = known[p]]
        BY DEF d
      <4> j \in Nat
        BY DEF TypeOK 
      <4>4. CASE wa[j] # NotAProc
        <5>1. PV(wa)' = PV(wa)
          <6>1. SUFFICES ASSUME NEW i \in Nat
                         PROVE  PV(wa)'[i] = PV(wa)[i]
            BY DEF PV
          <6>2. CASE wa[i] # NotAProc 
            <7> known'[wa[i]] = known[wa[i]]
              BY DEF d
            <7> QED
              BY <6>2 DEF PV
          <6>3. CASE wa[i] = NotAProc
             <7> i # j
               BY <4>4, <6>3
             <7> A3'[i] = A3[i]
               BY <4>3, SMT DEF TypeOK
             <7> QED
               BY <6>3 DEF PV
          <6>4. QED
            BY <6>2, <6>3
        <5>2. QED
          BY <4>2, <5>1 DEF PA3
      <4>5. CASE wa[j] = NotAProc
        <5>1. ASSUME NEW i \in Nat 
              PROVE  wa[i] # p
          <6>1. ~ReadyToWrite(i, p)'
            BY SMT DEF d, ReadyToWrite, TypeOK
          <6>2. QED
            BY <6>1, SMT DEF WriterAssignment
        <5> DEFINE za == [wa EXCEPT ![j] = p]
        <5>2. za \in WriterAssignment
          <6>1. wa \in  [Nat -> Proc \cup {NotAProc}]
            BY <4>2 DEF WriterAssignment
          <6>2. za \in [Nat -> Proc \cup {NotAProc}]
            BY <6>1
          <6>3. ASSUME NEW i \in Nat, 
                       za[i] \in Proc
                PROVE  \A k \in Nat \ {i} : za[k] # za[i]
            <7> SUFFICES ASSUME NEW k \in Nat \ {i}
                         PROVE  za[k] # za[i]
              OBVIOUS
            <7>1. CASE k # j /\ i # j
              <8> za[k] = wa[k] /\ za[i] = wa[i]
                BY <7>1, <6>1
              <8> wa[i] \in Proc
                BY <6>3
              <8> wa[k] # wa[i]
                BY <4>2, SMT DEF WriterAssignment
              <8> QED
                BY SMT DEF WriterAssignment
                \** 2013-06-25 DEF WriterAssignment missing
            <7>2. CASE j \in {i, k}
              <8>1. PICK m \in {i, k} : m # j
                BY SMT
              <8> SUFFICES za[j] # za[m]
                BY <8>1, <7>2, SMT DEF WriterAssignment
                \** 2013-06-25 DEF WriterAssignment missing
              <8>2. za[j] = p /\ za[m] = wa[m]
                BY <6>1, <8>1
              <8> HIDE DEF za
              <8>3. QED
                BY <8>2, <5>1, SMT
            <7>3. QED
              BY <7>1, <7>2, SMT DEF WriterAssignment
              \** 2013-06-25 DEF WriterAssignment missing
          <6>4. ASSUME NEW i \in Nat 
                PROVE  WriterAssignment!(za)!(i)
            <7>1. CASE i # j
              <8>1. za[i] = wa[i]
                BY <7>1, <6>1
              <8>2. WriterAssignment!(wa)!(i)
                BY  <4>2, SMT DEF WriterAssignment
              <8> HIDE DEF za
              <8>3. QED
                BY <8>1, <8>2, <6>3
            <7>2. CASE i = j
              <8>1. ReadyToWrite(j, p)
                BY SMT DEF ReadyToWrite, d
              <8>2. za[j] = p
                BY <6>1
              <8> HIDE DEF za
              <8>3. QED
                BY <7>2, <8>1, <8>2, <6>2, <6>3 DEF WriterAssignment
            <7>3. QED
              BY <7>1, <7>2
          <6>5. QED
            BY <6>2, <6>4, SMT DEF WriterAssignment
        <5>3. PV(wa)' = PV(za)
          <6>1. wa = [k \in Nat |-> wa[k]]
              BY DEF WriterAssignment
          <6>2. SUFFICES ASSUME NEW i \in Nat
                         PROVE  PV(wa)'[i] = PV(za)[i]
            BY DEF PV
          <6>3. CASE wa[i] # NotAProc 
            <7>1. i # j
              BY <4>5, <6>3
            <7>2. known'[wa[i]] = known[wa[i]]
              BY <7>1 DEF d
            <7>3. PV(wa)'[i] = known'[wa[i]]
              BY <6>3, SMT DEF PV
            <7>4. za[i] = wa[i]
               BY <6>1, <7>1
            <7>5. PV(za)[i] = known[wa[i]]
              BY <7>4, <6>3 DEF PV  
            <7>6. QED
              BY <7>2, <7>3, <7>5
          <6>4. CASE wa[i] = NotAProc
             <7>1. CASE i # j
               <8> A3'[i] = A3[i]
                 BY <7>1, <4>3, SMT DEF TypeOK
               <8> wa[i] = za[i]
                 BY <6>1, <7>1
               <8> QED
                 BY <6>4 DEF PV
             <7>2. CASE i = j
               <8>1. PV(wa)'[j] = A3[j]'
                 BY <7>2, <6>4 DEF PV
               <8>2. za[j] = p
                 BY <6>1, <7>2
               <8>3. PV(za)[j] = known[p]
                  BY <8>2, NotAProcProp, SMT DEF PV, WriterAssignment
                  \** 2013-06-25 DEF WriterAssignment missing
               <8>4. A3'[j] = known[p]
                 BY <4>3, SMT DEF TypeOK
               <8> HIDE DEF za
               <8>5. QED
                 BY  <7>2, <8>1, <8>3, <8>4
             <7>3. QED
               BY <7>1, <7>2
           <6>5. QED
            BY <6>3, <6>4
        <5>4. QED
          BY <5>2, <5>3 DEF PA3
      <4>6. QED
        BY <4>4, <4>5
    <3>4. QED
      BY <3>1, <3>2, <3>3
  <2>9. ASSUME NEW p \in Proc, e(p)
        PROVE  Inv'
    <3> USE <2>9
    <3>1. TypeOK'
      <4>1. TypeOK!1'
        BY SMT DEF TypeOK, e
      <4>2. TypeOK!2'
        BY SMT DEF TypeOK, e
      <4>3. TypeOK!3'
        BY SMT DEF TypeOK, e
      <4>4. TypeOK!4'
        BY SMT DEF TypeOK, e
      <4>5. TypeOK!5'
        BY SMT DEF TypeOK, e
      <4>6. TypeOK!6'
        BY SMT DEF TypeOK, e
      <4>7. TypeOK!7'
        BY <2>2, SMT DEF TypeOK, e
      <4>8. TypeOK!8'
        BY SMT DEF TypeOK, e
      <4>9. TypeOK!9'
        BY SMT DEF TypeOK, e
      <4>10. TypeOK!10'
        BY SMT DEF TypeOK, e
      <4>11. TypeOK!11'
        BY SMT DEF TypeOK, e
      <4>12. QED
        BY <4>1, <4>2, <4>3, <4>4, <4>5, <4>6, 
           <4>7, <4>8, <4>9, <4>10, <4>11, SMT DEF TypeOK
    <3>2. Inv1'
      <4>1. ASSUME NEW q \in Proc
            PROVE  Inv1!1!(q)'
        <5>1. Inv1!1!(q)!1'
          BY SMT DEF Inv1, TypeOK, e
        <5>2. Inv1!1!(q)!2'
          BY SMT DEF Inv1, TypeOK, e
        <5>3. Inv1!1!(q)!3'
          BY SMT DEF Inv1, TypeOK, e
        <5>4. Inv1!1!(q)!4'
          BY SMT DEF Inv1, TypeOK, e
        <5>5. nbpart'[q] =< Cardinality(NUnion(A2'))
          <6> Cardinality(NUnion(A2')) = Cardinality(NUnion(A2))
            BY DEF e
          <6>1. CASE p = q
            BY <2>2, <6>1, SMT DEF Inv1, TypeOK, e
          <6>2. CASE p # q
            BY <2>2, <6>2, SMT DEF Inv1, TypeOK, e
          <6>3. QED 
            BY <6>1, <6>2
        <5>6. Inv1!1!(q)!6'
          BY SMT DEF Inv1, TypeOK, e
        <5>7. Inv1!1!(q)!7'
          BY SMT DEF Inv1, TypeOK, e
        <5>8. Inv1!1!(q)!8'
          BY SMT DEF Inv1, TypeOK, e
        <5>9. Inv1!1!(q)!9'
          BY SMT DEF Inv1, TypeOK, e
        <5>10. Inv1!1!(q)!10'
          BY SMT DEF Inv1, TypeOK, e
        <5>11. QED
          BY <5>1, <5>2, <5>3, <5>4, <5>5, <5>6, <5>7, <5>8, <5>9, <5>10,
            SMT DEF Inv1
      <4>2. NUnion(A3') \subseteq PUnion(myVals') 
        BY SMT DEF Inv1, TypeOK, e
      <4>3. Inv1!3'
        BY SMT DEF Inv1, TypeOK, e
      <4>4. QED
        BY <4>1, <4>2, <4>3 DEF Inv1
    <3>3. Inv2'
      (*********************************************************************)
      (* This proof copied from the proof of for b(p).                     *)
      (*********************************************************************)
      <4> SUFFICES PA3' = PA3
        BY DEF Inv2, e
      <4>1. WriterAssignment' = WriterAssignment
        <5>1. ASSUME NEW q \in Proc 
              PROVE  (pc[q] = "d") = (pc'[q]="d")
          <6>1. pc[q] = "d" => p # q
             BY DEF e
          <6>2. pc'[q] = "d" => p # q
            BY DEF e, TypeOK
          <6>3. p # q => pc'[q]= pc[q]
            BY DEF e, TypeOK
          <6>4. QED
            BY <6>1, <6>2, <6>3 
        <5>2. \A i \in Nat, q \in Proc : ReadyToWrite(i, q) = ReadyToWrite(i, q)'
          BY <5>1, SMT  DEF ReadyToWrite, e
        <5>3. QED
          BY <5>2, SMT DEF WriterAssignment
      <4>2. ASSUME NEW wa \in WriterAssignment
            PROVE  PV(wa) = PV(wa)'
        <5>1. A3' = A3 
          BY DEF e
        <5>2. ASSUME wa \in WriterAssignment, NEW i \in Nat, wa[i] # NotAProc 
              PROVE known'[wa[i]] = known[wa[i]]
          <6>1. wa[i] \in Proc
            BY <5>2, SMT DEF WriterAssignment
          <6>2. ReadyToWrite(i, wa[i])
            BY  <5>2, <6>1, SMT DEF WriterAssignment
          <6>3. pc[wa[i]] = "d"
            BY <6>2 DEF ReadyToWrite
          <6>4. wa[i] # p
            BY <6>3 DEF e
          <6>5. QED
            BY <6>4, SMT DEF TypeOK, e
        <5>3. ASSUME NEW i \in Nat, wa \in WriterAssignment 
              PROVE  (IF wa[i] = NotAProc THEN A3[i] ELSE known[wa[i]]) =
                               (IF wa[i] = NotAProc THEN A3'[i] ELSE known'[wa[i]])
          <6>1. CASE wa[i] = NotAProc
            BY <5>1, <5>2, <6>1
          <6>2. CASE wa[i] # NotAProc
            BY <5>1, <5>2, <6>2
          <6>3. QED
            BY <6>1, <6>2
        <5>4. QED
          BY <5>3 DEF PV
      <4>3. QED
        BY <4>2, <4>1 DEF PA3
    <3>4. QED
      BY <3>1, <3>2, <3>3
  <2>10. QED
    BY <2>4, <2>5, <2>6, <2>7, <2>8, <2>9 DEF Next
         
<1>3. QED
  (*************************************************************************)PROOF
  (* By <1>1, <1>2 and TLA reasoning.                                      *)
  (*************************************************************************)OMITTED
-----------------------------------------------------------------------------
(***************************************************************************)
(* We now prove that algorithm SnapShot implements/refines the             *)
(* specification BigSpec of module SnapSpec.                               *)
(***************************************************************************)
pcBar == [p \in Proc |-> 
            CASE pc[p] \in {"a", "b"} -> "A"
            []   pc[p] \in {"c", "d"} -> "B"
            []   pc[p] = "e" -> IF lnbpart[p] = Cardinality(NUnion(A2))
                                  THEN "C"
                                  ELSE "B" ]

LEMMA pcBarFcn == /\ pcBar = [i \in Proc |-> pcBar[i]]
                  /\ pcBar' = [i \in Proc |-> pcBar'[i]]
BY Isa DEF pcBar
          
S == INSTANCE SnapSpec WITH pc <- pcBar  

THEOREM Spec => S!BigSpec
<1> USE DEF ProcSet, S!ProcSet, Pr, S!Pr

<1>1. Init => S!Init
  <2> SUFFICES ASSUME Init
               PROVE  S!Init
    OBVIOUS
  <2>1. S!Init!1
    BY SMT DEF Init   
  <2>2. S!Init!2
    BY SMT DEF Init  
  <2>3. S!Init!3
    BY SMT DEF Init   
  <2>4. S!Init!4
    <3>1. NUnion(A2) = {}
      BY SMT DEF NUnion, Init
    <3>2. Cardinality({}) = 0
      BY EmptySetCardinality, SMT
    <3>3. QED
      BY <3>1, <3>2 DEF Init, pcBar
  <2>5. QED
    BY <2>1, <2>2, <2>3, <2>4, SMT DEF S!Init   

<1>2. Inv /\ Inv' /\ [Next]_vars => [S!BigNext]_S!vars
  <2>1. SUFFICES ASSUME Inv, Inv', [Next]_vars
               PROVE  [S!BigNext]_S!vars
    OBVIOUS
  (*************************************************************************)
  (* We want to use Inv' only when necessary.                              *)
  (*************************************************************************)
  <2> SUFFICES ASSUME Inv, [Next]_vars
               PROVE  [S!BigNext]_S!vars
    BY <2>1
  <2> USE Inv DEF Inv
  <2>2. ASSUME UNCHANGED vars
        PROVE  UNCHANGED S!vars
    <3> pcBar' = pcBar
      <4> A2' = A2 /\ pc' = pc /\ lnbpart = lnbpart'
        BY <2>2 DEF vars
      <4> QED
        BY Isa DEF pcBar
    <3> QED
      BY <2>2, SMT DEF vars, S!vars
  <2>3. ASSUME NEW p \in Proc, a(p)
        PROVE  [S!BigNext]_S!vars
    <3> USE <2>3 
    <3>1. CASE Cardinality(NUnion(A2')) =  Cardinality(NUnion(A2))
      <4> SUFFICES ASSUME NEW q \in Proc
                   PROVE  pcBar'[q] = pcBar[q]
        BY DEF pcBar, S!vars, a
      <4> QED
       BY <3>1 DEF a, TypeOK, pcBar
    <3>2. CASE  Cardinality(NUnion(A2')) #  Cardinality(NUnion(A2))
      <4>1. /\ Cardinality(NUnion(A2')) \in Nat
            /\ Cardinality(NUnion(A2)) \in Nat
        <5>1. /\ NUnion(A2) \in SUBSET Proc
              /\ NUnion(A2') \in SUBSET Proc
          BY Isa, <2>1, <2>1 DEF TypeOK, NUnion
        <5>2. QED
          BY <5>1, ProcFinite, SubsetFinite, CardType, SMT
      <4> SUFFICES S!BigNext!2!(p)
        BY DEF S!BigNext
      <4>2. Cardinality(NUnion(A2')) >  Cardinality(NUnion(A2))
        <5>1. Cardinality(NUnion(A2)) =< Cardinality(NUnion(A2')) 
          BY <2>1, A2monotonic, TypeOK', SMT
        <5>2. QED
          BY <5>1, <4>1, <3>2, SMT 
      <4>3. /\ pcBar[p] = "A"
            /\ pcBar'[p] = "A"
        BY DEF a, pcBar, TypeOK
      <4> DEFINE P == {q \in Proc \ {p} : pcBar[q] = "C"}
      <4>4. pcBar' = [q \in Proc |-> IF q \in P THEN "B" 
                                                ELSE pcBar[q]]
        <5>1. ASSUME NEW q \in P
              PROVE  pcBar'[q] = "B"
          <6>1. /\ pc[q] = "e"
                /\ lnbpart[q] = Cardinality(NUnion(A2))
            <7>1. /\ q \in Proc
                  /\ pcBar[q] = "C"
              OBVIOUS
            <7> HIDE DEF P
            <7>2. pc[q] \in {"a", "b", "c", "d", "e"}
              BY <7>1 DEF TypeOK
            <7>3. QED
              BY <7>1, <7>2 DEF pcBar
          <6>2. q # p
            BY <6>1 DEF a
          <6>3. /\ pc'[q] = pc[q]
                /\ lnbpart'[q] = lnbpart[q]
            BY DEF a, TypeOK
          <6>4. lnbpart'[q] # Cardinality(NUnion(A2'))
            BY <3>2, <6>1, <6>3
          <6>5. QED
            BY <6>1, <6>3, <6>4 DEF pcBar
        <5>2. ASSUME NEW q \in Proc, q \notin P
              PROVE  pcBar'[q] = pcBar[q]
          <6>1. CASE q = p
            BY <6>1, <4>3
          <6>2. CASE q # p
            <7>1. /\ pc'[q] = pc[q]
                  /\ lnbpart'[q] = lnbpart[q]
              BY <6>2 DEF a, TypeOK
            <7>2. CASE pc[q] \in {"a", "b", "c", "d"}
              BY <7>1, <7>2 DEF pcBar
            <7>3. CASE pc[q] = "e"
              <8>1. pcBar[q] # "C"
                BY <5>2, <6>2
              <8> HIDE DEF P
              <8>2. lnbpart[q] # Cardinality(NUnion(A2))
                BY <7>3, <8>1 DEF pcBar
              <8>3. lnbpart[q] < Cardinality(NUnion(A2))
                BY <8>2, <4>1, SMT DEF Inv1, TypeOK
              <8>4. lnbpart'[q] # Cardinality(NUnion(A2'))
                BY <8>3, <4>1, <4>2, <7>1, SMT DEF TypeOK
              <8>5. pcBar'[q] = "B"
                BY <7>1, <7>3, <8>4 DEF pcBar
              <8>6. pcBar[q] = "B"
                BY <7>3, <8>2 DEF pcBar
              <8>7. QED
                BY <8>5, <8>6
            <7>4. QED
              BY <7>2, <7>3 DEF TypeOK            
          <6>3. QED
            BY <6>1, <6>2
        <5>3. QED
         <6> pcBar' = [q \in Proc |-> pcBar'[q]]
           BY Isa DEF pcBar
         <6> HIDE DEF P
         <6> ASSUME NEW q \in Proc
             PROVE  pcBar'[q] = IF q \in P THEN "B" ELSE pcBar[q]
           BY <5>1, <5>2, SMT
         <6> QED
           OBVIOUS \* BY <5>1, <5>2, SMT
      <4>5. UNCHANGED << myVals, nextout,  out>>
        BY DEF a 
      <4>6. /\ P \in SUBSET (Proc \ {p})
            /\ \A q \in P : pcBar[q] = "C"
        OBVIOUS
      <4> HIDE DEF P
      <4>7. \E PP \in SUBSET (Proc \ {p}) :
                    /\ \A q \in PP : pcBar[q] = "C"
                    /\ pcBar' = [q \in Proc |-> IF q \in PP THEN "B" 
                                                            ELSE pcBar[q]]
                    /\ UNCHANGED << myVals, nextout,  out>>              
        BY <4>3, <4>4, <4>5, <4>6
      <4>8. QED
        BY <4>3, <4>7 \* , SMT
    <3>3. QED
      BY <3>1, <3>2
  <2>4. ASSUME NEW p \in Proc, b(p)
        PROVE  [S!Next]_S!vars
    <3> USE <2>4
    <3> SUFFICES S!A(p)
      BY DEF S!Next 
    <3>1. pcBar[p] = "A"
      BY DEF b, pcBar
    <3>2. pcBar' = [pcBar EXCEPT ![p] = "B"]
      <4> USE DEF pcBar
      <4>1. pcBar'[p] = "B"
        BY SMT DEF b, TypeOK
      <4>2. \A q \in Proc \ {p} : pcBar'[q] = pcBar[q]
        BY DEF b, pcBar, TypeOK
      <4>3.  pcBar' = [q \in Proc |-> pcBar'[q]]
        BY Isa DEF pcBar
      <4>4. pcBar = [q \in Proc |-> pcBar[q]]
        BY Isa DEF pcBar
      <4> HIDE DEF pcBar
      <4>5. QED
        BY <4>1, <4>2, <4>3, <4>4
    <3>3. \E v \in Val:
                myVals' = [myVals EXCEPT ![p] = myVals[p] \cup {v}]
      BY DEF b
    <3>4. UNCHANGED << out, nextout >>
      BY DEF b
    <3>5. QED
      BY <3>1, <3>2, <3>3, <3>4 DEF S!A
  <2>5. ASSUME NEW p \in Proc, c(p)
        PROVE  [S!Next]_S!vars
    <3> USE <2>5
    <3>1. A3 \in PA3
      <4> DEFINE wa == [i \in Nat |-> NotAProc]
      <4>1. wa \in WriterAssignment
        BY NotAProcProp, SMT DEF WriterAssignment
      <4>2. A3 = PV(wa)
        BY SMT DEF TypeOK, PV
      <4>3. QED
        BY <4>1, <4>2 DEF PA3
    <3>2. CASE notKnown'[p] # {}
      <4> SUFFICES UNCHANGED S!vars
        OBVIOUS
      <4>1. /\ pc[p] = "c"
            /\ lnbpart' = [lnbpart EXCEPT ![p] = nbpart[p]]
            /\ known' = [known EXCEPT ![p] = 
                           known[p] \cup UNION {A3[i] : i \in Nat}]
            /\ notKnown' = [notKnown EXCEPT ![p] = 
                             {i \in 0..(nbpart[p]-1) : 
                                 known'[p] # A3[i]}]
            /\ notKnown'[p] # {}
            /\ pc' = [pc EXCEPT ![p] = "d"]
            /\ UNCHANGED nextout
            /\ UNCHANGED << result, A2, A3, myVals, nbpart, out >>
         BY <3>2 DEF c, NUnion
      <4>2. UNCHANGED <<myVals, nextout, out>>
        BY <4>1
      <4>3. UNCHANGED pcBar 
        <5> pc[p] = "c" /\ pc'[p] = "d"
          BY <4>1 DEF TypeOK
        <5> pcBar'[p] = pcBar[p]
          BY DEF pcBar
        <5> \A q \in Proc \ {p} : pcBar'[q] = pcBar[q]
          BY <4>1, SMT DEF pcBar, TypeOK
        <5> QED
          BY DEF pcBar              
      <4>4. QED
        BY <4>2, <4>3 DEF S!vars
    <3>3. CASE /\ notKnown'[p] = {}
               /\ nbpart[p] = Cardinality(NUnion(A2))
      <4> SUFFICES S!B(p)
        BY DEF S!Next
      <4>1. /\ pc[p] = "c"
            /\ lnbpart' = [lnbpart EXCEPT ![p] = nbpart[p]]
            /\ known' = [known EXCEPT ![p] = 
                           known[p] \cup UNION {A3[i] : i \in Nat}]
            /\ notKnown' = [notKnown EXCEPT ![p] = 
                               {i \in 0..(nbpart[p]-1) : 
                                      known'[p] # A3[i]}]
            /\ notKnown'[p] = {}
            /\ nbpart[p] (* lnbpart'[p] *) = Cardinality(NUnion(A2))
            /\ nextout' = [nextout EXCEPT ![p] = known'[p]]
            /\ pc' = [pc EXCEPT ![p] = "e"]
            /\ UNCHANGED << result, A2, A3, myVals, nbpart, out >>
       <5>1. <4>1!1
          BY <3>3 DEF c
        <5>2. <4>1!2
          BY <3>3 DEF c
        <5>3. <4>1!3
          BY <3>3 DEF c, NUnion
        <5>4. <4>1!4
          BY <3>3 DEF c
        <5>5. <4>1!5
          BY <3>3 DEF c
        <5>6. <4>1!6
          BY <3>3 DEF c
        <5>7. <4>1!7
          BY <3>3 DEF c
        <5>8. <4>1!8
          BY <3>3 DEF c
        <5>9. <4>1!9
          BY <3>3 DEF c
        <5>10. QED
          BY <5>1, <5>2, <5>3, <5>4, <5>5, <5>6, <5>7, <5>8, <5>9 
      <4>2./\ NUnion(A3) \subseteq nextout'[p]
           /\ \A i \in 0..(nbpart[p]-1) : nextout'[p] = A3[i]
        <5> USE DEF NUnion
        <5>1. {i \in 0..(nbpart[p]-1) : known'[p] # A3[i]} = {}
          BY <4>1 DEF TypeOK
        <5>2. \A i \in 0..(nbpart[p]-1) : known'[p] = A3[i]
          BY <5>1
        <5>3. known'[p] = known[p] \cup UNION {A3[i] : i \in Nat}
          BY <4>1 DEF TypeOK
        <5>4. nextout'[p] = known'[p]
          BY <4>1 DEF TypeOK
        <5>5. QED
          BY <5>4, <5>3, <5>2
      <4>3. PUnion(nextout) \subseteq nextout'[p]
        <5>1. SUFFICES ASSUME NEW q \in Proc
                     PROVE  nextout[q] \subseteq nextout'[p]
          BY DEF PUnion
        <5>2. nextout[q] \subseteq NUnion(A3)
          BY <3>1, SMT DEF Inv2
        <5>3. QED
          BY <4>2, <5>2
      <4>4. pcBar[p] = "B"
        BY <4>1, SMT DEF pcBar
      <4>5. \E V \in {W \in SUBSET S!PUnion(myVals) :
                          /\ myVals[p] \subseteq W
                          /\ S!PUnion(nextout) \subseteq W }:
                 nextout' = [nextout EXCEPT ![p] = V]
         <5> DEFINE V == nextout'[p]
         <5>1. V \in SUBSET S!PUnion(myVals)
           <6> /\ V \subseteq known'[p]
               /\ known'[p] \subseteq PUnion(myVals')
             BY <2>1, SMT DEF Inv1, TypeOK \* , S!PUnion, PUnion
           <6> myVals' = myVals
             BY <4>1
           <6> PUnion(myVals') = S!PUnion(myVals')
             BY DEF S!PUnion, PUnion
           <6> QED
             BY SMT
         <5>2. myVals'[p] \subseteq V
           <6> myVals'[p] \subseteq known'[p]
             BY <2>1, SMT DEF Inv1
           <6> /\ myVals' = myVals
               /\ V = known'[p]
             BY <4>1, SMT DEF TypeOK
           <6> QED
             OBVIOUS
         <5>3. S!PUnion(nextout) \subseteq V
           BY <4>3 DEF PUnion, S!PUnion
         <5>4. V \in <4>5!1
           BY <4>1, <5>1, <5>2, <5>3, SMT DEF TypeOK
           \** 2013-06-25 DEF TypeOK missing
         <5>5. nextout' = [nextout EXCEPT ![p] = V]
           BY Isa, <4>1
         <5>6. QED
           BY <5>4, <5>5
      <4>6. pcBar' = [pcBar EXCEPT ![p] = "C"]
        <5> pcBar'[p] = "C"
          BY <4>1, SMT DEF pcBar, TypeOK
        <5> \A q \in Proc \ {p} : pcBar'[q] = pcBar[q]
          BY <4>1 DEF pcBar, TypeOK
        <5> QED
          BY pcBarFcn
      <4>7. UNCHANGED << myVals, out >>
        BY <4>1
      <4>8. QED
        BY <4>4, <4>5, <4>6, <4>7 DEF S!B
    <3>4. CASE /\ notKnown'[p] = {}
               /\ nbpart[p] # Cardinality(NUnion(A2))
      <4> SUFFICES UNCHANGED S!vars
        OBVIOUS
      <4>1. /\ pc[p] = "c"
            /\ lnbpart' = [lnbpart EXCEPT ![p] = nbpart[p]]
            /\ known' = [known EXCEPT ![p] = 
                           known[p] \cup UNION {A3[i] : i \in Nat}]
            /\ notKnown' = [notKnown EXCEPT ![p] = 
                              {i \in 0..(nbpart[p]-1) : 
                                   known'[p] # A3[i]}]
            /\ notKnown'[p] = {}
            /\ nbpart[p] # Cardinality(NUnion(A2))
            /\ UNCHANGED nextout
            /\ pc' = [pc EXCEPT ![p] = "e"]
            /\ UNCHANGED << result, A2, A3, myVals, nbpart, out >>
        BY <3>4 DEF c, NUnion
      <4>2. UNCHANGED <<myVals, nextout, out>>
        BY <4>1
      <4>3. UNCHANGED pcBar 
        <5> pc[p] = "c" /\ pc'[p] = "e" /\ lnbpart'[p] # Cardinality(NUnion(A2'))
          BY <4>1 DEF TypeOK
        <5> pcBar'[p] = pcBar[p]
          BY DEF pcBar
        <5> \A q \in Proc \ {p} : pcBar'[q] = pcBar[q]
          BY <4>1 DEF pcBar, TypeOK
        <5> QED
          BY DEF pcBar              
      <4>4. QED
        BY <4>2, <4>3 DEF S!vars
     <3>5. QED
       BY <3>2, <3>3, <3>4
  <2>6. ASSUME NEW p \in Proc, d(p)
        PROVE  [S!Next]_S!vars
    <3> USE <2>6
    <3> SUFFICES UNCHANGED S!vars
      OBVIOUS
    <3>1. pcBar' = pcBar
      <4> pcBar[p] = "B"
        BY DEF d, pcBar
      <4> pcBar'[p] = "B"
        BY DEF d, pcBar, TypeOK
      <4> \A q \in Proc \ {p} : pcBar'[q] = pcBar[q]
        BY DEF d, pcBar, TypeOK
      <4> QED
        BY pcBarFcn
    <3>2. QED
      BY <3>1 DEF d, S!vars
  <2>7. ASSUME NEW p \in Proc, e(p)
        PROVE  [S!Next]_S!vars
    <3> USE <2>7
    <3>1. CASE lnbpart[p] = nbpart'[p]     
      <4>1. /\ lnbpart[p] = nbpart'[p]
            /\ pc[p] = "e"
            /\ nbpart' = [nbpart EXCEPT ![p] = Cardinality(NUnion(A2))]
            /\ out' = [out EXCEPT ![p] = known[p]]
            /\ pc' = [pc EXCEPT ![p] = "b"]
            /\ UNCHANGED << result, A2, A3, myVals, known, notKnown, lnbpart, 
                            nextout >>
        BY <3>1 DEF e
      <4>2. nbpart[p] = Cardinality(NUnion(A2))
        <5>1. lnbpart[p] = Cardinality(NUnion(A2))
          BY <4>1, SMT DEF TypeOK
        <5>2. /\ lnbpart[p] =< nbpart[p]
              /\ nbpart[p] =< Cardinality(NUnion(A2))
          BY <4>1 DEF Inv1
        <5>3. lnbpart[p] \in Nat /\ nbpart[p] \in Nat
          BY SMT DEF TypeOK
        <5>4. QED
          BY <5>1, <5>2, <5>3, SMT
      <4>3. nextout[p] = known[p]
        BY <4>1, <4>2, SMT DEF Inv1
      <4>4. pcBar[p] = "C" /\ pcBar'[p] = "A"
        BY <4>1 DEF pcBar, TypeOK 
      <4>5. pcBar' = [pcBar EXCEPT ![p] = "A"]
        <5> \A q \in Proc \ {p} : pcBar'[q] = pcBar[q]
          BY <4>1 DEF pcBar, TypeOK
        <5> /\ pcBar = [q \in Proc |-> pcBar[q]]
            /\ pcBar' = [q \in Proc |-> pcBar'[q]]
          BY Isa DEF pcBar        
        <5> QED
          BY <4>4
      <4>6. S!C(p)
        BY <4>3, <4>4, <4>5, <4>1, SMT DEF S!C
      <4>7. QED
        BY <4>6 DEF S!Next
    <3>2. CASE lnbpart[p] # nbpart'[p]
      <4>1. /\ lnbpart[p] # nbpart'[p]
            /\ pc[p] = "e"
            /\ nbpart' = [nbpart EXCEPT ![p] = Cardinality(NUnion(A2))]
            /\ pc' = [pc EXCEPT ![p] = "c"]
            /\ out' = out
            /\ UNCHANGED << result, A2, A3, myVals, known, notKnown, lnbpart, 
                            nextout >>
        BY <3>2 DEF e
      <4>2. lnbpart[p] # Cardinality(NUnion(A2))
        BY <4>1, SMT DEF TypeOK
      <4>3. pcBar[p] = "B" /\ pcBar'[p] = "B"
        BY <4>1, <4>2, SMT DEF TypeOK, pcBar
      <4>4. pcBar' = pcBar
        <5> \A q \in Proc \ {p} : pcBar'[q] = pcBar[q]
          BY <4>1 DEF pcBar, TypeOK
        <5> /\ pcBar = [q \in Proc |-> pcBar[q]]
            /\ pcBar' = [q \in Proc |-> pcBar'[q]]
          BY Isa DEF pcBar        
        <5> QED
          BY <4>3
      <4>5. QED
        BY <4>1, <4>4 DEF S!vars
    <3>3. QED
     BY <3>1, <3>2
  <2>8. QED
    <3> S!Next => S!BigNext
      BY DEF S!BigNext
    <3> QED
      BY <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, SMT DEF Next, Pr

<1>3. QED
  (*************************************************************************)PROOF
  (* BY <1>1, <1>2, Invariance and TLA reasoning.                          *)
  (*************************************************************************)OMITTED
=============================================================================
\* Modification History
\* Last modified Tue Apr 14 16:42:06 CEST 2020 by doligez
\* Last modified Tue Jun 25 15:13:49 CEST 2013 by hernanv
\* Last modified Sat Jun 01 10:16:42 CEST 2013 by merz
\* Last modified Sat Jun 01 10:16:24 CEST 2013 by merz
\* Last modified Fri May 31 09:38:40 PDT 2013 by lamport
\* Last modified Wed Jul 04 18:46:31 CEST 2012 by cd
\* Last modified Wed Jul 04 16:49:18 CEST 2012 by hf
\* Created Wed Jul 04 11:46:40 CEST 2012 by cd
