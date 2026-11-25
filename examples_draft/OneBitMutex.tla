---------------------------- MODULE OneBitMutex ----------------------------
(***************************************************************************)
(* N-process One-Bit Algorithm.  TLC Model_3.                              *)
(*   Checking Mutex & DeadlockFree on SVC-LAMPORT-6 takes:                 *)
(*      N = 3:  3 sec                                                      *)
(*      N = 4:  (2 workers, 23 min on SVC-LAMPORT-2)                       *)
(*                                                                         *)
(* Checked inductive invariance of Inv and LiveInv on SVC-LAMPORT-6 with   *)
(* N=2 in 1 sec.  For N=3, need to handle about 57M initial states.        *)
(***************************************************************************)
EXTENDS Naturals, TLAPS

CONSTANT N
ASSUME NAssump == N \in Nat

Procs == 1..N

(***************************************************************************
--algorithm OneBitMutex
    { variable x = [i \in Procs |-> FALSE];
       fair process (p \in Procs)
         variables unchecked = {};
                   other \in Procs ; \*  = CHOOSE i \in Procs \ {self} : TRUE;
         { ncs:- while (TRUE)
                  { e1: x[self] := TRUE ;
                        unchecked := Procs \ {self};
                    e2: while (unchecked # {})
                          { with (i \in unchecked)
                               { other := i;
                                 unchecked := unchecked \ {i};
                                } ;
                            if (x[other])
                              { if (self > other)
                                  { e3: x[self] := FALSE;
                                    e4: await ~x[other];
                                        goto e1;
                                   }
                                 else { e5: await ~x[other]; }
                                }  ;
                          } ;
                    cs: skip;
                    f:  x[self] := FALSE
                  }
         }
    }


****************************************************************************)
\* BEGIN TRANSLATION
VARIABLES x, pc, unchecked, other

vars == << x, pc, unchecked, other >>

ProcSet == (Procs)

Init == (* Global variables *)
        /\ x = [i \in Procs |-> FALSE]
        (* Process p *)
        /\ unchecked = [self \in Procs |-> {}]
        /\ other \in [Procs -> Procs]
        /\ pc = [self \in ProcSet |-> "ncs"]

ncs(self) == /\ pc[self] = "ncs"
             /\ pc' = [pc EXCEPT ![self] = "e1"]
             /\ UNCHANGED << x, unchecked, other >>

e1(self) == /\ pc[self] = "e1"
            /\ x' = [x EXCEPT ![self] = TRUE]
            /\ unchecked' = [unchecked EXCEPT ![self] = Procs \ {self}]
            /\ pc' = [pc EXCEPT ![self] = "e2"]
            /\ other' = other

e2(self) == /\ pc[self] = "e2"
            /\ IF unchecked[self] # {}
                  THEN /\ \E i \in unchecked[self]:
                            /\ other' = [other EXCEPT ![self] = i]
                            /\ unchecked' = [unchecked EXCEPT ![self] = unchecked[self] \ {i}]
                       /\ IF x[other'[self]]
                             THEN /\ IF self > other'[self]
                                        THEN /\ pc' = [pc EXCEPT ![self] = "e3"]
                                        ELSE /\ pc' = [pc EXCEPT ![self] = "e5"]
                             ELSE /\ pc' = [pc EXCEPT ![self] = "e2"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "cs"]
                       /\ UNCHANGED << unchecked, other >>
            /\ x' = x

e3(self) == /\ pc[self] = "e3"
            /\ x' = [x EXCEPT ![self] = FALSE]
            /\ pc' = [pc EXCEPT ![self] = "e4"]
            /\ UNCHANGED << unchecked, other >>

e4(self) == /\ pc[self] = "e4"
            /\ ~x[other[self]]
            /\ pc' = [pc EXCEPT ![self] = "e1"]
            /\ UNCHANGED << x, unchecked, other >>

e5(self) == /\ pc[self] = "e5"
            /\ ~x[other[self]]
            /\ pc' = [pc EXCEPT ![self] = "e2"]
            /\ UNCHANGED << x, unchecked, other >>

cs(self) == /\ pc[self] = "cs"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "f"]
            /\ UNCHANGED << x, unchecked, other >>

f(self) == /\ pc[self] = "f"
           /\ x' = [x EXCEPT ![self] = FALSE]
           /\ pc' = [pc EXCEPT ![self] = "ncs"]
           /\ UNCHANGED << unchecked, other >>

p(self) == ncs(self) \/ e1(self) \/ e2(self) \/ e3(self) \/ e4(self)
              \/ e5(self) \/ cs(self) \/ f(self)

Next == (\E self \in Procs: p(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Procs : WF_vars((pc[self] # "ncs") /\ p(self))

\* END TRANSLATION
TypeOK == /\ pc \in [Procs -> {"ncs", "e1", "e2", "e3", "e4", "e5", "cs", "f"}]
          /\ x \in [Procs -> BOOLEAN]
          /\ other \in [Procs -> Procs]
          /\ unchecked \in [Procs -> SUBSET Procs]

Past(i, j) == \/ (pc[i] = "e2") /\ (j \notin unchecked[i])
              \/ (pc[i] = "e5") /\ (j \notin unchecked[i] \cup {other[i]})
              \/ pc[i] = "cs"


Inv == \A i \in Procs :
          /\ (pc[i] \in {"e2", "e5", "cs"}) => x[i]
          /\ \A j \in Procs \ {i} :
                Past(i, j) => ~Past(j, i) /\ x[i]

LiveInv == \A i \in Procs : (pc[i] = "e4") => ~x[i]

Trying(i) == pc[i] \in {"e1", "e2", "e3", "e4", "e5"}
InCS(i) == pc[i] = "cs"

Mutex == \A i, j \in Procs : (i # j) => ~(InCS(i) /\ InCS(j))

DeadlockFree == (\E i \in Procs : Trying(i)) ~> (\E i \in Procs : InCS(i))
StarvationFree == \A i \in Procs : Trying(i) ~> InCS(i)

-----------------------------------------------------------------------------

THEOREM TypeCorrect == Spec => []TypeOK
<1>. USE NAssump DEF Procs, ProcSet
<1>1. Init => TypeOK 
  BY DEF Init, TypeOK 
<1>2. TypeOK /\ [Next]_vars => TypeOK'
  <2>. SUFFICES ASSUME TypeOK, [Next]_vars PROVE TypeOK'
    OBVIOUS 
  <2>. USE DEF TypeOK
  <2>1. ASSUME NEW self \in Procs, ncs(self) PROVE TypeOK'
    BY <2>1 DEF ncs 
  <2>2. ASSUME NEW self \in Procs, e1(self) PROVE TypeOK'
    BY <2>2 DEF e1 
  <2>3. ASSUME NEW self \in Procs, e2(self) PROVE TypeOK'
    BY <2>3 DEF e2
  <2>4. ASSUME NEW self \in Procs, e3(self) PROVE TypeOK'
    BY <2>4 DEF e3 
  <2>5. ASSUME NEW self \in Procs, e4(self) PROVE TypeOK'
    BY <2>5 DEF e4 
  <2>6. ASSUME NEW self \in Procs, e5(self) PROVE TypeOK'
    BY <2>6 DEF e5 
  <2>7. ASSUME NEW self \in Procs, cs(self) PROVE TypeOK'
    BY <2>7 DEF cs
  <2>8. ASSUME NEW self \in Procs, f(self) PROVE TypeOK'
    BY <2>8 DEF f 
  <2>9. CASE UNCHANGED vars 
    BY <2>9 DEF vars 
  <2>. QED  BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9 DEF Next, p
<1>. QED  BY <1>1, <1>2, PTL DEF Spec

THEOREM Invariant == Spec => []Inv
<1>. USE NAssump DEFS Procs, ProcSet, Past
<1>1. Init => Inv
  BY DEF Init, Inv
<1>2. Inv /\ TypeOK /\ [Next]_vars => Inv'
  <2>. SUFFICES ASSUME Inv, TypeOK, [Next]_vars PROVE Inv'
    OBVIOUS 
  <2>. USE DEF TypeOK, Inv
  <2>1. ASSUME NEW self \in Procs, ncs(self) PROVE Inv'
    BY <2>1 DEF ncs
  <2>2. ASSUME NEW self \in Procs, e1(self) PROVE Inv'
    BY <2>2 DEF e1 
  <2>3. ASSUME NEW self \in Procs, e2(self) PROVE Inv'
    BY <2>3 DEF e2 
  <2>4. ASSUME NEW self \in Procs, e3(self) PROVE Inv'
    BY <2>4 DEF e3 
  <2>5. ASSUME NEW self \in Procs, e4(self) PROVE Inv'
    BY <2>5 DEF e4 
  <2>6. ASSUME NEW self \in Procs, e5(self) PROVE Inv'
    BY <2>6 DEF e5 
  <2>7. ASSUME NEW self \in Procs, cs(self) PROVE Inv'
    BY <2>7 DEF cs 
  <2>8. ASSUME NEW self \in Procs, f(self) PROVE Inv'
    BY <2>8 DEF f 
  <2>9. CASE UNCHANGED vars 
    BY <2>9 DEF vars 
  <2>. QED  BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9 DEF Next, p
<1>3. QED  BY <1>1, <1>2, TypeCorrect, PTL DEF Spec 

THEOREM MutualExclusion == Spec => []Mutex 
<1>. TypeOK /\ Inv => Mutex 
  BY DEF TypeOK, Inv, Past, Mutex, InCS 
<1>. QED  BY TypeCorrect, Invariant, PTL 

=============================================================================
\* Created Sat Mar 31 14:32:32 PDT 2012 by lamport
