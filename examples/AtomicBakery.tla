------------ MODULE AtomicBakery ----------------------------
(***************************************************************************)
(* The Atomic Bakery algorithm is a version of the bakery algorithm in     *)
(* which reading and writing of a process's number is an atomic operation. *)
(* The bakery algorithm originally appeared in:                            *)
(*                                                                         *)
(*   Leslie Lamport                                                        *)
(*   A New Solution of Dijkstra's Concurrent Programming Problem           *)
(*   Communications of the ACM 17, 8   (August 1974), 453-455              *)
(*                                                                         *)
(* This PlusCal version of the Atomic Bakery algorithm is one in which     *)
(* variables whose initial values are not used are initialized to          *)
(* arbitrary type-correct values.  It is good for proving correctness but  *)
(* not for model checking, because it produces an unnecessarily large      *)
(* number of reachable states.  If the variables were left uninitialized,  *)
(* the PlusCal translation would initialize them to a particular           *)
(* unspecified value.  This would complicate the proof because it would    *)
(* make the type-correctness invariant more complicated, but it would be   *)
(* efficient to model check.  We could write a version that is both easy   *)
(* to prove and efficient to model check by initializing the variables to  *)
(* particular type-correct values.                                         *)
(***************************************************************************)
EXTENDS Naturals, TLAPS

(***************************************************************************)
(* We first declare N to be the number of processes, and we assume that N  *)
(* is a natural number.                                                    *)
(***************************************************************************)
CONSTANT N 
ASSUME N \in Nat

(***************************************************************************)
(* We define P to be the set {1, 2, ...  , N} of processes.                *)
(***************************************************************************)
P == 1..N 

(***       this is a comment containing the PlusCal code ***

--algorithm AtomicBakery {
variable num = [i \in P |-> 0], flag = [i \in P |-> FALSE];

(***************************************************************************)
(* The following defines LL(j, i) to be true iff <<num[j], j>> is less     *)
(* than or equal to <<num[i], i>> in the usual lexicographical ordering.   *)
(***************************************************************************)
define { LL(j, i) == \/ num[j] < num[i]
                     \/ /\ num[i] = num[j]
                        /\ j =< i
       }

process (p \in P)
  variables unread \in SUBSET P, 
            max \in Nat, 
            nxt \in P;
{
p1: while (TRUE) {
      unread := P \ {self} ;
      max := 0;
      flag[self] := TRUE;
p2:   while (unread # {}) {
        with (i \in unread) { unread := unread \ {i};
                              if (num[i] > max) { max := num[i]; }
         }
       };
p3:   num[self] := max + 1;
p4:   flag[self] := FALSE;
      unread := P \ {self} ;
p5:   while (unread # {}) {
        with (i \in unread) { nxt := i ; };
        await ~ flag[nxt];
p6:     await \/ num[nxt] = 0
              \/ LL(self, nxt) ;
        unread := unread \ {nxt};
        } ;
cs:   skip ;  \* the critical section;
p7:   num[self] := 0;
 }}
}
****     this ends the comment containg the pluscal code      **********)

\* BEGIN TRANSLATION  (this begins the translation of the PlusCal code)
VARIABLES num, flag, pc

(* define statement *)
LL(j, i) == \/ num[j] < num[i]
            \/ /\ num[i] = num[j]
               /\ j =< i

VARIABLES unread, max, nxt

vars == << num, flag, pc, unread, max, nxt >>

ProcSet == (P)

Init == (* Global variables *)
        /\ num = [i \in P |-> 0]
        /\ flag = [i \in P |-> FALSE]
        (* Process p *)
        /\ unread \in [P -> SUBSET P]
        /\ max \in [P -> Nat]
        /\ nxt \in [P -> P]
        /\ pc = [self \in ProcSet |-> "p1"]

p1(self) == /\ pc[self] = "p1"
            /\ unread' = [unread EXCEPT ![self] = P \ {self}]
            /\ max' = [max EXCEPT ![self] = 0]
            /\ flag' = [flag EXCEPT ![self] = TRUE]
            /\ pc' = [pc EXCEPT ![self] = "p2"]
            /\ UNCHANGED << num, nxt >>

p2(self) == /\ pc[self] = "p2"
            /\ IF unread[self] # {}
                  THEN /\ \E i \in unread[self]:
                            /\ unread' = [unread EXCEPT ![self] = unread[self] \ {i}]
                            /\ IF num[i] > max[self]
                                  THEN /\ max' = [max EXCEPT ![self] = num[i]]
                                  ELSE /\ TRUE
                                       /\ max' = max
                       /\ pc' = [pc EXCEPT ![self] = "p2"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "p3"]
                       /\ UNCHANGED << unread, max >>
            /\ UNCHANGED << num, flag, nxt >>

p3(self) == /\ pc[self] = "p3"
            /\ num' = [num EXCEPT ![self] = max[self] + 1]
            /\ pc' = [pc EXCEPT ![self] = "p4"]
            /\ UNCHANGED << flag, unread, max, nxt >>

p4(self) == /\ pc[self] = "p4"
            /\ flag' = [flag EXCEPT ![self] = FALSE]
            /\ unread' = [unread EXCEPT ![self] = P \ {self}]
            /\ pc' = [pc EXCEPT ![self] = "p5"]
            /\ UNCHANGED << num, max, nxt >>

p5(self) == /\ pc[self] = "p5"
            /\ IF unread[self] # {}
                  THEN /\ \E i \in unread[self]:
                            nxt' = [nxt EXCEPT ![self] = i]
                       /\ ~ flag[nxt'[self]]
                       /\ pc' = [pc EXCEPT ![self] = "p6"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "cs"]
                       /\ nxt' = nxt
            /\ UNCHANGED << num, flag, unread, max >>

p6(self) == /\ pc[self] = "p6"
            /\ \/ num[nxt[self]] = 0
               \/ LL(self, nxt[self])
            /\ unread' = [unread EXCEPT ![self] = unread[self] \ {nxt[self]}]
            /\ pc' = [pc EXCEPT ![self] = "p5"]
            /\ UNCHANGED << num, flag, max, nxt >>

cs(self) == /\ pc[self] = "cs"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "p7"]
            /\ UNCHANGED << num, flag, unread, max, nxt >>

p7(self) == /\ pc[self] = "p7"
            /\ num' = [num EXCEPT ![self] = 0]
            /\ pc' = [pc EXCEPT ![self] = "p1"]
            /\ UNCHANGED << flag, unread, max, nxt >>

p(self) == p1(self) \/ p2(self) \/ p3(self) \/ p4(self) \/ p5(self)
              \/ p6(self) \/ cs(self) \/ p7(self)

Next == (\E self \in P: p(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION   (this ends the translation of the PlusCal code)

(***************************************************************************)
(* MutualExclusion asserts that two distinct processes are in their        *)
(* critical sections.                                                      *)
(***************************************************************************)
MutualExclusion == \A i,j \in P : (i # j) => ~ /\ pc[i] = "cs"
                                               /\ pc[j] = "cs"
-----------------------------------------------------------------------------
(***************************************************************************)
(* The Inductive Invariant                                                 *)
(*                                                                         *)
(* TypeOK is the type-correctness invariant.                               *)
(***************************************************************************)

TypeOK == /\ num \in [P -> Nat]
          /\ flag \in [P -> BOOLEAN]
          /\ unread \in [P -> SUBSET P]
          /\ \A i \in P :
                pc[i] \in {"p2", "p5", "p6"} => i \notin unread[i]
          /\ max \in [P -> Nat]
          /\ nxt \in [P -> P]
          /\ \A i \in P : (pc[i] = "p6") => nxt[i] # i
          /\ pc \in
              [P -> {"p1", "p2", "p3", "p4", "p5", "p6", "cs", "p7"}]


(***************************************************************************)
(* After(i, j) is a condition that implies that num[j] > 0 and, if i is    *)
(* trying to enter its critical section and j does not change num[j], then *)
(* i either has or will choose a value of num[i] for which LL(j, i) is     *)
(* true.                                                                   *)
(***************************************************************************)
After(i, j) == /\ num[j] > 0
               /\ \/ pc[i] = "p1"
                  \/ /\ pc[i] = "p2"
                     /\ \/ j \in unread[i]
                        \/ max[i] >= num[j]
                  \/ /\ pc[i] = "p3"
                     /\ max[i] >= num[j]
                  \/ /\ pc[i] \in {"p4", "p5", "p6"}
                     /\ LL(j,i)
                     /\ (pc[i] \in {"p5", "p6"}) => (j \in unread[i])

(***************************************************************************)
(* IInv(i) is the part of the inductive invariant that ensures that when i *)
(* is in its critical section, no other process is.                        *)
(***************************************************************************)
IInv(i) ==
  /\ (num[i] = 0) <=> (pc[i] \in {"p1", "p2", "p3"})
  /\ flag[i] <=> (pc[i] \in {"p2", "p3", "p4"})
  /\ (pc[i] \in {"p5", "p6"}) =>
        \A j \in (P \ unread[i]) \ {i} : After(j, i)
  /\ /\ (pc[i] = "p6")
     /\ \/ (pc[nxt[i]] = "p2") /\ (i \notin unread[nxt[i]])
        \/ pc[nxt[i]] = "p3"
     => max[nxt[i]] >= num[i]
  /\ (pc[i] \in {"cs", "p7"}) => \A j \in P \ {i} : After(j, i)

(***************************************************************************)
(* Inv is the complete inductive invariant.                                *)
(***************************************************************************)  
Inv == TypeOK /\ \A i \in P : IInv(i)
-----------------------------------------------------------------------------
(***************************************************************************)
(* Proof of Mutual Exclusion                                               *)
(*                                                                         *)
(* This is a standard invariance proof, where <1>2 asserts that any step   *)
(* of the algorithm (including a stuttering step) starting in a state in   *)
(* which Inv is true leaves Inv true.  Step <1>4 follows easily from       *)
(* <1>1-<1>3 by simple temporal reasoning.                                 *)
(***************************************************************************)
THEOREM Spec => []Inv
<1> USE DEFS TypeOK, Inv, IInv, ProcSet
<1>1. Init => Inv
  BY DEFS Init, Inv
<1>2. Inv /\ [Next]_vars => Inv'
  <2> SUFFICES ASSUME Inv, [Next]_vars PROVE Inv'
    OBVIOUS
  <2> USE DEFS After, LL
  <2>1. ASSUME NEW self \in P, p1(self) PROVE Inv'
    BY <2>1 DEF p1
  <2>2. ASSUME NEW self \in P, p2(self) PROVE Inv'
    <3>1. CASE unread[self] = {}
      BY <2>2, <3>1 DEF p2
    <3>2. CASE unread[self] # {}
      BY <2>2, <3>2 DEF p2
    <3>3. QED
      BY <3>1, <3>2    
  <2>3. ASSUME NEW self \in P, p3(self) PROVE Inv'
    BY <2>3 DEF p3
  <2>4. ASSUME NEW self \in P, p4(self) PROVE Inv'
    BY <2>4 DEF p4
  <2>5. ASSUME NEW self \in P, p5(self) PROVE Inv'
    <3>1. CASE unread[self] = {}
      BY <2>5, <3>1 DEF p5
    <3>2. CASE unread[self] # {}
      BY <2>5, <3>2, CVC4T(30) DEF p5
    <3>3. QED
      BY <3>1, <3>2
  <2>6. ASSUME NEW self \in P, p6(self) PROVE Inv'
    <3>p. P \subseteq Nat
      BY N \in Nat DEF P
    <3>1. CASE num[nxt[self]] = 0
      BY <2>6, <3>1 DEF p6
    <3>2. CASE LL(self, nxt[self])
      BY <2>6, <3>2, <3>p DEF p6
    <3>3. QED
      BY <2>6, <3>1, <3>2 DEF p6
  <2>7. ASSUME NEW self \in P, cs(self) PROVE Inv'
    BY <2>7 DEF cs
  <2>8. ASSUME NEW self \in P, p7(self) PROVE Inv'
    BY <2>8 DEF p7
  <2>9. CASE UNCHANGED vars
    BY <2>9 DEF vars
  <2>10. QED
    BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9 DEF Next, p
<1>3. Inv => MutualExclusion
  BY DEFS Inv, After, MutualExclusion 
<1>4. QED
  BY <1>1, <1>2, <1>3, PTL DEF Spec
=============================================================================

