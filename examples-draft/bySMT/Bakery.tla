----------------------------- MODULE Bakery ---------------------------------
(***************************************************************************)
(* This is a PlusCal description of the bakery algorithm from:             *)
(*                                                                         *)
(*   Leslie Lamport                                                        *)
(*   A New Solution of Dijkstra's Concurrent Programming Problem           *)
(*   Communications of the ACM 17, 8   (August 1974), 453-455              *)
(*                                                                         *)
(* and a TLAPS checked proof that it implements mutual exclusion.          *)
(*                                                                         *)
(* The bakery algorithm is remarkable because it does not assume atomic    *)
(* operations to shared registers.  More precisely, it assumes what are    *)
(* called multi-reader safe registers in:                                  *)
(*                                                                         *)
(*   Leslie Lamport                                                        *)
(*   On Interprocess Communication--Part I: Basic Formalism,               *)
(*   Part II: Algorithms                                                   *)
(*   Distributed Computing 1, 2 (1986), 77-101.                            *)
(*                                                                         *)
(* Such a register can be written by one process and satisfies only the    *)
(* requirement that a read that does not overlap a write obtains the       *)
(* current value of the register.  As I believe the article points out, it *)
(* is trivial to implement multi-reader safe registers from single-reader  *)
(* ones.  Also, one can trivially assume that the reader always obtains a  *)
(* value of the correct type.                                              *)
(*                                                                         *)
(* A theorem (possibly unpublished) states that one can model a safe       *)
(* register by one in which a read is atomic but a write is performed by   *)
(* atomically writing an arbitrary sequence of (type-correct) values       *)
(* followed by the correct value.  In the bakery algorithm, the shared     *)
(* registers are the array elements num[i] and flag[i], which are written  *)
(* only by process i.                                                      *)
(*                                                                         *)
(* This PlusCal version of the algorithm allows the process-local          *)
(* variables, whose initial values are not used, to be initialized to      *)
(* arbitrary type-correct values.  This is a more general specification    *)
(* than one that initializes those variables to particular values, as      *)
(* would be the case in the PlusCal code did not specify any initial       *)
(* value.  Initializing the variables to type-correct values simplifies    *)
(* the proof, but allowing them to have any type-correct initial values is *)
(* not good for model checking, because it produces an unnecessarily large *)
(* number of reachable states.  We could write a version that is both easy *)
(* to prove and efficient to model check by initializing the variables to  *)
(* particular type-correct values.  However, the nondeterminism in the     *)
(* modeling of safe registers makes model checking infeasible.             *)
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

(***************************************************************************)
(* The following declares num and flag to be arrays indexed by P,          *)
(* initialized with num[i] = 0 and flag[i] = FALSE for all processes i     *)
(* in P.                                                                   *)
(***************************************************************************)
variable num = [i \in P |-> 0], flag = [i \in P |-> FALSE];

(***************************************************************************)
(* The following defines LL(j, i) to be true iff <<num[j], j>> is less     *)
(* than or equal to <<num[i], i>> in the usual lexicographical ordering.   *)
(***************************************************************************)
define { LL(j, i) == \/ num[j] < num[i]
                     \/ /\ num[i] = num[j]
                        /\ j =< i
       }

(***************************************************************************)
(* The following process declaration describes the code for all processes  *)
(* in P, where self is the current process.                                *)
(***************************************************************************)
process (p \in P)
  variables unread \in SUBSET P, 
            max \in Nat, 
            nxt \in P;
{
p1: while (TRUE) {
      unread := P \ {self} ;
      max := 0;
      with (repeat \in BOOLEAN) { 
        if (repeat) { flag[self] := ~ flag[self];
                      goto p1 }
        else { flag[self] := TRUE } 
        } ;
p2:   while (unread # {}) {
        with (i \in unread) { unread := unread \ {i};
                              if (num[i] > max) { max := num[i]; }
                            }
       } ;
p3:   with (repeat \in BOOLEAN, k \in Nat) {
         if (repeat) { num[self] := k ;
                       goto p3 }
         else { with (i \in {j \in Nat : j > max}) {num[self] := i } } ;
       } ;
p4:   unread := P \ {self} ;
      with (repeat \in BOOLEAN) { 
        if (repeat) { flag[self] := ~ flag[self];
                      goto p4 }
        else  { flag[self] := FALSE } 
       } ;
p5:   while (unread # {}) {
        with (i \in unread) { nxt := i ; };
        await ~ flag[nxt];
p6:     await \/ num[nxt] = 0
              \/ LL(self, nxt) ;
        unread := unread \ {nxt};
        } ;
cs:   skip ;    \* the critical section;
p7:   with (repeat \in BOOLEAN, k \in Nat) {
         if (repeat) { num[self] := k ;
                       goto p7 }
         else { num[self] := 0 } 
       } 
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
            /\ \E repeat \in BOOLEAN:
                 IF repeat
                    THEN /\ flag' = [flag EXCEPT ![self] = ~ flag[self]]
                         /\ pc' = [pc EXCEPT ![self] = "p1"]
                    ELSE /\ flag' = [flag EXCEPT ![self] = TRUE]
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
            /\ \E repeat \in BOOLEAN:
                 \E k \in Nat:
                   IF repeat
                      THEN /\ num' = [num EXCEPT ![self] = k]
                           /\ pc' = [pc EXCEPT ![self] = "p3"]
                      ELSE /\ \E i \in {j \in Nat : j > max[self]}:
                                num' = [num EXCEPT ![self] = i]
                           /\ pc' = [pc EXCEPT ![self] = "p4"]
            /\ UNCHANGED << flag, unread, max, nxt >>

p4(self) == /\ pc[self] = "p4"
            /\ unread' = [unread EXCEPT ![self] = P \ {self}]
            /\ \E repeat \in BOOLEAN:
                 IF repeat
                    THEN /\ flag' = [flag EXCEPT ![self] = ~ flag[self]]
                         /\ pc' = [pc EXCEPT ![self] = "p4"]
                    ELSE /\ flag' = [flag EXCEPT ![self] = FALSE]
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
            /\ \E repeat \in BOOLEAN:
                 \E k \in Nat:
                   IF repeat
                      THEN /\ num' = [num EXCEPT ![self] = k]
                           /\ pc' = [pc EXCEPT ![self] = "p7"]
                      ELSE /\ num' = [num EXCEPT ![self] = 0]
                           /\ pc' = [pc EXCEPT ![self] = "p1"]
            /\ UNCHANGED << flag, unread, max, nxt >>

p(self) == p1(self) \/ p2(self) \/ p3(self) \/ p4(self) \/ p5(self)
              \/ p6(self) \/ cs(self) \/ p7(self)

Next == (\E self \in P: p(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION  (this ends the translation of the PlusCal code)

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
After(i, j) ==  /\ num[j] > 0
                /\ \/ pc[i] = "p1"
                   \/ /\ pc[i] = "p2"
                      /\ \/ j \in unread[i]
                         \/ max[i] >= num[j]
                   \/ /\ pc[i] = "p3"
                      /\ max[i] >= num[j]
                   \/ /\ pc[i] \in {"p4", "p5", "p6"}
                      /\ LL(j,i)
                      /\ (pc[i] \in {"p5", "p6"}) => (j \in unread[i])
                   \/ pc[i] = "p7"

(***************************************************************************)
(* IInv(i) is the part of the inductive invariant that ensures that when i *)
(* is in its critical section, no other process is.                        *)
(***************************************************************************)
IInv(i) ==
  /\ /\ (pc[i] \in {"p1", "p2"}) => (num[i] = 0) 
     /\  (num[i] = 0) => (pc[i] \in {"p1", "p2", "p3", "p7"})
  /\ /\ flag[i] => (pc[i] \in {"p1", "p2", "p3", "p4"})
     /\ (pc[i] \in {"p2", "p3"}) => flag[i] 
  /\ (pc[i] \in {"p5", "p6"}) =>
        \A j \in (P \ unread[i]) \ {i} : After(j, i)
  /\ /\ (pc[i] = "p6")
     /\ \/ (pc[nxt[i]] = "p2") /\ (i \notin unread[nxt[i]])
        \/ pc[nxt[i]] = "p3"
     => max[nxt[i]] >= num[i]
  /\ (pc[i] = "cs") => \A j \in P \ {i} : After(j, i)


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
(* <1>1-<1>3 by simple temporal reasoning, but TLAPS does not yet do any   *)
(* temporal reasoning.                                                     *)
(***************************************************************************)
THEOREM Spec => []MutualExclusion
<1> USE N \in Nat DEFS P, Inv, IInv, TypeOK, After, LL, ProcSet 
<1>1. Init => Inv
  BY SMT DEF Init
<1>2. Inv /\ [Next]_vars => Inv'
  BY SMTT(40) DEF Next, p, p1, p2, p3, p4, p5, p6, cs, p7, vars
<1>3. Inv => MutualExclusion
  BY SMT DEFS MutualExclusion 
<1>4. QED
  PROOF OMITTED
=============================================================================
