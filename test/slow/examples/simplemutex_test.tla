----------------------------- MODULE simplemutex_test ------------------------
EXTENDS Integers, TLAPS

(***********

(***************************************************************************)
(* The following algorithm is an important mutual exclusion protocol.      *)
(* This protocol is at the heart of many mutual exclusion algorithms.  It  *)
(* is a two-process protocol that guarantees that both processes cannot    *)
(* execute statement cs.  (However, they can both deadlock.)               *)
(***************************************************************************)
--algorithm Mutex {
  variable trying = [i \in {0,1} |-> FALSE]

  process (p \in {0,1}) {
a:   trying[self] := TRUE ;
b:   await ~trying[1 - self];
cs:  skip  \* the critical section
   }
}

***********)

\* BEGIN TRANSLATION
VARIABLES trying, pc

vars == << trying, pc >>

ProcSet == ({0,1})

Init == (* Global variables *)
        /\ trying = [i \in {0,1} |-> FALSE]
        /\ pc = [self \in ProcSet |-> CASE self \in {0,1} -> "a"]

a(self) == /\ pc[self] = "a"
           /\ trying' = [trying EXCEPT ![self] = TRUE]
           /\ pc' = [pc EXCEPT ![self] = "b"]

b(self) == /\ pc[self] = "b"
           /\ ~trying[1 - self]
           /\ pc' = [pc EXCEPT ![self] = "cs"]
           /\ UNCHANGED trying

cs(self) == /\ pc[self] = "cs"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "Done"]
            /\ UNCHANGED trying

p(self) == a(self) \/ b(self) \/ cs(self)

Next == (\E self \in {0,1}: p(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

TypeOK ==
  /\ trying \in [{0,1} -> BOOLEAN]
  /\ pc \in [{0,1} -> {"a", "b", "cs", "Done"}]

Inv == \A i \in {0,1} :
          /\ pc[i] \in {"b", "cs"} => trying[i]
          /\ pc[i] = "cs" => pc[1-i] # "cs"


IndInvSpec == (TypeOK /\ Inv) /\ [][Next]_vars
   (************************************************************************)
   (* TypeOK /\ Inv is an inductive invariant Spec iff it is an invariant  *)
   (* of IndInvSpec.  TLC can be used to check what we are about to prove. *)
   (************************************************************************)


(***************************************************************************)
(* The following theorem asserts that TypeOK /\ Inv is true in the initial *)
(* state.                                                                  *)
(***************************************************************************)
THEOREM Initialization == Init => TypeOK /\ Inv
  BY DEF Init, TypeOK, Inv, ProcSet

MutualExclusion == ~(pc[0] = "cs" /\ pc[1] = "cs")

(***************************************************************************)
(* The following theorem asserts that our invariant implies mutual         *)
(* exclusion.                                                              *)
(***************************************************************************)
THEOREM Mutex == Inv => MutualExclusion
<1>1. 1-0 = 1 /\ 1-1 = 0
  BY SimpleArithmetic
<1>2. QED
  BY <1>1 DEF Inv, MutualExclusion
THEOREM TRUE OBVIOUS \* This put in for the tla-mode macros

(***************************************************************************)
(* The following theorem asserts that if a step (a pair of states)         *)
(* satisfies the formula Next, and TypeOK /\ Inv is true in the first      *)
(* state, then TypeOK /\ Inv is true in the second state.                  *)
(***************************************************************************)
THEOREM Invariance == TypeOK /\ Inv /\ Next => TypeOK' /\ Inv'
<1>1. CASE UNCHANGED vars
  BY <1>1 DEF TypeOK, Inv, Next, ProcSet, p, vars
<1>2. ASSUME TypeOK, Inv,
             NEW i \in {0,1},
             a(i) \/ b(i) \/ cs(i)
      PROVE  TypeOK'
    BY <1>2, Auto DEF TypeOK, Inv, a, b, cs
<1>3. ASSUME TypeOK, TypeOK', Inv,
             NEW i \in {0,1},
             a(i) \/ b(i) \/ cs(i),
             NEW j \in {0,1},
             Inv!(i) /\ Inv!(j)
      PROVE  Inv!(j)'
  <2>1. /\ 1-i \in {0, 1}
        /\ 1-j \in {0, 1}
        /\ i # j => /\ 1-i = j
                    /\ 1-j = i
    BY SimpleArithmetic
  <2>2. USE DEF TypeOK, Inv
  <2>3. CASE a(i)
     BY <2>1, <1>3, <2>3 DEF a
  <2>4. CASE b(i)
    <3>1. CASE i = j
      BY <2>1, <1>3, <2>4, <3>1 DEF b
    <3>2. CASE i # j
       BY <2>1, <1>3, <2>4, <3>2 DEF b
    <3>3. QED
      BY <3>1, <3>2
  <2>5. CASE cs(i)
      BY <2>1, <2>5, <1>3 DEF cs
  <2>6. QED
     BY <2>3, <2>4, <2>5, <1>3
<1>4. QED
  BY <1>1, <1>2, <1>3 DEF Next, p, ProcSet, Inv
----------------------------------------------------------------------
(***************************************************************************)
(* The following is a trivial consequence of the Invariance theorem, the   *)
(* definition of [Next]_vars, and the fact that UNCHANGED vars implies     *)
(* that none of the declared variables changes.                            *)
(***************************************************************************)
THEOREM TLAInvariance == TypeOK /\ Inv /\ [Next]_vars => TypeOK' /\ Inv'
BY Invariance DEF TypeOK, Inv, Next, ProcSet, p, vars
-----------------------------------------------------------------------------
(***************************************************************************)
(* The prover now handles just enough temporal logic to prove the main     *)
(* theorem.                                                                *)
(***************************************************************************)
THEOREM Init /\ [][Next]_vars => []MutualExclusion
OMITTED
(*BY Initialization, TLAInvariance, Mutex, Inv1*)
=============================================================================
