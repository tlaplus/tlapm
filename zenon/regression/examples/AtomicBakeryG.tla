\* THIS DIFFERS FROM THE REAL AtomicBakery BECAUSE
\*  - A (1-arm) CASE removed

------------ MODULE AtomicBakeryG ----------------------------
EXTENDS Naturals
(******
 The following doesn't work yet because ".." has not yet been defined
 over the integers.

 CONSTANT N \* The number of processors
 ASSUME N \in Nat
 P == 1..N \* The set of processors
******)
CONSTANT P
ASSUME PsubsetNat == P \subseteq Nat

(*********************************************************************
--algorithm AtomicBakery {
variable num = [i \in P |-> 0], flag = [i \in P |-> FALSE];

process (p \in P)
  variables unread, max, nxt {
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
              \/ IF self > nxt THEN num[nxt] > num[self]
                               ELSE num[nxt] \geq num[self];
        unread := unread \ {nxt};
        } ;
p7:   skip ; \* critical section;
p8:  num[self] := 0;
 }}
}
*********************************************************************)

\* BEGIN TRANSLATION
CONSTANT defaultInitValue
VARIABLES num, flag, pc, unread, max, nxt

vars == << num, flag, pc, unread, max, nxt >>

ProcSet == (P)

Init == (* Global variables *)
        /\ num = [i \in P |-> 0]
        /\ flag = [i \in P |-> FALSE]
        (* Process p *)
        /\ unread = [self \in P |-> defaultInitValue]
        /\ max = [self \in P |-> defaultInitValue]
        /\ nxt = [self \in P |-> defaultInitValue]
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
                            /\ unread' = [unread EXCEPT
                                            ![self] = unread[self] \ {i}]
                            /\ IF num[i] > max[self]
                                  THEN /\ max' = [max EXCEPT
                                                    ![self] = num[i]]
                                  ELSE /\ TRUE
                                       /\ UNCHANGED max
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
                            nxt' = [nxt EXCEPT
                                      ![self] = i]
                       /\ ~ flag[nxt'[self]]
                       /\ pc' = [pc EXCEPT ![self] = "p6"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "p7"]
                       /\ UNCHANGED nxt
            /\ UNCHANGED << num, flag, unread, max >>

p6(self) == /\ pc[self] = "p6"
            /\ \/ num[nxt[self]] = 0
               \/ IF self > nxt[self] THEN num[nxt[self]] > num[self]
                                      ELSE num[nxt[self]] >= num[self]
            /\ unread' = [unread EXCEPT ![self] = unread[self] \ {nxt[self]}]
            /\ pc' = [pc EXCEPT ![self] = "p5"]
            /\ UNCHANGED << num, flag, max, nxt >>

p7(self) == /\ pc[self] = "p7"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "p8"]
            /\ UNCHANGED << num, flag, unread, max, nxt >>

p8(self) == /\ pc[self] = "p8"
            /\ num' = [num EXCEPT ![self] = 0]
            /\ pc' = [pc EXCEPT ![self] = "p1"]
            /\ UNCHANGED << flag, unread, max, nxt >>

p(self) == p1(self) \/ p2(self) \/ p3(self) \/ p4(self) \/ p5(self)
              \/ p6(self) \/ p7(self) \/ p8(self)

Next == (\E self \in P: p(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

MutualExclusion == \A i,j \in P : (i # j) => ~ /\ pc[i] = "p7"
                                               /\ pc[j] = "p7"

-----------------------------------------------------------------------------
TypeOK == /\ num  \in [P -> Nat]
          /\ flag \in [P -> BOOLEAN]
          /\ unread \in [P -> (SUBSET P) \cup {defaultInitValue}]
          /\ \A i \in P :
                pc[i] \in {"p2", "p5", "p6"} => /\ unread[i] \subseteq P
                                                /\ i \notin unread[i]
          /\ max \in [P -> Nat \cup {defaultInitValue}]
          /\ \A j \in P : (pc[j] \in {"p2", "p3"}) => (max[j] \in Nat)
          /\ nxt \in [P -> P \cup {defaultInitValue}]
          /\ \A i \in P : (pc[i] = "p6") => nxt[i] \in P \ {i}
          /\ pc \in
              [P -> {"p1", "p2", "p3", "p4", "p5", "p6", "p7", "p8"}]

GG(j, i) == IF j > i THEN num[i] > num[j]
                     ELSE num[i] >= num[j]

After(i, j) ==  /\ num[j] > 0
                /\ \/ pc[i] = "p1"
                   \/ /\ pc[i] = "p2"
                      /\ \/ j \in unread[i]
                         \/ max[i] >= num[j]
                   \/ /\ pc[i] = "p3"
                      /\ max[i] >= num[j]
                   \/ /\ pc[i] \in {"p4", "p5", "p6"}
                      /\ GG(j,i)
                      /\ (pc[i] \in {"p5", "p6"}) => (j \in unread[i])

IInv(i) ==
  /\ (num[i] = 0) <=> (pc[i] \in {"p1", "p2", "p3"})
  /\ flag[i] <=> (pc[i] \in {"p2", "p3", "p4"})
  /\ (pc[i] \in {"p5", "p6"}) =>
        \A j \in (P \ unread[i]) \ {i} : After(j, i)
  /\ /\ (pc[i] = "p6")
     /\ \/ (pc[nxt[i]] = "p2") /\ (i \notin unread[nxt[i]])
        \/ pc[nxt[i]] = "p3"
     => max[nxt[i]] >= num[i]
  /\ (pc[i] \in {"p7", "p8"}) => \A j \in P \ {i} : After(j, i)
Inv == TypeOK /\ \A i \in P : IInv(i)
-----------------------------------------------------------------------------

THEOREM GTAxiom  == \A n, m \in Nat : ~ (n > m /\ m > n)
  OBVIOUS (*{ by (isabelle "(auto dest: nat_less_trans)") }*)

THEOREM GEQAxiom == \A n, m \in Nat : (n = m) \/ n > m \/ m > n
  OBVIOUS (*{ by (isabelle "(auto elim: nat_less_cases)") }*)

THEOREM GEQTransitive == \A n, m, q \in Nat : n >= m /\ m >= q => n >= q
  OBVIOUS (*{ by (isabelle "(auto dest: nat_leq_trans)") }*)

THEOREM Transitivity2 == \A n, m, q \in Nat : n > m /\ m >= q => n > q
  OBVIOUS (*{ by (isabelle "(auto dest: nat_leq_less_trans)") }*)

THEOREM GEQorLT == \A n, m \in Nat : n >= m <=> ~(m > n)
  OBVIOUS (*{ by (isabelle "(auto simp: nat_not_less dest: nat_leq_less_trans)") }*)

THEOREM NatGEQZero == \A n \in Nat: (n > 0) <=> (n # 0)
  OBVIOUS (*{ by (isabelle "(auto simp: nat_gt0_not0)") }*)

THEOREM GGIrreflexive == ASSUME NEW i \in P,
                                NEW j \in P,
                                i # j,
                                num[i] \in Nat,
                                num[j] \in Nat
                         PROVE  ~ (GG(i, j) /\ GG(j, i))
<1>. /\ i \in Nat /\ j \in Nat /\ i # j
     /\ num[i] \in Nat /\ num[j] \in Nat
  BY PsubsetNat
<1>1. CASE j > i
  <2>1. ~(i > j)
    BY <1>1, GTAxiom
  <2>3. QED
    BY <1>1, <2>1, GTAxiom, GEQorLT DEF GG
<1>2. CASE i > j
  <2>1. ~(j > i)
    BY <1>2, GTAxiom
  <2>3. QED
    BY <1>2, <2>1, GTAxiom, GEQorLT DEF GG
<1>3. QED
  BY <1>1, <1>2, i#j, GEQAxiom

(************************************************************************)
(* The following Isabelle proof method first does extensive equality    *)
(* substitution and some "obvious" first-order reasoning, avoiding case *)
(* splits. If there is something left to prove it then applies the      *)
(* standard "auto" tactic to solve the proof obligation. Preprocessing  *)
(* using "clarsimp" is beneficial when there are many equalities in the *)
(* assumptions -- typically, when reasoning about actions.              *)
(************************************************************************)
AXIOM SimplifyAndSolve == TRUE
(*{ by (isabelle "clarsimp auto?") }*)

-----------------------------------------------------------------------------
THEOREM InitImpliesTypeOK == Init => TypeOK
  <1> ASSUME Init PROVE TypeOK
    BY DEF Init, TypeOK, ProcSet
  <1> QED OBVIOUS

THEOREM TypeOKInvariant ==
        ASSUME TypeOK,
               Next
        PROVE  TypeOK'
<1>1. SUFFICES ASSUME NEW self \in P,
                      p(self)
               PROVE  TypeOK'
  BY <1>1 DEF Next, TypeOK, vars

<1>2. USE DEF TypeOK

<1>3. CASE p1(self)
  BY <1>3, SimplifyAndSolve DEF p1

<1>4. CASE p2(self)
  <2>0. USE DEF p2
  <2>1. /\ unread[self] \subseteq P
        /\ self \notin unread[self]
        /\ max[self] \in Nat
    BY <1>4
  <2>2. ASSUME NEW j \in P
        PROVE  /\ unread' \in [P -> (SUBSET P) \cup {defaultInitValue}]
               /\ pc' \in
                    [P -> {"p1", "p2", "p3", "p4", "p5", "p6", "p7", "p8"}]
               /\ pc'[j] \in {"p2", "p5", "p6"} => /\ unread'[j] \subseteq P
                                                   /\ j \notin unread'[j]
               /\ max' \in [P -> Nat \cup {defaultInitValue}]
               /\ (pc'[j] \in {"p2", "p3"}) => (max'[j] \in Nat)
               /\ (pc'[j] = "p6") => nxt'[j] \in P \ {j}
    <3>1. CASE unread[self] = {}
      BY <1>4, <3>1, SimplifyAndSolve
    <3>2. CASE unread[self] # {}
      <4>1. PICK k \in unread[self] :
                      /\ pc[self] = "p2"
                      /\ unread' = [unread EXCEPT
                                          ![self] = unread[self] \ {k}]
                      /\ IF num[k] > max[self]
                                THEN /\ max' = [max EXCEPT
                                                  ![self] = num[k]]
                                ELSE /\ TRUE
                                     /\ max' = max
                      /\ pc' = [pc EXCEPT ![self] = "p2"]
                      /\ num' = num /\ flag' = flag /\ nxt' = nxt 
        BY <1>4, <3>2
      <4>2 CASE j = self
        BY <2>1, <4>1, <4>2, SimplifyAndSolve
      <4>3 CASE j # self
        BY <2>1, <4>1, <4>3, SimplifyAndSolve
      <4>4. QED
        BY <4>2, <4>3
     <3>3. QED
      BY <3>1, <3>2
  <2>3. /\ max' \in [P -> Nat \cup {defaultInitValue}]
        /\ unread' \in [P -> (SUBSET P) \cup {defaultInitValue}]
        /\ pc' \in [P -> {"p1", "p2", "p3", "p4", "p5", "p6", "p7", "p8"}]
        /\ \A j \in P :
              pc'[j] \in {"p2", "p5", "p6"} => /\ unread'[j] \subseteq P
                                               /\ j \notin unread'[j]
        /\ \A j \in P : (pc'[j] \in {"p2", "p3"}) => (max'[j] \in Nat)
        /\ \A j \in P : (pc'[j] = "p6") => nxt'[j] \in P \ {j}
   BY <2>2
  <2>4. /\ num'  \in [P -> Nat]
        /\ flag' \in [P -> BOOLEAN]
        /\ nxt' \in [P -> P \cup {defaultInitValue}]
   BY <1>4
  <2>5. QED
     BY <2>3, <2>4

<1>5. CASE p3(self)
  BY <1>5, SimplifyAndSolve DEF p3

<1>6. CASE p4(self)
  BY <1>6, SimplifyAndSolve DEF p4

<1>7. CASE p5(self)
  <2>1. USE DEF p5
  <2>2. CASE unread[self] = {}
    BY <1>7, <2>2, SimplifyAndSolve
  <2>3. CASE unread[self] # {}
    BY <1>7, <2>3, SimplifyAndSolve
  <2>4. QED
    BY <2>2, <2>3

<1>8. CASE p6(self)
  (** "SimplifyAndSolve" handles this case but we can speed up things
      by removing the guard of the action, which doesn't contribute
      to type correctness and induces a needless case split. **)
  <2>1. /\ pc[self] = "p6"
        /\ unread' = [unread EXCEPT ![self] = unread[self] \ {nxt[self]}]
        /\ pc' = [pc EXCEPT ![self] = "p5"]
        /\ UNCHANGED << num, flag, max, nxt >>
    BY <1>8 DEF p6
  <2>2. QED 
    BY <2>1, SimplifyAndSolve

<1>9. CASE p7(self)
  BY <1>9, SimplifyAndSolve DEF p7

<1>10. CASE p8(self)
  BY <1>10, SimplifyAndSolve DEF p8

<1>11. QED
  BY p(self), <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>10 DEF p

THEOREM Init => Inv
<1>1. SUFFICES ASSUME Init,
                      NEW i \in P
               PROVE  IInv(i)
  BY InitImpliesTypeOK DEF Inv
<1>2. QED
  BY <1>1 DEF Init, ProcSet, IInv


THEOREM Inv => MutualExclusion
<1>1. SUFFICES ASSUME Inv,
                      NEW i \in P,
                      NEW j \in P,
                      i # j,
                      pc[i] = "p7",
                      pc[j] = "p7"
               PROVE  FALSE
  BY <1>1 DEF MutualExclusion
<1>2. IInv(i) /\ IInv(j)
  BY Inv DEF Inv
<1>3. After(i, j)
  BY <1>1, <1>2 DEF IInv
<1>99. QED
  BY pc[i]="p7", <1>3 DEF After


(***************************************************************************)
(* The following lemma asserts that the predicate After(i,j) is preserved  *)
(* if none of the state components change in terms of which it is defined. *)
(***************************************************************************)
THEOREM AfterPrime == 
  ASSUME NEW i, NEW j,
         After(i,j),
         UNCHANGED <<num[i], num[j], pc[i], unread[i], max[i]>>
  PROVE  After(i, j)'
  BY DEF After, GG


THEOREM Inv /\ Next => Inv'
(***************************************************************************)
(* Proof of the invariance theorem for the Bakery algorithm.               *)
(* It is about 600 lines long (down from 1400 for the original version)    *)
(* and takes about 6 minutes to process on Stephan's laptop (down from     *)
(* about 40 minutes on Leslie's laptop for the original version).          *)
(***************************************************************************)
<1>. SUFFICES ASSUME NEW i \in P,
                     NEW self \in P,
                     TypeOK,
                     Inv,
                     IInv(i),
                     p(self) \/ UNCHANGED vars
              PROVE  IInv(i)'
  BY TypeOKInvariant DEF Inv, Next

<1>. USE DEF TypeOK, IInv

<1>1. CASE p1(self)
 <2>1. USE <1>1 DEF p1
 <2>2. /\ (num'[i] = 0) <=> (pc'[i] \in {"p1", "p2", "p3"})
       /\ flag'[i] <=> (pc'[i] \in {"p2", "p3", "p4"})
   OBVIOUS
 <2>3. /\ (pc'[i] \in {"p5", "p6"}) => \A j \in (P \ unread'[i]) \ {i} : After(j, i)'
       /\ (pc'[i] \in {"p7", "p8"}) => \A j \in P \ {i} : After(j, i)'
   <3>. SUFFICES ASSUME NEW j \in P,
                        \/ /\ pc'[i] \in {"p5", "p6"}
                           /\ j \in (P \ unread'[i]) \ {i}
                        \/ /\ pc'[i] \in {"p7", "p8"}
                           /\ j \in P \ {i}
                 PROVE  After(j,i)'
      OBVIOUS
   <3>. i # self  (** since pc'[self] = "p2" **)
     OBVIOUS
   <3>1. CASE j = self
     <4>0. USE <3>1
     <4>1. num'[i] > 0
        BY NatGEQZero
     <4>2. /\ pc'[j] = "p2"
           /\ i \in unread'[j]
       BY SimplifyAndSolve
     <4>3. QED
       BY <4>1, <4>2 DEF After
   <3>2. CASE j # self
     <4>0. USE <3>2
     <4>1. After(j,i)
       OBVIOUS
     <4>2. UNCHANGED <<num[j], num[i], pc[j], unread[j], max[j]>>
       BY SimplifyAndSolve
     <4>3. QED
       BY <4>1, <4>2, AfterPrime
   <3>3. QED
     BY <3>1, <3>2
 <2>4. /\ (pc'[i] = "p6")
       /\ \/ (pc'[nxt'[i]] = "p2") /\ (i \notin unread'[nxt'[i]])
          \/ pc'[nxt'[i]] = "p3"
       => max'[nxt'[i]] >= num'[i]
   OBVIOUS
 <2>5. QED
   BY <2>2, <2>3, <2>4 DEF IInv

   (************************************************************************)
   (* SM: I split the "p2" case into two subcases, following the action    *)
   (* definition, because they are sensibly different.                     *)
   (* This proof takes the PM & Isabelle 12 min 11 sec on SVC-LAMPORT-5.   *)
   (* Down to 56 sec on Stephan's laptop (for <1>2a and <1>2b).            *)
   (************************************************************************)
<1>2a. CASE p2(self) /\ unread[self] = {}
      (* simplified description of the action helps Zenon to find some proofs *)
 <2>. /\ pc[self] = "p2" /\ unread[self] = {}
      /\ pc' = [pc EXCEPT ![self] = "p3"]
      /\ UNCHANGED << unread, max, num, flag, nxt >>
   BY <1>2a DEF p2
 <2>1. /\ (num'[i] = 0) <=> (pc'[i] \in {"p1", "p2", "p3"})
       /\ flag'[i] <=> (pc'[i] \in {"p2", "p3", "p4"})
   OBVIOUS
 <2>2. /\ (pc'[i] \in {"p5", "p6"}) => \A j \in (P \ unread'[i]) \ {i} : After(j, i)'
       /\ (pc'[i] \in {"p7", "p8"}) => \A j \in P \ {i} : After(j, i)'
   <3>. SUFFICES ASSUME NEW j \in P,
                        \/ /\ pc'[i] \in {"p5", "p6"}
                           /\ j \in (P \ unread'[i]) \ {i}
                        \/ /\ pc'[i] \in {"p7", "p8"}
                           /\ j \in P \ {i}
                 PROVE  After(j,i)'
      OBVIOUS
   <3>. i # self
     OBVIOUS
   <3>. After(j,i)
     OBVIOUS
   <3>1. CASE j = self
     <4>0. USE <3>1
     <4>1. max[j] >= num[i]
       BY DEF After
     <4>2. QED
       BY <4>1, SimplifyAndSolve DEF After
   <3>2. CASE j # self
     <4>0. USE <3>2
     <4>1. UNCHANGED << num[j], num[i], pc[j], unread[j], max[j] >>
       OBVIOUS
     <4>2. QED
       BY <4>1, AfterPrime
   <3>4. QED
     BY <3>1, <3>2
 <2>3. /\ (pc'[i] = "p6")
       /\ \/ (pc'[nxt'[i]] = "p2") /\ (i \notin unread'[nxt'[i]])
          \/ pc'[nxt'[i]] = "p3"
       => max'[nxt'[i]] >= num'[i]
   OBVIOUS
 <2>4. QED
   BY <2>1, <2>2, <2>3 DEF IInv

<1>2b. CASE p2(self) /\ unread[self] # {}
 <2>.  PICK k \in unread[self]:
              /\ pc[self] = "p2"
              /\ unread' = [unread EXCEPT
                              ![self] = unread[self] \ {k}]
              /\ IF num[k] > max[self]
                        THEN max' = [max EXCEPT ![self] = num[k]]
                        ELSE max' = max
              /\ pc' = [pc EXCEPT ![self] = "p2"]
              /\ UNCHANGED <<num, flag, nxt>>
   BY <1>2b DEF p2
 <2>. k \in P
   OBVIOUS
 <2>1. /\ (num'[i] = 0) <=> (pc'[i] \in {"p1", "p2", "p3"})
       /\ flag'[i] <=> (pc'[i] \in {"p2", "p3", "p4"})
   OBVIOUS
 (* The following three assertions are useful for steps <2>5 and <2>6. *)
 <2>2. /\ max[self] \in Nat /\ max'[self] \in Nat /\ num[k] \in Nat
       /\ max'[self] >= max[self]
       /\ max'[self] >= num[k]
   <3>.  max[self] \in Nat /\ num[k] \in Nat
     OBVIOUS
   <3>1. CASE num[k] > max[self]
     BY <3>1, SimplifyAndSolve
   <3>2. CASE ~(num[k] > max[self])
     <4>1. max[self] >= num[k]
       BY <3>2, GEQorLT
     <4>2. QED
       BY <3>2, <4>1, SimplifyAndSolve
   <3>3. QED
     BY <3>1, <3>2
 <2>3. max[self] >= num[i] => max'[self] >= num'[i]
   BY <2>2, GEQTransitive
 <2>4. After(self,i) => After(self,i)'
   <3>1. HAVE After(self,i)
   <3>2. i \in unread[self] \/ max[self] >= num[i]
     BY <3>1 DEF After
   <3>3 CASE i \in unread[self] /\ i # k
       BY <3>3, <3>1, SimplifyAndSolve DEF After
   <3>4 CASE i \in unread[self] /\ i = k
     BY <3>4, <2>2, <3>1, SimplifyAndSolve DEF After
   <3>5 CASE max[self] >= num[i]
     BY <3>5, <2>3, <3>1, SimplifyAndSolve DEF After
   <3>6. QED
     BY <3>2, <3>3, <3>4, <3>5
 (* Proof of remaining conjuncts of the invariant *)
 <2>5. /\ pc'[i] \in {"p5", "p6"} => \A j \in (P \ unread'[i]) \ {i} : After(j, i)'
       /\ pc'[i] \in {"p7", "p8"} => \A j \in P \ {i} : After(j, i)'
   <3>. SUFFICES ASSUME NEW j \in P,
                        \/ pc'[i] \in {"p5", "p6"} /\ j \in (P \ unread'[i]) \ {i}
                        \/ pc'[i] \in {"p7", "p8"} /\ j \in P \ {i}
                 PROVE  After(j, i)'
       OBVIOUS
   <3>1. i # self
     OBVIOUS
   <3>2. UNCHANGED <<pc[i], unread[i]>>
     BY <3>1
   <3>3. After(j,i)
     BY <3>2
   <3>4. CASE j = self
     BY <3>3, <3>4, <2>4
   <3>5. CASE j # self
     <4>1. UNCHANGED <<num[j], num[i], pc[j], unread[j], max[j]>>
       (* FIXME: Isabelle should find the following case split by itself *)
       <5>1. CASE num[k] > max[self]
         BY <3>1, <3>5, <5>1, SimplifyAndSolve
       <5>2. CASE ~ (num[k] > max[self])
         BY <3>1, <3>5, <5>2, SimplifyAndSolve
       <5>3. QED
         BY <5>1, <5>2
     <4>2. QED
       BY <3>3, <4>1, AfterPrime
   <3>6. QED
     BY <3>4, <3>5
 <2>6. /\ (pc'[i] = "p6")
       /\ \/ (pc'[nxt'[i]] = "p2") /\ (i \notin unread'[nxt'[i]])
          \/ pc'[nxt'[i]] = "p3"
       => max'[nxt'[i]] >= num'[i]
   BY <2>2, <2>3
 <2>7. QED
   BY <2>1, <2>5, <2>6 DEF IInv

<1>3. CASE p3(self)
   (************************************************************************)
   (* This proof takes the PM & Isabelle 5 min 9 sec on SVC-LAMPORT-5      *)
   (* Down to 26 sec on Stephan's laptop.                                  *)
   (************************************************************************)
 <2>. USE <1>3 DEF p3
 <2>1. /\ (num'[i] = 0) <=> (pc'[i] \in {"p1", "p2", "p3"})
       /\ flag'[i] <=> (pc'[i] \in {"p2", "p3", "p4"})
   <3>1. CASE i = self
     BY <3>1, SimplifyAndSolve
   <3>2. CASE i # self
     BY <3>2
   <3>3. QED
     BY <3>1, <3>2
 <2>2. /\ (pc'[i] \in {"p5", "p6"}) => \A j \in (P \ unread'[i]) \ {i} : After(j, i)'
       /\ (pc'[i] \in {"p7", "p8"}) => \A j \in P \ {i} : After(j, i)'
   <3>. SUFFICES ASSUME NEW j \in P,
                        \/ pc'[i] \in {"p5", "p6"} /\ j \in (P \ unread'[i]) \ {i}
                        \/ pc'[i] \in {"p7", "p8"} /\ j \in P \ {i}
                 PROVE  After(j,i)'
      OBVIOUS
   <3>. i # self
     OBVIOUS
   <3>1. CASE j = self
     <4>. USE <3>1
     <4>. max[j] \in Nat
       OBVIOUS
     <4>. num'[j] \in Nat
       BY SimplifyAndSolve
     <4>1. After(j,i)
       OBVIOUS
     <4>2. max[j] >= num[i]
       BY <4>1 DEF After
     <4>3. num'[j] > max[j]
       BY SimplifyAndSolve
     <4>4. num'[j] > num[i]
       BY <4>2, <4>3, Transitivity2
     <4>5. GG(i,j)'
       BY <4>4, SimplifyAndSolve DEF GG
     <4>6. QED
       BY <4>1, <4>5, SimplifyAndSolve DEF After
   <3>2. CASE j # self
     <4>1. After(j,i) /\ UNCHANGED <<num[j], num[i], pc[j], unread[j], max[j]>>
       BY <3>2
     <4>2. QED
       BY <4>1, AfterPrime
   <3>4. QED
     BY <3>1, <3>2
 <2>3. /\ (pc'[i] = "p6")
       /\ \/ (pc'[nxt'[i]] = "p2") /\ (i \notin unread'[nxt'[i]])
          \/ pc'[nxt'[i]] = "p3"
       => max'[nxt'[i]] >= num'[i]
   OBVIOUS
 <2>4. QED
   BY <2>1, <2>2, <2>3 DEF IInv

<1>4. CASE p4(self)
   (************************************************************************)
   (* This proof takes the PM & Isabelle 2 min 14 sec on SVC-LAMPORT-5     *)
   (* Down to 22 sec on Stephan's laptop.                                  *)
   (************************************************************************)
 <2>. USE <1>4 DEF p4

 <2>1. /\ (num'[i] = 0) <=> (pc'[i] \in {"p1", "p2", "p3"})
       /\ flag'[i] <=> (pc'[i] \in {"p2", "p3", "p4"})
   OBVIOUS
 <2>2. /\ (pc'[i] \in {"p5", "p6"}) => \A j \in (P \ unread'[i]) \ {i} : After(j, i)'
       /\ (pc'[i] \in {"p7", "p8"}) => \A j \in P \ {i} : After(j, i)'
   <3>. SUFFICES ASSUME NEW j \in P,
                        \/ pc'[i] \in {"p5", "p6"} /\ j \in (P \ unread'[i]) \ {i}
                        \/ pc'[i] \in {"p7", "p8"} /\ j \in P \ {i}
                 PROVE  After(j,i)'
      OBVIOUS
   <3>. i # self
     OBVIOUS
   <3>1. CASE j = self
     <4>0. USE <3>1
     <4>1. After(j,i)
       OBVIOUS
     <4>2. GG(i,j)'
       BY <4>1 DEF After, GG
     <4>3. QED
       BY <4>1, <4>2, SimplifyAndSolve DEF After
   <3>2. CASE j # self
     <4>0. USE <3>2
     <4>1. After(j,i) /\ UNCHANGED <<num[i], num[j], pc[j], unread[i], max[i]>>
       OBVIOUS
     <4>2. QED
       BY <4>1, AfterPrime
   <3>3. QED
     BY <3>1, <3>2
 <2>3. /\ (pc'[i] = "p6")
       /\ \/ (pc'[nxt'[i]] = "p2") /\ (i \notin unread'[nxt'[i]])
          \/ pc'[nxt'[i]] = "p3"
       => max'[nxt'[i]] >= num'[i]
   OBVIOUS
 <2>4. QED
   BY <2>1, <2>2, <2>3 DEF IInv

(************************************************************************)
(* Proof for action p5 split into two subcases according to the case    *)
(* distinction in the action definition.                                *)
(* This proof takes the PM & Isabelle 3 min 37 sec on SVC-LAMPORT-5     *)
(* Down to 52 sec on Stephan's laptop (for <1>5a and <1>5b).            *)
(************************************************************************)

<1>5a. CASE p5(self) /\ unread[self] = {}
 <2>. /\ pc[self] = "p5" /\ unread[self] = {}
      /\ pc' = [pc EXCEPT ![self] = "p7"]
      /\ UNCHANGED <<nxt, num, flag, unread, max>>
   BY <1>5a DEF p5
 <2>1. /\ (num'[i] = 0) <=> (pc'[i] \in {"p1", "p2", "p3"})
       /\ flag'[i] <=> (pc'[i] \in {"p2", "p3", "p4"})
   OBVIOUS
 <2>2. /\ (pc'[i] \in {"p5", "p6"}) => \A j \in (P \ unread'[i]) \ {i} : After(j, i)'
       /\ (pc'[i] \in {"p7", "p8"}) => \A j \in P \ {i} : After(j, i)'
   <3>. SUFFICES ASSUME NEW j \in P,
                        \/ pc'[i] \in {"p5", "p6"} /\ j \in (P \ unread'[i]) \ {i}
                        \/ pc'[i] \in {"p7", "p8"} /\ j \in P \ {i}
                 PROVE  After(j,i)'
     OBVIOUS
   <3>1. CASE i = self
     <4>1. After(j,i) /\ UNCHANGED <<num[i], num[j], pc[j], unread[i], max[i]>>
       BY <3>1
     <4>2. QED
       BY <4>1, AfterPrime
   <3>2. CASE i # self
     <4>0. USE <3>2
     <4>1. After(j,i)
       OBVIOUS
     <4>2. j # self  (** otherwise would have i \in unread[self], contradiction **)
       BY <4>1 DEF After
     <4>4. UNCHANGED <<num[i], num[j], pc[j], unread[i], max[i]>>
       BY <4>2
     <4>5. QED
       BY <4>1, <4>4, AfterPrime
   <3>3. QED
     BY <3>1, <3>2
 <2>3. /\ (pc'[i] = "p6")
       /\ \/ (pc'[nxt'[i]] = "p2") /\ (i \notin unread'[nxt'[i]])
          \/ pc'[nxt'[i]] = "p3"
       => max'[nxt'[i]] >= num'[i]
   OBVIOUS
 <2>4. QED
   BY <2>1, <2>2, <2>3 DEF IInv

<1>5b. CASE p5(self) /\ unread[self] # {}
 <2>. PICK k \in unread[self] :
             /\ pc[self] = "p5"
             /\ nxt' = [nxt EXCEPT ![self] = k]
             /\ ~ flag[nxt'[self]]
             /\ pc' = [pc EXCEPT ![self] = "p6"]
             /\ UNCHANGED << num, flag, unread, max >>
   BY <1>5b DEF p5
 <2>. k \in P
   OBVIOUS
 <2>1. /\ (num'[i] = 0) <=> (pc'[i] \in {"p1", "p2", "p3"})
       /\ flag'[i] <=> (pc'[i] \in {"p2", "p3", "p4"})
   OBVIOUS
 <2>2. /\ (pc'[i] \in {"p5", "p6"}) => \A j \in (P \ unread'[i]) \ {i} : After(j, i)'
       /\ (pc'[i] \in {"p7", "p8"}) => \A j \in P \ {i} : After(j, i)'

   <3>. SUFFICES ASSUME NEW j \in P,
                        \/ pc'[i] \in {"p5", "p6"} /\ j \in (P \ unread'[i]) \ {i}
                        \/ pc'[i] \in {"p7", "p8"} /\ j \in P \ {i}
                 PROVE  After(j, i)'
       OBVIOUS
   <3>. j # i
     OBVIOUS
   <3>1. After(j,i)
     OBVIOUS
   <3>2. CASE i = self
     <4>1. UNCHANGED <<num[j], num[i], pc[j], unread[j], max[j]>>
       BY <3>2
     <4>2. QED
       BY <3>1, <4>1, AfterPrime
   <3>3. CASE i # self /\ j = self
     <4>.  USE <3>3
     <4>1. GG(i,j) /\ i \in unread[j]
       BY <3>1 DEF After
     <4>2. GG(i,j)' /\ i \in unread'[j]
       BY <4>1 DEF GG
     <4>3. QED
       BY <3>1, <4>2, SimplifyAndSolve DEF After
   <3>4. CASE i # self /\ j # self
     <4>1. UNCHANGED <<num[j], num[i], pc[j], unread[j], max[j]>>
       BY <3>4
     <4>2. QED
       BY <3>1, <4>1, AfterPrime
   <3>5. QED
     BY <3>2, <3>3, <3>4
 <2>3. /\ (pc'[i] = "p6")
       /\ \/ (pc'[nxt'[i]] = "p2") /\ (i \notin unread'[nxt'[i]])
          \/ pc'[nxt'[i]] = "p3"
       => max'[nxt'[i]] >= num'[i]
   <3>.  HAVE /\ (pc'[i] = "p6")
              /\ \/ (pc'[nxt'[i]] = "p2") /\ (i \notin unread'[nxt'[i]])
                 \/ pc'[nxt'[i]] = "p3"
   <3>2. CASE i = self
     <4>.  USE <3>2
     <4>1. IInv(k)
       BY Inv DEF Inv
     <4>2. pc[k] \notin {"p2", "p3", "p4"}
       BY <4>1 DEF IInv
     <4>3. k # self
       OBVIOUS  (* from type invariant *)
     <4>4. QED  (* contradiction between HAVE and IInv(k) *)
       BY <4>2, <4>3
   <3>3. CASE i # self
     BY <3>3
   <3>4. QED
     BY <3>2, <3>3
 <2>4. QED
   BY <2>1, <2>2, <2>3 DEF IInv

<1>6. CASE p6(self)
   (************************************************************************)
   (* This proof takes the PM & Isabelle 6 min 49 sec on SVC-LAMPORT-5     *)
   (* Down to 1 min 12 sec on Stephan's laptop.                            *)
   (************************************************************************)
  <2>. USE <1>6 DEF p6
  <2>1. /\ (num'[i] = 0) <=> (pc'[i] \in {"p1", "p2", "p3"})
        /\ flag'[i] <=> (pc'[i] \in {"p2", "p3", "p4"})
    OBVIOUS
  <2>2. /\ (pc'[i] \in {"p5", "p6"}) => \A j \in (P \ unread'[i]) \ {i} : After(j, i)'
        /\ (pc'[i] \in {"p7", "p8"}) => \A j \in P \ {i} : After(j, i)'
   <3>. SUFFICES ASSUME NEW j \in P,
                        \/ pc'[i] \in {"p5", "p6"} /\ j \in (P \ unread'[i]) \ {i}
                        \/ pc'[i] \in {"p7", "p8"} /\ j \in P \ {i}
                 PROVE  After(j,i)'
      OBVIOUS
   <3>. j # i
     OBVIOUS
   <3>1. CASE i = self
     <4>. USE <3>1
     <4>1. After(j,i)
       <5>1. CASE j \in (P \ unread[i]) \ {i}
         BY <5>1
       <5>2. CASE j = nxt[self]
         <6>. USE <5>2
         <6>1. IInv(j)
           BY Inv DEF Inv
         <6>2. num[i] > 0
           BY NatGEQZero
         <6>3. CASE num[j] = 0
           BY <6>1, <6>2, <6>3 DEF IInv, After
         <6>4. CASE num[j] # 0 /\ GG(i,j)  (* GG(i,j) from definition of p6 *)
           <7>. USE <6>4
           <7>1. CASE pc[j] \in {"p4", "p5", "p6"}
             <8>. USE <7>1
             <8>1. pc[j] \in {"p5", "p6"} => i \in unread[j]
               <9>. HAVE pc[j] \in {"p5", "p6"}
               <9>. SUFFICES ASSUME i \notin unread[j]
                             PROVE  FALSE
                  OBVIOUS
               <9>1. After(i,j)
                 BY <6>1 DEF IInv
               <9>2. GG(j,i)
                 BY <9>1 DEF After
               <9>3. QED
                 BY <9>2, GGIrreflexive
             <8>2. QED
               BY <6>2, <8>1 DEF After
           <7>2. CASE pc[j] \in {"p7", "p8"}  (* leads to contradiction *)
             <8>1. After(i,j)
               BY <6>1, <7>2 DEF IInv
             <8>2. GG(j,i)
               BY <8>1 DEF After
             <8>3. QED
               BY <8>2, GGIrreflexive
           <7>3. QED
             BY <6>1, <7>1, <7>2 DEF IInv
         <6>5. QED
           BY <6>3, <6>4 DEF GG
       <5>3. QED
         BY <5>1, <5>2
     <4>2. UNCHANGED <<num[j], num[i], pc[j], unread[j], max[j]>>
       OBVIOUS
     <4>3. QED
       BY <4>1, <4>2, AfterPrime
   <3>2. CASE i # self /\ j = self
     <4>. USE <3>2
     <4>1. After(j,i)
       OBVIOUS
     <4>2. GG(i,j) /\ i \in unread[j]
       BY <4>2 DEF After
     <4>3. CASE i = nxt[self]  (* we show that this case is actually impossible *)
       <5>. USE <4>3
       <5>. num[i] # 0
         OBVIOUS
       <5>1. CASE self > nxt[self]
         <6>1. num[nxt[self]] > num[self]
           BY <5>1  (* from definition of p6 *)
         <6>2. ~(nxt[self] > self)
           BY <5>1, GTAxiom, PsubsetNat
         <6>3. num[self] >= num[nxt[self]]
           BY <4>2, <6>2 DEF GG  (* from definition of GG and assumptions for i and j *)
         <6>4. num[nxt[self]] > num[nxt[self]]
           BY <6>1, <6>3, Transitivity2
         <6>5. QED
           BY <6>4, SimplifyAndSolve
       <5>2. CASE ~(self > nxt[self])
         <6>1. num[nxt[self]] >= num[self]
           BY <5>2  (* from definition of p6 *)
         <6>2. nxt[self] > self
           BY <5>2, GEQAxiom, PsubsetNat
         <6>3. num[self] > num[nxt[self]]
           BY <4>2, <6>2 DEF GG  (* from definition of GG, assumptions for i and j *)
         <6>4. num[self] > num[self]
           BY <6>1, <6>3, Transitivity2
         <6>5. QED
           BY <6>4, SimplifyAndSolve
       <5>3. QED
         BY <5>1, <5>2
     <4>4. CASE i # nxt[self]
       <5>1. GG(i,j)' /\ i \in unread'[j]
         BY <4>2, <4>4 DEF GG
       <5>2. QED
         BY <4>1, <5>1, SimplifyAndSolve DEF After
     <4>5. QED
       BY <4>3, <4>4
   <3>3. CASE i # self /\ j # self
     <4>1. After(j,i) /\ UNCHANGED <<num[j], num[i], pc[j], unread[j], max[j]>>
       BY <3>3
     <4>2. QED
       BY <4>1, AfterPrime
   <3>4. QED
     BY <3>1, <3>2, <3>3
  <2>3. /\ (pc'[i] = "p6")
        /\ \/ (pc'[nxt'[i]] = "p2") /\ (i \notin unread'[nxt'[i]])
           \/ pc'[nxt'[i]] = "p3"
        => max'[nxt'[i]] >= num'[i]
    OBVIOUS
  <2>4. QED
   BY <2>1, <2>2, <2>3 DEF IInv

<1>7. CASE p7(self)
   (************************************************************************)
   (* This proof takes the PM & Isabelle 2 min 25 sec on SVC-LAMPORT-5     *)
   (* Down to 13 sec on Stephan's laptop.                                  *)
   (************************************************************************)
  <2>. USE <1>7 DEF p7
  <2>1. /\ (num'[i] = 0) <=> (pc'[i] \in {"p1", "p2", "p3"})
        /\ flag'[i] <=> (pc'[i] \in {"p2", "p3", "p4"})
    OBVIOUS
  <2>2. /\ (pc'[i] \in {"p5", "p6"}) => \A j \in (P \ unread'[i]) \ {i} : After(j, i)'
        /\ (pc'[i] \in {"p7", "p8"}) => \A j \in P \ {i} : After(j, i)'
   <3>. SUFFICES ASSUME NEW j \in P,
                        \/ pc'[i] \in {"p5", "p6"} /\ j \in (P \ unread'[i]) \ {i}
                        \/ pc'[i] \in {"p7", "p8"} /\ j \in P \ {i}
                 PROVE  After(j,i)'
      OBVIOUS
   <3>1. After(j,i)
     OBVIOUS
   <3>2. j # self
     BY <3>1 DEF After
   <3>3. UNCHANGED <<num[j], num[i], pc[j], unread[j], max[j]>>
     BY <3>2
   <3>4. QED
       BY <3>1, <3>3, AfterPrime
  <2>3. /\ (pc'[i] = "p6")
        /\ \/ (pc'[nxt'[i]] = "p2") /\ (i \notin unread'[nxt'[i]])
           \/ pc'[nxt'[i]] = "p3"
        => max'[nxt'[i]] >= num'[i]
    OBVIOUS
  <2>4. QED
   BY <2>1, <2>2, <2>3 DEF IInv

<1>8. CASE p8(self)
   (************************************************************************)
   (* This proof takes the PM & Isabelle 1 min 22 sec on SVC-LAMPORT-5     *)
   (* Down to 16 sec on Stephan's laptop.                                  *)
   (* NB: The proof of this case is a verbatim copy of the previous one.   *)
   (************************************************************************)
  <2>. USE <1>8 DEF p8
  <2>1. /\ (num'[i] = 0) <=> (pc'[i] \in {"p1", "p2", "p3"})
        /\ flag'[i] <=> (pc'[i] \in {"p2", "p3", "p4"})
    OBVIOUS
  <2>2. /\ (pc'[i] \in {"p5", "p6"}) => \A j \in (P \ unread'[i]) \ {i} : After(j, i)'
        /\ (pc'[i] \in {"p7", "p8"}) => \A j \in P \ {i} : After(j, i)'
   <3>. SUFFICES ASSUME NEW j \in P,
                        \/ pc'[i] \in {"p5", "p6"} /\ j \in (P \ unread'[i]) \ {i}
                        \/ pc'[i] \in {"p7", "p8"} /\ j \in P \ {i}
                 PROVE  After(j,i)'
      OBVIOUS
   <3>1. After(j,i)
     OBVIOUS
   <3>2. j # self
     BY <3>1 DEF After
   <3>3. UNCHANGED <<num[j], num[i], pc[j], unread[j], max[j]>>
     BY <3>2
   <3>4. QED
       BY <3>1, <3>3, AfterPrime
  <2>3. /\ (pc'[i] = "p6")
        /\ \/ (pc'[nxt'[i]] = "p2") /\ (i \notin unread'[nxt'[i]])
           \/ pc'[nxt'[i]] = "p3"
        => max'[nxt'[i]] >= num'[i]
    OBVIOUS
  <2>4. QED
   BY <2>1, <2>2, <2>3 DEF IInv

<1>9. CASE UNCHANGED vars
   (************************************************************************)
   (* This proof takes the PM & Isabelle 42 sec on SVC-LAMPORT-5           *)
   (* Down to 2 sec on Stephan's laptop.                                   *)
   (************************************************************************)
   BY <1>9, SimplifyAndSolve DEF IInv, After, GG, vars

<1>10. QED
  BY <1>1, <1>2a, <1>2b, <1>3, <1>4, <1>5a, <1>5b, <1>6, <1>7, <1>8, <1>9 DEF p

=============================================================================

(***************************************************************************)
(* The proof of the last theorem took me about a week.  I wrote it the way *)
(* I usually write such proofs, first breaking it down into checking that  *)
(* each action preserves the invariant, then for each action checking that *)
(* it preserves each conjunct of the invariant.  After proving that for a  *)
(* couple of actions, I realized that the reasoning was similar for the    *)
(* same conjunct in different actions.  This may mean that I should have   *)
(* broken it up the other way, first by conjuncts of the invariant.        *)
(* However, I probably would have had to prove each conjunct by a case     *)
(* split on the actions, so that might have only made things worse.  I did *)
(* eventually figure out that it was better to group the conjuncts,        *)
(* proving the conjunction of two of them at once.                         *)
(*                                                                         *)
(* Because of the similarity of reasoning about the same conjuncts for     *)
(* different actions, I was able to do a lot of copy-and-paste from the    *)
(* proof of the same conjunct in one action to its proof in another        *)
(* action.  When the invariant was preserved for similar                   *)
(* reasoning--usually because it was a subcase in which the conjunct was   *)
(* preserved because nothing relevant changed--the proof went through      *)
(* with little or no change.  Sometimes a subproof had to be completely    *)
(* rewritten because the invariant was preserved for a different reason.   *)
(*                                                                         *)
(* No matter how trivial the reasoning, Zenon and Isabelle require that    *)
(* quantifiers in a conclusion be eliminated.  And Isabelle sometimes      *)
(* needs to be led by the nose.  For example, the proof that leaving all   *)
(* the variables unchanged preserves the invariant took 33 lines.  I       *)
(* found one place in which a HIDE was necessary to get something          *)
(* proven--otherwise both Zenon and Isabelle got lost and was unable to    *)
(* do a fairly simple deduction.  I didn't test if the judicious use of    *)
(* HIDE would have sped up some of the proofs that took Isabelle a long    *)
(* time.                                                                   *)
(*                                                                         *)
(* The best strategy for writing a proof is to try something and, if it    *)
(* fails, keep breaking the proof into simpler steps until you either      *)
(* succeed or (more often) realize what simple fact it hasn't been told    *)
(* that it needs.  If things were infinitely fast, you'd check these one   *)
(* at a time.  Since they're not, there's a tradeoff between trying to     *)
(* check a lot of things in one run and waiting a long time for Zenon to   *)
(* grind on things that it won't reach because an earlier step fails.      *)
(* When doing this, make sure you can tell from Isabelle's printout what   *)
(* it's not succeeding on if it sits there thinking for a long time.  In   *)
(* other words, don't try two different steps in the same run that have    *)
(* the same goal (for example, two CASEs).                                 *)
(*                                                                         *)
(* It seems to me that Zenon fails on all reasoning about EXCEPT. However, *)
(* it works when I run it on little tests.  Anyway, most of the proof's    *)
(* execution time is spent waiting for Zenon to fail.  I should probably   *)
(* add a pragma telling the PM not to use Zenon on these steps.  (About    *)
(* all that seems possible is to tell the PM to run Zenon for a very short *)
(* time.)                                                                  *)
(*                                                                         *)
(* On several occasions, Isabelle failed to check obligations that I       *)
(* thought Isabelle had already checked.  It's possible this was operator  *)
(* error, but it happened enough times that I suspect it wasn't.           *)
(***************************************************************************)
