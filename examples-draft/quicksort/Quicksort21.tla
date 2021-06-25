----------------------------- MODULE Quicksort21 ----------------------------
(***************************************************************************)
(* This module specifies a Quicksort algorithm for sorting a sequence A of *)
(* length N of integers.                                                   *)
(* Derived by Stephan from Jael's Quicksort07.                             *)
(***************************************************************************)
EXTENDS Integers, TLAPS, FiniteSetTheorems, Utils, Bags

CONSTANT A0, N
 
ASSUME ConstantAssump == /\ N \in Nat \ {0}
                         /\ A0 \in [1..N -> Int] 

IsSorted(B) == \A i, j \in 1..N : 
(i < j) => (B[i] =< B[j])

(* Modification: made Automorphisms and ** top-level operators because we want
   to reason about them.
PermsOf(Arr) ==
  LET Automorphisms(S) == { f \in [S -> S] : \A y \in S : \E x \in S : f[x] = y }
  
      f ** g == [x \in DOMAIN g |-> f[g[x]]]
      
  IN  { Arr ** f : f \in Automorphisms(DOMAIN Arr) }
*)

(* The set of automorphisms of a finite set S. *)
Automorphisms(S) == { f \in [S -> S] : \A y \in S : \E x \in S : f[x] = y }

(* Function composition. *)
f ** g == [x \in DOMAIN g |-> f[g[x]]]

(* Set of permutations of array Arr (with finite domain). *)
PermsOf(Arr) == { Arr ** f : f \in Automorphisms(DOMAIN Arr) }
  
(* Leslie's original definition: the problem is that the automorphism that generates
   C from B is not restricted to the interval lo .. hi, so it might exchange some
   elements within this interval with elements outside (as long as the exchanged
   elements have the same values). This not only drastically complicates the proofs
   but also obviously does not correspond to any sensible implementation. One could
   even argue that it complicates parallelization of Quicksort, since it is not
   obvious from the specification that partitioning two non-overlapping intervals in
   the worklist does not interfere.
Partitions(B, pivot, lo, hi) ==
  {C \in PermsOf(B) : 
      /\ \A i \in 1..(lo-1) \cup (hi+1)..N : C[i] = B[i]
      /\ \A i \in lo..pivot, j \in (pivot+1)..hi : C[i] =< C[j] }
*)

(* Jael's definition. I'm following the same idea but introduce a bit more structure.
Partitions(B, pivot, lo, hi) ==
{ C \in [1..N -> Int] : 
    /\ (\E D \in PermsOf([i \in lo..hi |-> B[i]]) : C = [i \in 1..N |-> IF i \in lo..hi 
                                                                           THEN D[i]
                                                                           ELSE B[i] ] )
    /\ \A i \in lo..pivot, j \in (pivot+1)..hi : C[i] =< C[j]                                                                       
  } 
*)

(* Set of permutations such that all elements below pivot are smaller than all
   elements above it. *)
OrderingPerms(Arr, pivot) ==
  { B \in PermsOf(Arr) : \A i,j \in DOMAIN Arr : i <= pivot /\ pivot < j => B[i] <= B[j] }

(* Copy of array Arr with elements between lo and hi overridden with values from B. *)
Override(Arr, lo, hi, B) ==
  [x \in DOMAIN Arr |-> IF x \in lo .. hi THEN B[x] ELSE Arr[x]]

Partitions(B, pivot, lo, hi) ==
  { Override(B, lo, hi, C) : C \in OrderingPerms(Restrict(B, lo .. hi), pivot) }

VARIABLES A, U

(* Type correctness predicate strengthened w.r.t. Jael's version *)
TypeOK == /\ A \in [1..N -> Int]
          /\ A \in PermsOf(A0)
          /\ U \in SUBSET { u \in (1..N) \X (1..N) : u[1] <= u[2] }
          
vars == <<A, U>>

Init == /\ A = A0
        /\ U = { <<1, N>> }

Next ==   /\ U # {}    \* NB: This conjunct is implied by the following one
          /\ \E b \in 1..N, t \in 1..N :
               /\ <<b, t>> \in U
               /\ IF b # t
                    THEN \E p \in b..(t-1) :
                           /\ A' \in Partitions(A, p, b, t)
                           /\ U' = (U \ {<<b, t>>}) \cup {<<b, p>>, <<p+1, t>>}
                    ELSE /\ U' = U \ {<<b, t>>}
                         /\ A' = A  
                        
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

-----------------------------------------------------------------------------

(* The main correctness (safety) property: 
   whenever U becomes empty, A contains a sorted permutation of A0 *)
Safety == (U = {}) => (A \in PermsOf(A0)) /\ IsSorted(A)


(* UnsortedIsCovered : if there are two positions i,j that point to values which are not sorted, 
    then the work list U contains a pair <<b,t>> that covers both i and j. *)
UnsortedIsCovered == \A i, j \in 1..N  :  i < j /\ A[j] < A[i]
                                => \E u \in U : {i,j} \subseteq u[1] .. u[2]

(* NoOverlap : no two pairs contained in the work list U overlap in range *)
NoOverlap == \A u,v \in U : (u[1] .. u[2]) \cap (v[1] .. v[2]) # {} => u = v
(* NoOverlap == \A a,b \in 1..N : <<a,b>> \in U => \A i \in a..b :  \A c,d \in 1..N : <<c,d>> \in U \ {<<a,b>>} => ~ i \in c..d *)


Inv ==
  /\ UnsortedIsCovered
  /\ NoOverlap

-----------------------------------------------------------------------------

(***************************************************************************)
(* Lemmas about constant operators.                                        *)
(***************************************************************************)

LEMMA ImageOfIntervalIsFinite == 
  ASSUME NEW X, NEW a \in Int, NEW b \in Int
  PROVE  IsFiniteSet({X[k] : k \in a..b})
<1>1. Restrict(X, a..b) \in Surjection(a..b, {X[k] : k \in a..b})
  BY DEF Restrict, Surjection
<1>. QED
  BY <1>1, FS_Surjection, FS_Interval

(* A permutation of an array is an array of the same type. *)
LEMMA PermsOf_type ==
  ASSUME NEW S, NEW T, NEW X \in [S -> T], NEW Y \in PermsOf(X)
  PROVE  Y \in [S -> T]
BY DEF PermsOf, Automorphisms, **
  
(* Any array is a permutation of itself. *)
LEMMA PermsOf_refl == 
  ASSUME NEW S, NEW T, NEW X \in [S -> T]
  PROVE  X \in PermsOf(X)
BY Isa DEF PermsOf, Automorphisms, **

(* The composition of two automorphisms is an automorphism. *)
LEMMA Automorphisms_trans ==
  ASSUME NEW S, NEW f \in Automorphisms(S), NEW g \in Automorphisms(S)
  PROVE  f ** g \in Automorphisms(S)
BY DEF Automorphisms, **

(* A permutation of a permutation of X is a permutation of X. *)
LEMMA PermsOf_trans ==
  ASSUME NEW S, NEW T, NEW X \in [S -> T], NEW Y \in PermsOf(X), NEW Z \in PermsOf(Y)
  PROVE  Z \in PermsOf(X)
<1>1. Y \in [S -> T]
  BY PermsOf_type
<1>2. PICK f \in Automorphisms(S) : Y = X ** f
  BY DEF PermsOf
<1>3. PICK g \in Automorphisms(S) : Z = Y ** g
  BY <1>1 DEF PermsOf
<1>4. Z = X ** (f ** g)
  BY <1>2, <1>3 DEF Automorphisms, **
<1>. QED
  BY Automorphisms_trans, <1>4 DEF PermsOf

(* The set of values contained in a permutation is the set of the original array. *)
LEMMA PermsOf_range ==
  ASSUME NEW X, NEW Y \in PermsOf(X)
  PROVE  Range(Y) = Range(X)
BY DEF PermsOf, Automorphisms, **, Range

(* A partition is a permutation. *)
LEMMA PartitionPermsOf ==
  ASSUME NEW S, NEW T, NEW B \in [S -> T], 
         NEW lo \in Int, NEW hi \in Int, NEW pivot \in Int, lo .. hi \subseteq S,
         NEW C \in Partitions(B, pivot, lo, hi)
  PROVE  C \in PermsOf(B)
<1>1. PICK CC \in OrderingPerms(Restrict(B, lo .. hi), pivot) :
              C = Override(B, lo, hi, CC)
  BY DEF Partitions
<1>2. CC \in PermsOf(Restrict(B, lo .. hi))
  BY DEF OrderingPerms
<1>3. PICK g \in Automorphisms(lo .. hi) : CC = Restrict(B, lo..hi) ** g
  BY <1>2 DEF PermsOf, Restrict
<1>. DEFINE h == [x \in S |-> IF x \in lo .. hi THEN g[x] ELSE x]
<1>4. h \in Automorphisms(S)
  BY DEF Automorphisms
<1>5. C = B ** h
  BY <1>1, <1>3 DEF Automorphisms, **, Override, Restrict
<1>. QED
  BY <1>4, <1>5 DEF PermsOf

(* For any partition, the set of values between lo and hi is the set of the 
   original values contained in the array within that interval. 
*)
LEMMA PartitionsSetStable ==
  ASSUME NEW B, NEW pivot, NEW lo, NEW hi, lo .. hi \subseteq DOMAIN B,
         NEW C \in Partitions(B, pivot, lo, hi)
  PROVE  Range(Restrict(C, lo .. hi)) = Range(Restrict(B, lo .. hi))
<1>1. PICK CC \in OrderingPerms(Restrict(B, lo .. hi), pivot) :
              C = Override(B, lo, hi, CC)
  BY DEF Partitions
<1>2. DOMAIN CC = lo .. hi
  BY DEF OrderingPerms, PermsOf, Automorphisms, **, Restrict
<1>3. Range(CC) = Range(Restrict(B, lo .. hi))
  BY PermsOf_range DEF OrderingPerms
<1>4. Range(Restrict(C, lo .. hi)) = Range(CC)
  BY <1>1, <1>2 DEF Override, Range, Restrict
<1>. QED
  BY <1>3, <1>4


-----------------------------------------------------------------------------

(***************************************************************************)
(* Proof of the invariant.                                                 *)
(***************************************************************************)

USE ConstantAssump

(***************************************************************************)
(* We first prove type correctness, although there is no logical reason    *)
(* to prove it separately from the main invariant.                         *)
(***************************************************************************)

LEMMA Typing == Spec => []TypeOK
<1>1. ASSUME Init
      PROVE  TypeOK
  <2>1. A \in [1..N -> Int]  BY <1>1 DEF Init
  <2>2. A \in PermsOf(A0)    BY <1>1, PermsOf_refl DEF Init
  <2>3. U \in  SUBSET {u \in (1 .. N)  \X  (1 .. N) : u[1]  =<  u[2]}
    BY <1>1 DEF Init
  <2>. QED  BY <2>1, <2>2, <2>3 DEF TypeOK

<1>2. ASSUME TypeOK, [Next]_vars
      PROVE  TypeOK'
  <2>1. CASE Next
    <3>1. PICK b \in 1..N, t \in 1..N : 
               /\ <<b,t>> \in U
               /\ IF b # t
                    THEN \E p \in b..(t-1) :
                           /\ A' \in Partitions(A, p, b, t)
                           /\ U' = (U \ {<<b, t>>}) \cup {<<b, p>>, <<p+1, t>>}
                    ELSE /\ U' = U \ {<<b, t>>}
                         /\ A' = A 
      BY <2>1 DEF Next
    <3>2. CASE b # t
      <4>1. PICK p \in b .. (t-1) :
                 /\ A' \in Partitions(A, p, b, t)
                 /\ U' = (U \ {<<b, t>>}) \cup {<<b, p>>, <<p+1, t>>}
        BY <3>1, <3>2
      <4>1a. /\ b \in Int
             /\ t \in Int
             /\ p \in Int
             /\ b .. t \subseteq 1 .. N
        OBVIOUS
      <4>2. A' \in PermsOf(A)
        BY PartitionPermsOf, TypeOK, <4>1, <4>1a, Zenon DEF TypeOK  \* not proved by SMT
      <4>3. A' \in [1..N -> Int]
        BY <4>2, TypeOK, PermsOf_type, Zenon DEF TypeOK
      <4>4. A' \in PermsOf(A0)
        BY <4>2, TypeOK, PermsOf_trans, Zenon DEF TypeOK
      <4>4a. /\ b <= p
             /\ p+1 <= t
             /\ p \in 1 .. N
             /\ p+1 \in 1 .. N
        OBVIOUS
      <4>5. U' \in  SUBSET {u \in (1 .. N)  \X  (1 .. N) : u[1]  =<  u[2]}
        BY <4>1, <4>4a, TypeOK, Isa DEF TypeOK
      <4>. QED  BY <4>3, <4>4, <4>5 DEF TypeOK
    <3>3. CASE b = t
      BY <3>1, <3>3, TypeOK DEF TypeOK
    <3>. QED  BY <3>2, <3>3
  <2>2. CASE UNCHANGED vars  BY <1>2, <2>2 DEF vars, TypeOK
  <2>. QED  BY <1>2, <2>1, <2>2
<1>. QED  BY <1>1, <1>2, PTL DEF Spec

(***************************************************************************)
(* Now we prove the main invariant.                                        *)
(***************************************************************************)
LEMMA Invariance == Spec => []Inv
<1>1. ASSUME Init
      PROVE  Inv
  BY <1>1 DEF Init, Inv, UnsortedIsCovered, NoOverlap
<1>2. ASSUME Inv, TypeOK, TypeOK', [Next]_vars
      PROVE  Inv'
  <2>. CASE Next
    <3>1. PICK b \in 1..N, t \in 1..N :
               /\ <<b, t>> \in U
               /\ IF b # t
                    THEN \E p \in b..(t-1) :
                           /\ A' \in Partitions(A, p, b, t)
                           /\ U' = (U \ {<<b, t>>}) \cup {<<b, p>>, <<p+1, t>>}
                    ELSE /\ U' = U \ {<<b, t>>}
                         /\ A' = A
      BY DEF Next
    <3>. CASE b # t
      <4>. PICK p \in b..(t-1) :
                /\ A' \in Partitions(A, p, b, t)
                /\ U' = (U \ {<<b, t>>}) \cup {<<b, p>>, <<p+1, t>>}
        BY <3>1
      <4>2. UnsortedIsCovered'
        <5>. SUFFICES ASSUME NEW i \in 1 .. N, NEW j \in 1 .. N,
                             i < j, A'[j] < A'[i]
                      PROVE  \E u \in U' : {i,j} \subseteq u[1] .. u[2]
          BY DEF UnsortedIsCovered
        <5>1. b .. t \subseteq DOMAIN A
          BY TypeOK DEF TypeOK
        <5>2. Range(Restrict(A', b..t)) = Range(Restrict(A, b..t))
          BY <5>1, PartitionsSetStable
        <5>. CASE i \notin b .. t
          (* In this case j cannot be within the interval b..t either because
             this would imply the existence of two overlapping intervals in U.
             But then A'[i] = A[i] and A'[j] = A[j], and there exists some
             entry in the worklist that covers them and that stays in the worklist. *)
          <6>1. A'[i] = A[i]
            BY TypeOK DEF TypeOK, Partitions, Override
          <6>2. ASSUME j \in b .. t PROVE FALSE
            <7>1. PICK jj \in b..t : A[jj] = A'[j]
              BY ONLY <6>2, <5>2, Zenon DEF Range, Restrict
                \* Zenon may timeout on slow machines without ONLY
            <7>2. /\ jj \in 1..N
                  /\ i < jj
                  /\ A[jj] < A[i]
              BY <6>1, <6>2, <7>1, TypeOK, TypeOK' DEF TypeOK
            <7>3. PICK u \in U : {i,jj} \subseteq u[1] .. u[2]
              BY <7>2, Inv DEF Inv, UnsortedIsCovered
            <7>4. u = <<b,t>>
              BY <3>1, <7>3, Inv DEF Inv, NoOverlap
            <7>. QED  BY <7>3, <7>4
          <6>3. A'[j] = A[j]
            BY TypeOK, <6>2 DEF TypeOK, Partitions, Override
          <6>. QED  BY <6>1, <6>3, Inv DEF Inv, UnsortedIsCovered
        <5>. CASE j \notin b .. t
          (* This case is symmetric to the preceding one. *)
          <6>1. A'[j] = A[j]
            BY TypeOK DEF TypeOK, Partitions, Override
          <6>2. ASSUME i \in b .. t PROVE FALSE
            <7>1. PICK ii \in b..t : A[ii] = A'[i]
              BY ONLY <6>2, <5>2, Zenon DEF Range, Restrict
                \* Zenon may timeout on slow machines without ONLY
            <7>2. /\ ii \in 1..N
                  /\ ii < j
                  /\ A[j] < A[ii]
              BY <6>1, <6>2, <7>1, TypeOK, TypeOK' DEF TypeOK
            <7>3. PICK u \in U : {ii,j} \subseteq u[1] .. u[2]
              BY <7>2, Inv DEF Inv, UnsortedIsCovered
            <7>4. u = <<b,t>>
              BY <3>1, <7>3, Inv DEF Inv, NoOverlap
            <7>. QED  BY <7>3, <7>4
          <6>3. A'[i] = A[i]
            BY TypeOK, <6>2 DEF TypeOK, Partitions, Override
          <6>. QED  BY <6>1, <6>3, Inv DEF Inv, UnsortedIsCovered
        <5>. CASE i \in b .. t /\ j \in b .. t
          (* In this case A'[i] and A'[j] have to be covered by one of the
             two new entries of the worklist because A' is a partition. *)
          <6>1. /\ A' \in [1..N -> Int]
                /\ \A k,l \in b..t : k <= p /\ p < l => A'[k] <= A'[l]
            BY TypeOK, TypeOK', Z3 DEF TypeOK, Partitions, Override, OrderingPerms, Restrict
          <6>. QED  BY <6>1, Z3 
        <5>. QED  OBVIOUS
      <4>3. NoOverlap'
        BY <3>1, Inv DEF Inv, NoOverlap
      <4>. QED  BY <4>2, <4>3 DEF Inv
    <3>. CASE b = t
      BY Inv, <3>1 DEF Inv, UnsortedIsCovered, NoOverlap
    <3>. QED  OBVIOUS
  <2>. CASE UNCHANGED vars  BY Inv DEF Inv, UnsortedIsCovered, NoOverlap, vars
  <2>. QED  BY <1>2
<1>. QED  BY <1>1, <1>2, Typing, PTL DEF Spec

(***************************************************************************)
(* Finally, we prove the correctness (safety) property.                    *)
(***************************************************************************)
THEOREM Spec => []Safety
<1>1. ASSUME TypeOK, Inv PROVE Safety
  BY <1>1, Z3 DEF TypeOK, Inv, UnsortedIsCovered, Safety, IsSorted
<1>. QED  BY <1>1, Typing, Invariance, PTL

     
=============================================================================

