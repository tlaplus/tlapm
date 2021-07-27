----------------------------- MODULE BubbleSort -----------------------------
(***************************************************************************)
(* This module contains a PlusCal description of the classic Bubble Sort   *)
(* algorithm and an incomplete TLAPS-checked proof of its correctness.     *)
(***************************************************************************)
EXTENDS Integers, TLAPS, TLC

CONSTANT N
ASSUME NAssumption == N \in Nat /\ N >= 1
  (*************************************************************************)
  (* The algorithm is actually correct for N = 0, but allowing for that    *)
  (* case complicates the proof a bit, so I decided not to handle that     *)
  (* possibility.                                                          *)
  (*************************************************************************)
-----------------------------------------------------------------------------
(***************************************************************************)
(* Here are some definitions used for stating and proving correctness.     *)
(* For simplicity, I decide to write an algorithm that sorts               *)
(* integer-valued arrays (functions) indexed by (with domain) 1..N.        *)
(*                                                                         *)
(* The obvious correctness condition is that, at termination, the array    *)
(* should be sorted--expressed by IsSorted.                                *)
(***************************************************************************)
IsSortedFromTo(A, i, j) == \A p, q \in i..j : (p =< q) => (A[p] =< A[q])

IsSortedTo(A, i) == \A j, k \in 1..i : (j =< k) => (A[j] =< A[k])

IsSorted(A) == IsSortedTo(A, N)

(***************************************************************************)
(* The less obvious correctness condition is that the array should be a    *)
(* permutation of its initial value.  I define IsPermOf(A, B) to mean that *)
(* arrays A and B are permutations of one another.  I start by defining    *)
(* Perms to be the set of permutations of (sequences of length N           *)
(* containing all of) the numbers from 1 through N.                        *)
(***************************************************************************)
Perms == { f \in [1..N -> 1..N] : 
                     \A i \in 1..N : \E j \in 1..N : f[i] = f[j] }

f ** g == [i \in 1..N |-> f[g[i]]]
   
IsPermOf(A, B) == \E f \in Perms : A = (B ** f)

(***************************************************************************)
(* Next, I define two useful permutations of 1..N , the identity Id and    *)
(* the permutation of 1..N that just exchanges two numbers.  (If the       *)
(* numbers are the same, it's the identity permutation.)                   *)
(***************************************************************************)
Id == [i \in 1..N |-> i] 

Exchange(i, j) == [Id EXCEPT ![i] = j, ![j] = i]

(***************************************************************************)
(* Here are some theorems that I figured would be useful for proving the   *)
(* correctness of Bubble Sort.                                             *)
(***************************************************************************)
THEOREM IdAPerm == Id \in Perms
BY DEF Perms, Id

THEOREM IdIdentity == \A A \in [1..N -> Int] : A ** Id = A
BY DEF Id, **

THEOREM IsPermOfReflexive == \A A \in [1..N -> Int]  : IsPermOf(A, A)
BY IdAPerm, IdIdentity DEF IsPermOf, Id

THEOREM ExchangeAPerm == \A i, j \in 1..N : Exchange(i, j) \in Perms
BY Zenon DEF Perms, Exchange, Id

THEOREM IsPermOfExchange == 
           \A A \in [1..N -> Int],  i, j \in 1..N :
             /\ [A EXCEPT ![i] = A[j], ![j] = A[i]] \in [1..N -> Int]
             /\ IsPermOf([A EXCEPT ![i] = A[j], ![j] = A[i]], A)
<1> DEFINE AA(A, i, j) == [A EXCEPT ![i] = A[j], ![j] = A[i]]
<1> SUFFICES ASSUME NEW A \in [1..N -> Int],  NEW i \in 1..N , NEW j \in 1..N 
             PROVE  AA(A, i, j) \in [1..N -> Int]  /\ IsPermOf(AA(A, i, j), A)
  BY Zenon
<1>1. AA(A,i,j) = A ** Exchange(i, j)
  BY Zenon DEF **, Exchange, Id  
<1>2. QED
  BY <1>1, ExchangeAPerm, Zenon DEF IsPermOf

THEOREM CompositionAssociative == 
           \A A \in [1..N -> Int], f, g \in [1..N -> 1..N] :
                (A ** f) ** g  =  A ** (f ** g)
BY DEF **

THEOREM CompositionOfPerms == \A f, g \in Perms : f ** g \in Perms
BY Zenon DEF **, Perms

THEOREM IsPermOfTransitive == 
          \A A, B, C \in [1..N -> Int] : 
             IsPermOf(A, B) /\ IsPermOf(B, C) => IsPermOf(A, C)
<1> SUFFICES ASSUME NEW A \in [1..N -> Int], NEW B \in [1..N -> Int],
                    NEW C \in [1..N -> Int], IsPermOf(A, B), IsPermOf(B, C)
             PROVE  IsPermOf(A, C)
  OBVIOUS
<1>1. PICK f, g \in Perms : (A = B ** g) /\  (B = C ** f)
  BY DEF IsPermOf
<1>2. f \in [1..N -> 1..N] /\ g \in [1..N -> 1..N]
  BY DEF Perms
<1>3. A = C ** (f ** g)
  BY <1>1, <1>2, CompositionAssociative
<1>. QED
  BY <1>3, CompositionOfPerms DEF IsPermOf
----------------------------------------------------------------------------
(***************************************************************************)
(* Here is the PlusCal algorithm followed by its TLA+ translation.  It was *)
(* model checked, with the asserts not commented out, for N = 4, with Int  *)
(* replaced by a set of integers containing 4 distinct elements.           *)
(***************************************************************************)
(*
--fair algorithm BubbleSort {
    variables A \in [1..N -> Int], A0 = A, i = 1, j = 1;
    { while (i < N)
       { \* assert IsSortedTo(A, i) /\ IsPermOf(A, A0);
         j := i+1 ;
         while (j > 1  /\  A[j-1] > A[j]) 
           { \* assert IsSortedTo(A, j-1) /\ IsSortedFromTo(A, j, i+1) /\ IsPermOf(A, A0) ;
             A[j-1] := A[j] || A[j] := A[j-1] ;
             j := j-1 ;        
           } ;
         i := i+1 ;
       } ;
      \* assert IsSorted(A) /\ IsPermOf(A, A0)
    } 
} 
*)
\* BEGIN TRANSLATION
VARIABLES A, A0, i, j, pc

vars == << A, A0, i, j, pc >>

Init == (* Global variables *)
        /\ A \in [1..N -> Int]
        /\ A0 = A
        /\ i = 1
        /\ j = 1
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ IF i < N
               THEN /\ j' = i+1
                    /\ pc' = "Lbl_2"
               ELSE /\ pc' = "Done"
                    /\ j' = j
         /\ UNCHANGED << A, A0, i >>

Lbl_2 == /\ pc = "Lbl_2"
         /\ IF j > 1  /\  A[j-1] > A[j]
               THEN /\ A' = [A EXCEPT ![j-1] = A[j],
                                      ![j] = A[j-1]]
                    /\ j' = j-1
                    /\ pc' = "Lbl_2"
                    /\ i' = i
               ELSE /\ i' = i+1
                    /\ pc' = "Lbl_1"
                    /\ UNCHANGED << A, j >>
         /\ A0' = A0

Next == Lbl_1 \/ Lbl_2
           \/ (* Disjunct to prevent deadlock on termination *)
              (pc = "Done" /\ UNCHANGED vars)

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")

\* END TRANSLATION
-----------------------------------------------------------------------------
(***************************************************************************)
(* Next comes the definition of the inductive invariant Inv.  Its          *)
(* invariance was checked by TLC for N = 4, and its inductive invariance   *)
(* was checked for N = 3 (with Int replaced by a set of 3 integers).       *)
(***************************************************************************)
TypeOK == /\ i \in 1..N
          /\ j \in 1..N
          /\ A \in [1..N -> Int]
          /\ A0 \in [1..N -> Int]
          /\ pc \in {"Lbl_1", "Lbl_2", "Done"}
          
RealInv ==
  /\ pc = "Lbl_1" => /\ IsSortedTo(A, i)
                     /\ IsPermOf(A, A0)
  /\ pc = "Lbl_2" => /\ j \in 1..(i+1)
                     /\ i < N
                     /\ IsSortedTo(A, j-1)
                     /\ IsSortedFromTo(A, j, i+1)
                     /\ \A p \in 1..(j-1), q \in (j+1)..(i+1) : A[p] =< A[q]
                     /\ IsPermOf(A, A0)
                     
  /\ pc = "Done" => IsSorted(A) /\ IsPermOf(A, A0)
  
Inv == TypeOK /\ RealInv
-----------------------------------------------------------------------------
(***************************************************************************)
(* Finally, we get to the theorem asserting correctness of the algorithm   *)
(* and its proof.                                                          *)
(***************************************************************************)
THEOREM Spec => [](pc = "Done" => IsSorted(A) /\ IsPermOf(A, A0))
<1> USE NAssumption DEF Inv
<1>1 Init => Inv
  BY IsPermOfReflexive DEF Init, TypeOK, RealInv, IsSortedTo
<1>2. Inv /\ [Next]_vars => Inv'  
  <2> SUFFICES ASSUME Inv, Lbl_1 \/ Lbl_2 \* Next
               PROVE  Inv'
    <3>1. Inv /\ UNCHANGED vars => Inv'
      BY DEF vars, TypeOK, RealInv, IsSorted, IsSortedTo, 
                IsSortedFromTo, IsPermOf, Perms, **
    <3>2. QED
      BY <3>1 DEF Next 
  <2>1. TypeOK'
    BY DEF TypeOK, RealInv, Lbl_1, Lbl_2 
  <2>2. RealInv'
    \* This part of the proof is left as a (difficult!) exercise
    \* for the reader.
  <2>3. QED
    BY <2>1, <2>2 
<1>3. Inv => (pc = "Done" => IsSorted(A) /\ IsPermOf(A, A0))
  BY DEF Inv, RealInv
<1>4. QED
    BY <1>1, <1>2, <1>3, PTL DEF Spec

-----------------------------------------------------------------------------
(***************************************************************************)
(* Except for writing the comments, writing this module, including         *)
(* checking the proofs, took about 6.5 hours.                              *)
(***************************************************************************)
=============================================================================
\* Modification History
\* Last modified Wed Aug 28 14:03:35 CEST 2019 by merz
\* Last modified Mon Mar 17 11:17:49 CET 2014 by doligez
\* Last modified Fri Mar 07 15:24:43 CET 2014 by shaolin
\* Last modified Tue Nov 27 13:33:10 CET 2012 by doligez
\* Last modified Fri Nov 23 09:32:08 PST 2012 by lamport
\* Created Wed Nov 21 11:50:58 PST 2012 by lamport
