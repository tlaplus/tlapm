------------------------------- MODULE Euclid ------------------------------- 
(***************************************************************************)
(* This module specifies a version of Euclid's algorithm for computing the *)
(* greatest common divisor of two positive integers.                       *)
(***************************************************************************)
EXTENDS Integers, TLAPS

AXIOM SetExtensionality2 == \A S,T : (\A x : x \in S <=> x \in T) <=> S = T

CONSTANTS M, N  

ASSUME MNPosInt == /\ M \in Nat \ {0}
                   /\ N \in Nat \ {0}

VARIABLES x, y

TypeOK == /\ x \in Nat \ {0}
          /\ y \in Nat \ {0}
          
Init == (x = M)  /\  (y = N)

Next == \/ /\ x > y
           /\ x' = x - y
           /\ y' = y       
        \/ /\ y > x
           /\ y' = y - x
           /\ x' = x

\* Spec == Init /\ [][Next]_<<x, y>>
-----------------------------------------------------------------------------
(***************************************************************************)
(* We now define GCD(m, n) to be the greatest common divisor of m and n,   *)
(* if m and n are positive integers.  This requires some preliminary       *)
(* definitions.                                                            *)
(***************************************************************************)
Divides(p, n) == \E q \in 0..n : n = q * p       
  (*************************************************************************)
  (* True iff p divides n, for positive integers p and n.                  *)
  (*************************************************************************)
  
DivisorsOf(n) == {p \in 0..n : Divides(p, n)}  
  (*************************************************************************)
  (* The set of divisors of the positive integer n.                        *)
  (*************************************************************************)

Max(S) ==  CHOOSE i \in S : \A j \in S : i >= j
  (*************************************************************************)
  (* The maximum of a non-empty, bounded set S of integers.                *)
  (*************************************************************************)
  
GCD(m, n) == Max(DivisorsOf(m) \cap DivisorsOf(n)) 
-----------------------------------------------------------------------------
GCDInv == GCD(x, y) = GCD(M, N)

Inv == TypeOK /\ GCDInv

Safe == (x = y) => (x = GCD(M, N))
-----------------------------------------------------------------------------

(***************************************************************************)
(* Here are three simple facts about GCD that imply the correctness of     *)
(* Euclid's algorithm, and from which the algorithm can be derived.        *)
(***************************************************************************)
THEOREM GCD1 == \A m \in Nat \ {0} : GCD(m, m) = m
  BY SMT DEF GCD, Max 

THEOREM GCD2 == \A m, n \in Nat \ {0} : GCD(m, n) = GCD(n, m)
  BY SetExtensionality2, SMT DEF GCD 

THEOREM GCD3 == \A m, n \in Nat \ {0} : (n > m) => (GCD(m, n) = GCD(m, n-m))
  PROOF OMITTED

THEOREM GCD4 == \A m, n \in Nat \ {0} : GCD(m, n) \in Nat
<1>1. \A m : DivisorsOf(m) \subseteq Nat
  BY SMT DEF DivisorsOf
<1>3. \A S : S \subseteq Nat => Max(S) \in Nat
  (** S should be a finite set *)
<1>q. QED
  BY <1>1, <1>3, SMT DEF GCD 

THEOREM /\ Init => Inv
        /\ Inv /\ Next => Inv'
        /\ Inv => Safe       
  BY GCD1, GCD2, GCD3, GCD4, MNPosInt, Z3    \* CVC3T(30) fails  
  DEF Safe, Inv, TypeOK, GCDInv, Next, Init

\* ==================

THEOREM /\ Init => Inv
        /\ Inv /\ Next => Inv'
        /\ Inv => Safe       
<1>1. Init => Inv
  BY MNPosInt, SMT DEF Init, Inv, TypeOK, GCDInv
<1>2. Inv /\ Next => Inv'
  BY GCD2, GCD3, SMT DEF Inv, TypeOK, GCDInv, Next
<1>3. Inv => Safe
  BY GCD1, GCD4, MNPosInt, SMT  DEF Inv, Safe, TypeOK, GCDInv  
<1>4. QED
  BY <1>1, <1>2, <1>3, SMT DEF Inv
    
=============================================================================
\* Generated at Fri Nov 27 18:04:03 PST 2009
\* Modification History
\* Last modified Wed Nov 21 14:27:52 CET 2012 by hernanv
\* Last modified Thu May 03 15:11:10 PDT 2012 by lamport
