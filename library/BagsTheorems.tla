---------------------------- MODULE BagsTheorems ---------------------------
(**************************************************************************)
(* A bag, also called a multiset, is a set that can contain multiple      *)
(* copies of the same element.  A bag can have infinitely many elements,  *)
(* but only finitely many copies of any single element.                   *)
(*                                                                        *)
(* We represent a bag in the usual way as a function whose range is a     *)
(* subset of the positive integers.  An element e belongs to bag B iff e  *)
(* is in the domain of B, in which case bag B contains B[e] copies of e.  *)
(**************************************************************************)
EXTENDS Bags
      
LOCAL INSTANCE Naturals

CopiesIn(e, B) ==
  (************************************************************************)
  (* If B is a bag, then CopiesIn(e, B) is the number of copies of e in   *)
  (* B. If ~BagIn(e, B), then CopiesIn(e, B) = 0.                         *)
  (************************************************************************)
  IF BagIn(e, B) THEN B[e] ELSE 0
  
Scaling(n, B) ==  
  (************************************************************************)
  (* If B is a bag, then Scaling(e, B) is the Bag containing the same     *)
  (* elements of B with n times their copies                              *)
  (************************************************************************)
  IF n>0 THEN [i \in DOMAIN B |-> n*B[i] ] ELSE EmptyBag 


(***************************************************************************)
(* Converts a sequence into a bag                                          *)
(***************************************************************************)

SeqToBag(seq) == [ x \in Range(seq) |-> Cardinality({i \in DOMAIN seq: seq[i]=x}) ]


(***************************************************************************)
(* \sqsubseteq is a PARTIAL ORDER relattion                                *)
(***************************************************************************)

(*Reflexivity*)
THEOREM Bags_SqsubsetPO_Reflexivity == 
  ASSUME NEW B, IsABag(B)
  PROVE B \sqsubseteq B

(*Antisymmetry*)
THEOREM Bags_SqsubseteqPO_AntiSymmetry == 
  ASSUME NEW A, NEW B, IsABag(A), IsABag(B),
         A \sqsubseteq B, B \sqsubseteq A  
  PROVE A = B

(*Transitivity*)            
THEOREM Bags_SqsubseteqPO_Transitivity == 
  ASSUME NEW A, NEW B, NEW C, IsABag(A), IsABag(B), IsABag(C),
         A \sqsubseteq B, B \sqsubseteq C
  PROVE A \sqsubseteq C

(***************************************************************************)
(* Lemmas on EmptyBags                                                     *)
(***************************************************************************)
    
THEOREM Bags_EmptyBag == 
  ASSUME NEW B, IsABag(B)
  PROVE  /\ IsABag(EmptyBag)
         /\ B=EmptyBag <=> DOMAIN B ={}
         /\ DOMAIN EmptyBag ={}
         /\ EmptyBag \sqsubseteq B
         /\ \A e: ~BagIn(e, EmptyBag)

(***************************************************************************)
(* Lemmas on Scaling Operator for Bags                                     *)
(***************************************************************************)

THEOREM Bags_Scaling == 
  ASSUME NEW B, IsABag(B), NEW n \in Nat, NEW m \in Nat
  PROVE /\ IsABag(Scaling(n, B)) 
        /\ Scaling(n, EmptyBag)=EmptyBag
        /\ Scaling(0, B)=EmptyBag
        /\ Scaling(1, B)= B
        /\ Scaling(n*m, B) = Scaling(n, Scaling(m, B))
        /\ n>0 => DOMAIN(Scaling(n, B)) = DOMAIN B

(***************************************************************************)
(* SetToBag and BagToSet are inverse of each other                         *)
(***************************************************************************)

THEOREM Bags_Inverse == 
  ASSUME NEW S
  PROVE  BagToSet(SetToBag(S))=S

THEOREM Bags_Inverse1 == 
  ASSUME NEW B, IsABag(B)
  PROVE  SetToBag(BagToSet(B)) \sqsubseteq B

(***************************************************************************)
(* SetToBag Preserves Equality                                             *)
(***************************************************************************)

THEOREM Bags_SetToBagEquality == 
  ASSUME NEW A, NEW B
  PROVE  A=B <=> SetToBag(A)=SetToBag(B)

(***************************************************************************)
(* Union of Bags                                                           *)
(***************************************************************************)

THEOREM Bags_Union == 
  ASSUME NEW B1, NEW B2, IsABag(B1), IsABag(B2)
  PROVE  /\ IsABag(B1 (+) B2)
         /\ DOMAIN(B1 (+) B2) = DOMAIN B1 \cup DOMAIN B2
         /\ \A e : CopiesIn(e, B1(+)B2) = CopiesIn(e,B1) + CopiesIn(e,B2)

(***************************************************************************)
(* Difference of Bags                                                      *)
(***************************************************************************)

THEOREM Bags_Difference == 
  ASSUME NEW B1, NEW B2, IsABag(B1), IsABag(B2)
  PROVE  /\ IsABag(B1 (-) B2)
         /\ DOMAIN (B1 (-) B2) =
               {e \in DOMAIN B1 : e \notin DOMAIN B2 \/ B1[e] > B2[e]}
         /\ \A e : CopiesIn(e, B1 (-) B2) =
                   IF BagIn(e, B1(-)B2) THEN CopiesIn(e,B1) - CopiesIn(e,B2)
                   ELSE 0

(***************************************************************************)
(* Union is commutative.                                                   *)
(***************************************************************************)

THEOREM Bags_UnionCommutative == 
  ASSUME NEW B1, NEW B2, IsABag(B1), IsABag(B2)
  PROVE  B1(+)B2 = B2(+)B1      

(***************************************************************************)
(* Unon is associative.                                                    *)
(***************************************************************************)                      
THEOREM Bags_UnionAssociative == 
  ASSUME NEW B1, NEW B2, NEW B3, IsABag(B1), IsABag(B2), IsABag(B3)
  PROVE  (B1(+)B2) (+) B3 = B1 (+) (B2(+)B3)

(***************************************************************************)
(* Given Bags B1, B2 then B1 \sqsubseteq B1(+)B2                           *)
(***************************************************************************)
      
THEOREM Bags_UnionSqSubset == 
  ASSUME NEW B1, NEW B2, IsABag(B1), IsABag(B2)
  PROVE  B1 \sqsubseteq B1(+)B2

(***************************************************************************)
(* Scaling is monotonic in the scaling factor.                             *)
(***************************************************************************)

THEOREM Bags_ScalingMonotonic == 
  ASSUME NEW B, IsABag(B), NEW n \in Nat, NEW m \in Nat, m <= n
  PROVE  Scaling(m, B) \sqsubseteq Scaling(n, B)

(***************************************************************************)
(* Given Bags A and B, A(-)B \sqsubseteq A                                 *)
(***************************************************************************)

THEOREM Bags_DifferenceSqsubset == 
  ASSUME NEW A, NEW B, IsABag(A), IsABag(B)
  PROVE  A(-)B \sqsubseteq A 

(***************************************************************************)
(* EmptyBag is the additive identity.                                      *)
(***************************************************************************)  

THEOREM Bags_EmptyBagOperations == 
  ASSUME NEW B, IsABag(B)
  PROVE  /\ B (+) EmptyBag = B
         /\ B (-) EmptyBag = B

(***************************************************************************)
(* SetToBag of a set is a bag.                                             *)
(***************************************************************************)      

THEOREM Bags_SetToBagIsABag == 
  ASSUME NEW S
  PROVE  IsABag(SetToBag(S))

(***************************************************************************)
(* CopiesIn is monotone w.r.t \sqsubseteq                                  *)
(***************************************************************************)
  
THEOREM Bags_CopiesInBagsInMonotone ==
  ASSUME NEW B1, NEW B2, NEW e, IsABag(B1), IsABag(B2), B1 \sqsubseteq B2 
  PROVE  /\ BagIn(e, B1) => BagIn(e, B2)
         /\ CopiesIn(e, B1) <= CopiesIn(e, B2)

(***************************************************************************)
(* Given Bag B and Natural n, CopiesIn(e, Scaling(n, B))=n*CopiesIn(e, B)  *)
(***************************************************************************)
      
THEOREM Bags_CopiesInScaling == 
  ASSUME NEW B, IsABag(B), NEW n \in Nat, NEW e
  PROVE  CopiesIn(e, Scaling(n, B)) = n*CopiesIn(e, B)

(***************************************************************************)
(* Given set S, CopiesIn(e, SetToBag(S))=IF e \in B THEN 1 ELSE 0          *)
(***************************************************************************)
 
THEOREM Bags_CopiesInSetToBag == 
  ASSUME NEW B, NEW e
  PROVE  CopiesIn(e, SetToBag(B))=IF e \in B THEN 1 ELSE 0

(***************************************************************************)
(* Given sequence seq, SeqToBag(seq) is a Bag                              *)
(***************************************************************************)

THEOREM Bags_IsABagSeqToBag ==
  ASSUME NEW S, NEW seq \in Seq(S)
  PROVE  IsABag(SeqToBag(seq))

=============================================================================
