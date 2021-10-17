------------------------- MODULE BagsTheorems_proofs -------------------------------
(**************************************************************************)
(* A bag, also called a multiset, is a set that can contain multiple      *)
(* copies of the same element.  A bag can have infinitely many elements,  *)
(* but only finitely many copies of any single element.                   *)
(*                                                                        *)
(* We represent a bag in the usual way as a function whose range is a     *)
(* subset of the positive integers.  An element e belongs to bag B iff e  *)
(* is in the domain of B, in which case bag B contains B[e] copies of e.  *)
(**************************************************************************)
EXTENDS TLC,
        Bags,
        FiniteSetTheorems,
        SequenceTheorems

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
BY DEF \sqsubseteq, IsABag

(*Antisymmetry*)
THEOREM Bags_SqsubseteqPO_AntiSymmetry ==
  ASSUME NEW A, NEW B, IsABag(A), IsABag(B),
         A \sqsubseteq B, B \sqsubseteq A
  PROVE A = B
BY DEF IsABag, \sqsubseteq

(*Transitivity*)
THEOREM Bags_SqsubseteqPO_Transitivity ==
  ASSUME NEW A, NEW B, NEW C, IsABag(A), IsABag(B), IsABag(C),
         A \sqsubseteq B, B \sqsubseteq C
  PROVE A \sqsubseteq C
BY DEF IsABag, \sqsubseteq

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
BY DEF EmptyBag, SetToBag, IsABag, \sqsubseteq, BagIn, BagToSet

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
<1>1. IsABag(Scaling(n, B))
  BY DEF IsABag, Scaling, EmptyBag, SetToBag
<1>2. Scaling(n, EmptyBag)=EmptyBag
  BY DEF IsABag, Scaling, EmptyBag, SetToBag
<1>3. Scaling(0, B)=EmptyBag
  BY DEF Scaling
<1>4. Scaling(1, B)= B
  BY DEF Scaling, IsABag
<1>5. Scaling(n*m, B) = Scaling(n, Scaling(m, B))
  <2>1. CASE m>0 /\ n>0
    BY <2>1, n*m > 0 DEF Scaling, IsABag
  <2>2. CASE m=0
    BY <2>2, <1>2, <1>3 DEF Scaling
  <2>3. CASE n=0
    BY <2>3 DEF Scaling
  <2>. QED  BY <2>1, <2>2, <2>3
<1>6. n>0 => DOMAIN Scaling(n, B)=DOMAIN B
  BY DEF Scaling
<1> QED  BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6

(***************************************************************************)
(* SetToBag and BagToSet are inverse of each other                         *)
(***************************************************************************)

THEOREM Bags_Inverse ==
  ASSUME NEW S
  PROVE  BagToSet(SetToBag(S))=S
BY DEF SetToBag, BagToSet

THEOREM Bags_Inverse1 ==
  ASSUME NEW B, IsABag(B)
  PROVE  SetToBag(BagToSet(B)) \sqsubseteq B
BY DEF SetToBag, BagToSet, \sqsubseteq, IsABag

(***************************************************************************)
(* SetToBag Preserves Equality                                             *)
(***************************************************************************)

THEOREM Bags_SetToBagEquality ==
  ASSUME NEW A, NEW B
  PROVE  A=B <=> SetToBag(A)=SetToBag(B)
BY DEF SetToBag

(***************************************************************************)
(* Union of Bags                                                           *)
(***************************************************************************)

THEOREM Bags_Union ==
  ASSUME NEW B1, NEW B2, IsABag(B1), IsABag(B2)
  PROVE  /\ IsABag(B1 (+) B2)
         /\ DOMAIN(B1 (+) B2) = DOMAIN B1 \cup DOMAIN B2
         /\ \A e : CopiesIn(e, B1(+)B2) = CopiesIn(e,B1) + CopiesIn(e,B2)
BY DEF IsABag, (+), CopiesIn, BagIn, BagToSet

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
BY DEF IsABag, (-), CopiesIn, BagIn, BagToSet

(***************************************************************************)
(* Union is commutative.                                                   *)
(***************************************************************************)

THEOREM Bags_UnionCommutative ==
  ASSUME NEW B1, NEW B2, IsABag(B1), IsABag(B2)
  PROVE  B1(+)B2 = B2(+)B1
BY DEF IsABag, (+)

(***************************************************************************)
(* Unon is associative.                                                    *)
(***************************************************************************)

THEOREM Bags_UnionAssociative ==
  ASSUME NEW B1, NEW B2, NEW B3, IsABag(B1), IsABag(B2), IsABag(B3)
  PROVE  (B1(+)B2) (+) B3 = B1 (+) (B2(+)B3)
BY DEF IsABag, (+)

(***************************************************************************)
(* Given Bags B1, B2 then B1 \sqsubseteq B1(+)B2                           *)
(***************************************************************************)

THEOREM Bags_UnionSqSubset ==
  ASSUME NEW B1, NEW B2, IsABag(B1), IsABag(B2)
  PROVE  B1 \sqsubseteq B1(+)B2
BY DEF IsABag, (+), \sqsubseteq

(***************************************************************************)
(* Scaling is monotonic in the scaling factor.                             *)
(***************************************************************************)

THEOREM Bags_ScalingMonotonic ==
  ASSUME NEW B, IsABag(B), NEW n \in Nat, NEW m \in Nat, m <= n
  PROVE  Scaling(m, B) \sqsubseteq Scaling(n, B)
BY CVC4 DEF IsABag, Scaling, EmptyBag, SetToBag, \sqsubseteq

(***************************************************************************)
(* Given Bags A and B, A(-)B \sqsubseteq A                                 *)
(***************************************************************************)

THEOREM Bags_DifferenceSqsubset ==
  ASSUME NEW A, NEW B, IsABag(A), IsABag(B)
  PROVE  A(-)B \sqsubseteq A
BY DEF IsABag, (-), \sqsubseteq

(***************************************************************************)
(* EmptyBag is the additive identity.                                      *)
(***************************************************************************)

THEOREM Bags_EmptyBagOperations ==
  ASSUME NEW B, IsABag(B)
  PROVE  /\ B (+) EmptyBag = B
         /\ B (-) EmptyBag = B
BY DEF IsABag, (+), (-), EmptyBag, SetToBag

(***************************************************************************)
(* SetToBag of a set is a bag.                                             *)
(***************************************************************************)

THEOREM Bags_SetToBagIsABag ==
  ASSUME NEW S
  PROVE  IsABag(SetToBag(S))
BY DEF IsABag, SetToBag

(***************************************************************************)
(* CopiesIn is monotone w.r.t \sqsubseteq                                  *)
(***************************************************************************)

THEOREM Bags_CopiesInBagsInMonotone ==
  ASSUME NEW B1, NEW B2, NEW e, IsABag(B1), IsABag(B2), B1 \sqsubseteq B2
  PROVE  /\ BagIn(e, B1) => BagIn(e, B2)
         /\ CopiesIn(e, B1) <= CopiesIn(e, B2)
BY DEF IsABag, BagIn, \sqsubseteq, BagToSet, CopiesIn

(***************************************************************************)
(* Given Bag B and Natural n, CopiesIn(e, Scaling(n, B))=n*CopiesIn(e, B)  *)
(***************************************************************************)

THEOREM Bags_CopiesInScaling ==
  ASSUME NEW B, IsABag(B), NEW n \in Nat, NEW e
  PROVE  CopiesIn(e, Scaling(n, B)) = n*CopiesIn(e, B)
BY DEF IsABag, Scaling, CopiesIn, BagIn, EmptyBag, SetToBag, BagToSet

(***************************************************************************)
(* Given set S, CopiesIn(e, SetToBag(S))=IF e \in B THEN 1 ELSE 0          *)
(***************************************************************************)

THEOREM Bags_CopiesInSetToBag ==
  ASSUME NEW B, NEW e
  PROVE  CopiesIn(e, SetToBag(B))=IF e \in B THEN 1 ELSE 0
BY DEF CopiesIn, SetToBag, BagToSet, BagIn

(***************************************************************************)
(* Given sequence seq, SeqToBag(seq) is a Bag                              *)
(***************************************************************************)

THEOREM Bags_IsABagSeqToBag ==
  ASSUME NEW S, NEW seq \in Seq(S)
  PROVE  IsABag(SeqToBag(seq))
<1>. DEFINE occs(x) == { i \in DOMAIN seq : seq[i] = x }
<1>1. ASSUME NEW x \in Range(seq)
      PROVE  Cardinality(occs(x)) \in Nat \ {0}
  <2>1. /\ IsFiniteSet(occs(x))
        /\ occs(x) # {}
    BY SeqDef, FS_Interval, FS_Subset DEF Range
  <2>. QED  BY <2>1, FS_CardinalityType, FS_EmptySet, Zenon
<1>. QED  BY <1>1 DEF IsABag, SeqToBag

=============================================================================
