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
(* Equality of bags via DOMAIN and CopiesIn.                               *)
(***************************************************************************)
THEOREM BagEquality ==
  ASSUME NEW B1, NEW B2, IsABag(B1), IsABag(B2),
         DOMAIN B1 = DOMAIN B2,
         \A e : CopiesIn(e, B1) = CopiesIn(e, B2)
  PROVE  B1 = B2
BY DEF IsABag, CopiesIn, BagIn, BagToSet
 
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
    <3>. \A i \in DOMAIN B : n * m * B[i] = n * (m * B[i])
      BY DEF IsABag
    <3>. QED  BY <2>1 DEF Scaling
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
<1>. DEFINE B == [e \in DOMAIN B1 |-> IF e \in DOMAIN B2 THEN B1[e] - B2[e]
                                                         ELSE B1[e]]
            D == {e \in DOMAIN B1 : B[e] > 0}
            R == [e \in D |-> B[e]]
<1>1. R = B1 (-) B2
  BY Zenon DEF (-)
<1>2. \A e \in DOMAIN R : R[e] \in Nat /\ R[e] > 0
  BY DEF IsABag
<1>3. DOMAIN R = {e \in DOMAIN B1 : e \notin DOMAIN B2 \/ B1[e] > B2[e]}
  BY DEF IsABag
<1>4. \A e : CopiesIn(e, R) =
                   IF BagIn(e, R) THEN CopiesIn(e,B1) - CopiesIn(e,B2)
                   ELSE 0
  BY DEF IsABag, BagIn, BagToSet, CopiesIn
<1>. HIDE DEF D
<1>5. IsABag(R)
  BY <1>2 DEF IsABag
<1>. QED  BY <1>1, <1>2, <1>3, <1>4, <1>5

(***************************************************************************)
(* Union is commutative.                                                   *)
(***************************************************************************)

THEOREM Bags_UnionCommutative ==
  ASSUME NEW B1, NEW B2, IsABag(B1), IsABag(B2)
  PROVE  B1(+)B2 = B2(+)B1
<1>. DEFINE D1 == DOMAIN B1   D2 == DOMAIN B2
            C1(e) == IF e \in D1 THEN B1[e] ELSE 0
            C2(e) == IF e \in D2 THEN B2[e] ELSE 0
<1>1. \A e : C1(e) \in Nat /\ C2(e) \in Nat
  BY DEF IsABag
<1>2. /\ B1 (+) B2 = [e \in D1 \union D2 |-> C1(e) + C2(e)]
      /\ B2 (+) B1 = [e \in D2 \union D1 |-> C2(e) + C1(e)]
  BY DEF (+)
<1>. HIDE DEF D1, D2, C1, C2
<1>. QED  BY <1>1, <1>2

(***************************************************************************)
(* Unon is associative.                                                    *)
(***************************************************************************)

THEOREM Bags_UnionAssociative ==
  ASSUME NEW B1, NEW B2, NEW B3, IsABag(B1), IsABag(B2), IsABag(B3)
  PROVE  (B1(+)B2) (+) B3 = B1 (+) (B2(+)B3)
<1>. DEFINE D1 == DOMAIN B1   D2 == DOMAIN B2   D3 == DOMAIN B3
            C1(e) == IF e \in D1 THEN B1[e] ELSE 0
            C2(e) == IF e \in D2 THEN B2[e] ELSE 0
            C3(e) == IF e \in D3 THEN B3[e] ELSE 0
<1>1. \A e : C1(e) \in Nat /\ C2(e) \in Nat /\ C3(e) \in Nat
  BY DEF IsABag
<1>2. /\ (B1 (+) B2) (+) B3 = 
         [e \in (D1 \union D2) \union D3 |-> (C1(e) + C2(e)) + C3(e)]
      /\ B1 (+) (B2 (+) B3) = 
         [e \in D1 \union (D2 \union D3) |-> C1(e) + (C2(e) + C3(e))]
  BY DEF (+)
<1>. HIDE DEF D1, D2, D3, C1, C2, C3
<1>3. \A e : (C1(e) + C2(e)) + C3(e) = C1(e) + (C2(e) + C3(e))
  BY <1>1
<1>. QED  BY <1>2, <1>3, Zenon


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
BY DEF IsABag, Scaling, EmptyBag, SetToBag, \sqsubseteq

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
<1>. DEFINE D == DOMAIN B  C(e) == IF e \in D THEN B[e] ELSE 0
<1>1. /\ \A e \in D : C(e) \in Nat /\ C(e) > 0
      /\ \A e : e \notin D => C(e) = 0
  BY DEF IsABag
<1>2. /\ B = [e \in D |-> C(e)]
      /\ EmptyBag = [e \in {} |-> 0]
  BY DEF IsABag, EmptyBag, SetToBag
<1>. HIDE DEF D, C
<1>3. B (+) EmptyBag = B
  BY <1>1, <1>2 DEF (+)
<1>4. B (-) EmptyBag = B
  BY <1>1, <1>2 DEF (-)
<1>. QED  BY <1>3, <1>4

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
  <2>1. occs(x) # {}
    BY DEF Range
  <2>2. IsFiniteSet(occs(x))
    BY FS_Interval, FS_Subset
  <2>. QED  BY <2>1, <2>2, FS_CardinalityType, FS_EmptySet, Zenon
<1>. QED  BY <1>1 DEF IsABag, SeqToBag

=============================================================================
