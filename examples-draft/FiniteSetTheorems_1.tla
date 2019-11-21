------------------------- MODULE FiniteSetTheorems --------------------------
(***************************************************************************)
(* `^{\large\bf \vspace{12pt}                                              *)
(*  Facts about finite sets.                                               *)
(*  \vspace{12pt}}^'                                                       *)
(***************************************************************************)

EXTENDS
  FiniteSets,
  Naturals,
  Integers,
  Sequences,
  Jections,
  WellFoundedInduction,
  SequencesTheorems,
  JectionThm,
  TLAPS

THEOREM FiniteSetThm_IsFiniteSetDef ==
  \A S :
    IsFiniteSet(S) =
    \E Q \in Seq(S) : \A s \in S : \E i \in 1..Len(Q) : Q[i] = s
BY DEF IsFiniteSet



(***************************************************************************)
(* `.  .'                                                                  *)
(*                                                                         *)
(* The empty set is finite.                                                *)
(*                                                                         *)
(* `.  .'                                                                  *)
(***************************************************************************)
THEOREM FiniteSetThm_Empty ==
  IsFiniteSet({})
PROOF
  <1> DEFINE Q == << >>
  <1>1. Q \in Seq({})  BY EmptySeq
  <1>2. \A s \in {} : \E i \in 1..Len(Q) : Q[i] = s  OBVIOUS
  <1> QED BY <1>1, <1>2, FiniteSetThm_IsFiniteSetDef






(***************************************************************************)
(* `.  .'                                                                  *)
(*                                                                         *)
(* A set S is finite iff there exists a natural number n such that there   *)
(* exist a surjection from 1..n to S.                                      *)
(*                                                                         *)
(* `.  .'                                                                  *)
(***************************************************************************)
THEOREM FiniteSetThm_NatSurjection ==
  ASSUME
    NEW S
  PROVE
  IsFiniteSet(S) <=> \E n \in Nat : Surjection(1..n,S) # {}
PROOF
  <1>1. ASSUME IsFiniteSet(S)  PROVE \E n \in Nat : Surjection(1..n,S) # {}
    <2>1. PICK Q \in Seq(S) : \A s \in S : \E i \in 1..Len(Q) : Q[i] = s
          BY <1>1, FiniteSetThm_IsFiniteSetDef
    <2>2. Q \in [1..Len(Q) -> S]  BY LenProperties
    <2>3. Q \in Surjection(1..Len(Q),S)  BY <2>1, <2>2  DEF Surjection
    <2>4. Len(Q) \in Nat  BY <2>1, LenProperties
    <2> QED BY <2>3, <2>4

  <1>2. ASSUME NEW n \in Nat, Surjection(1..n,S) # {}  PROVE  IsFiniteSet(S)
    <2>1. PICK Q \in [1..n -> S] : \A s \in S : \E i \in 1..n : Q[i] = s
          BY <1>2  DEF Surjection
    <2>2. Q \in Seq(S)  BY <2>1, SMT\*, SeqDef\*, SeqThm_SeqWhenFunc
    <2>3. Len(Q) = n  BY <2>1, <2>2, LenProperties, SMT\*, SeqThm_LenFromFunc
    <2> QED BY <2>1, <2>2, <2>3, FiniteSetThm_IsFiniteSetDef

  <1> QED BY <1>1, <1>2




(***************************************************************************)
(* `.  .'                                                                  *)
(*                                                                         *)
(* A set S is finite iff there exists a natural number n such that there   *)
(* exists a bijection from 1..n to S.                                      *)
(*                                                                         *)
(* `.  .'                                                                  *)
(***************************************************************************)
THEOREM FiniteSetThm_NatBijection ==
  ASSUME
    NEW S
  PROVE
  IsFiniteSet(S) <=> \E n \in Nat : ExistsBijection(1..n,S)
PROOF
  <1>1. ASSUME IsFiniteSet(S)  PROVE \E n \in Nat : Bijection(1..n,S) # {}
    (***********************************************************************)
    (* QQ is all sequences that are surjective to S.                       *)
    (***********************************************************************)
    <2>1. PICK QQ : QQ = {Q \in Seq(S) : \A s \in S : \E i \in 1..Len(Q) : Q[i] = s}  OBVIOUS
    <2>2. QQ # {}  BY <1>1, <2>1, FiniteSetThm_IsFiniteSetDef
    <2>3. PICK NN \in SUBSET Nat : NN = {Len(Q) : Q \in QQ}  BY <2>1, LenProperties 
    <2>4. NN # {}  BY <2>2, <2>3
    (***********************************************************************)
    (* Pick n as smallest in NN and Q as a shortest in QQ.                 *)
    (***********************************************************************)
    <2>5. PICK n \in NN : \A m \in NN : n \leq m  \*BY <2>4, NatLessThanWellFounded 
    <2>6. PICK Q \in QQ : Len(Q) = n  BY <2>3
    <2>7. Q \in [1..n -> S]  BY <2>1, <2>6, LenProperties
    <2>8. Q \in Surjection(1..n,S)  BY <2>1, <2>6, <2>7  DEF Surjection
    <2>10. ASSUME Q \notin Injection(1..n,S)  PROVE FALSE
      (*********************************************************************)
      (* With this assumption, we can pick i < j such that Q[i] = Q[j].    *)
      (*********************************************************************)
      <3>1. PICK i,j \in 1..n : i < j /\ Q[i] = Q[j]
        <4>1. PICK i,j \in 1..n : i # j /\ Q[i] = Q[j]  BY <2>7, <2>10  DEF Injection
        <4>2. CASE i < j  BY <4>1, <4>2
        <4>3. CASE j < i  BY <4>1, <4>3
        <4> QED BY <4>1, <4>2, <4>3, SMT
      (*********************************************************************)
      (* Construct P shorter than Q but still surjective to S.             *)
      (*********************************************************************)
      <3> DEFINE m == n-1
      <3>3. m \in Nat  BY <3>1, SMT
      <3>4. PICK P : P = [k \in 1..m |-> IF k = j THEN Q[n] ELSE Q[k]]  OBVIOUS
      <3>5. P \in [1..m -> S]  BY <3>4, <2>7, SMT
      <3>6. P \in Seq(S)  BY <3>3, <3>5, SMT\*, SeqDef
      <3>7. Len(P) = m  BY <3>3, <3>5, <3>6, LenProperties, SMT
     (**********************************************************************)
     (* Case analysis showing where to find any element of S on P.         *)
     (**********************************************************************)
      <3>8. ASSUME NEW s \in S  PROVE \E k \in 1..m : P[k] = s
        <4>1. PICK k \in 1..n : Q[k] = s  BY <2>1, <2>6
        <4>2. CASE k = j
          <5>1. i \in 1..m  BY <3>1, SMT
          <5>2. P[i] = s  BY <4>1, <4>2, <3>1, <3>4, SMT
          <5> QED BY <5>1, <5>2
        <4>3. CASE k # j /\ k = n
          <5>1. j \in 1..m  BY <4>3, SMT
          <5>2. P[j] = s  BY <4>1, <4>3, <3>4, SMT
          <5> QED BY <5>1, <5>2
        <4>4. CASE k # j /\ k # n
          <5>1. k \in 1..m  BY <4>4, SMT
          <5>2. P[k] = s  BY <4>1, <4>4, <3>4, SMT
          <5> QED BY <5>1, <5>2
        <4> QED BY <4>2, <4>3, <4>4
      (*********************************************************************)
      (* Hence P \in QQ and m \in NN, which is impossible, since m < n.    *)
      (*********************************************************************)
      <3>9. P \in QQ BY <3>6, <3>7, <3>8, <2>1
      <3>10. m \in NN  BY <3>7, <3>9, <2>3
      <3> QED BY <3>10, <2>5, SMT
    <2> QED BY <2>8, <2>10  DEF Bijection

  <1>2. ASSUME NEW n \in Nat, Bijection(1..n,S) # {}  PROVE  IsFiniteSet(S)
    <2>1. PICK Q : Q \in Surjection(1..n,S)  BY <1>2  DEF Bijection
    <2>2. Q \in [1..n -> S]  BY <2>1  DEF Surjection
    <2>3. \A s \in S : \E i \in 1..n : Q[i] = s  BY <2>1  DEF Surjection
    <2>4. Q \in Seq(S)  BY <2>2, <2>3, SMT\*, SeqDef
    <2>5. Len(Q) = n  BY <2>2, <2>4, LenProperties, SMT
    <2> QED BY <2>3, <2>4, <2>5, FiniteSetThm_IsFiniteSetDef

  <1> QED BY <1>1, <1>2, JectionThm_ExistsBij





(***************************************************************************)
(* `.  .'                                                                  *)
(*                                                                         *)
(* A singleton set is finite.                                              *)
(*                                                                         *)
(* `.  .'                                                                  *)
(***************************************************************************)
THEOREM FiniteSetThm_Singleton ==
  ASSUME NEW s0
  PROVE IsFiniteSet({s0})
PROOF
  <1> DEFINE Q == << s0 >>
  <1> DEFINE LenQ == Len(Q)
  <1>1. LenQ = 1  OBVIOUS
  <1>2. Q \in Seq({s0})  BY (*SeqDef,*) SMT 
  <1>3. \A s \in {s0} : \E i \in 1..LenQ : Q[i] = s
    <2> SUFFICES \E i \in 1..LenQ : Q[i] = s0  OBVIOUS
    <2>1. 1 \in 1..LenQ
      <3> HIDE DEF LenQ
      <3> QED BY <1>1, SMT
    <2>2. Q[1] = s0  OBVIOUS
    <2> QED BY <2>1, <2>2
  <1> QED BY <1>2, <1>3, FiniteSetThm_IsFiniteSetDef





(***************************************************************************)
(* `.  .'                                                                  *)
(*                                                                         *)
(* Any subset of a finite set is finite.                                   *)
(*                                                                         *)
(* `.  .'                                                                  *)
(***************************************************************************)
THEOREM FiniteSetThm_Subset ==
  ASSUME
    NEW S, IsFiniteSet(S),
    NEW T \in SUBSET S
  PROVE IsFiniteSet(T)
<1>1. CASE T # {}
  BY <1>1, FiniteSetThm_NatSurjection, JectionThm_ExistsSurjSubset DEF ExistsSurjection
<1>. QED
  BY <1>1, FiniteSetThm_Empty




(***************************************************************************)
(* `.  .'                                                                  *)
(*                                                                         *)
(* The union of two finite sets is finite.                                 *)
(*                                                                         *)
(* `.  .'                                                                  *)
(***************************************************************************)
THEOREM FiniteSetThm_Union ==
  ASSUME
    NEW S1, IsFiniteSet(S1),
    NEW S2, IsFiniteSet(S2)
  PROVE IsFiniteSet(S1 \cup S2)
PROOF
  (*************************************************************************)
  (* Since S1 is finite, we can pick a Q1 \in Seq(S1) on which each        *)
  (* element of S1 appears.                                                *)
  (*************************************************************************)
  <1>1. PICK Q1 \in Seq(S1) : \A s \in S1 : \E i \in 1..Len(Q1) : Q1[i] = s
        BY FiniteSetThm_IsFiniteSetDef
  <1>2. Len(Q1) \in Nat  BY LenProperties
  <1>3. Q1 \in [1..Len(Q1) -> S1]  BY LenProperties(*SeqThm_SeqIsFunc*)
  (*************************************************************************)
  (* Since S2 is finite, we can pick a Q2 \in Seq(S2) on which each        *)
  (* element of S2 appears.                                                *)
  (*************************************************************************)
  <1>4. PICK Q2 \in Seq(S2) : \A s \in S2 : \E i \in 1..Len(Q2) : Q2[i] = s
        BY FiniteSetThm_IsFiniteSetDef, ZenonT(20)
  <1>5. Len(Q2) \in Nat  BY LenProperties(*SeqThm_LenType*), ZenonT(20)
  <1>6. Q2 \in [1..Len(Q2) -> S2]  BY LenProperties(*SeqThm_SeqIsFunc*)
  (*************************************************************************)
  (* From Q1 and Q2 construct a sequence Q \in Seq(S1 \cup S2) on which    *)
  (* each element of S1 \cup S2 appears.                                   *)
  (*************************************************************************)
  <1> DEFINE S == S1 \cup S2
  <1> DEFINE n == Len(Q1) + Len(Q2)
  <1>7. n \in Nat  BY <1>2, <1>5, SMTT(20)
  <1>8. PICK Q :
        Q = [i \in 1..n |-> IF i \leq Len(Q1) THEN Q1[i] ELSE Q2[i - Len(Q1)]]
        OBVIOUS
  <1>9. Q \in [1..n -> S]
    <2>1. ASSUME NEW i \in 1..n  PROVE Q[i] \in S
      <3>1. CASE i \leq Len(Q1)
        <4>1. Q[i] = Q1[i]  BY <3>1, <1>8
        <4>2. i \in 1..Len(Q1)  BY <3>1, <1>2, <1>5, SMT
        <4>3. Q1[i] \in S1  BY <4>2, <1>3
        <4> QED BY <4>1, <4>3
      <3>2. CASE ~(i \leq Len(Q1))
        <4>1. Q[i] = Q2[i - Len(Q1)]  BY <3>2, <1>8, SMT
        <4>2. i - Len(Q1) \in 1..Len(Q2)  BY <3>2, <1>2, <1>5, SMT
        <4>3. Q2[i - Len(Q1)] \in S2  BY <4>2, <1>6
        <4> QED BY <4>1, <4>3
      <3> QED BY <3>1, <3>2
    <2> QED BY <2>1, <1>8
  <1>10. Q \in Seq(S)  BY <1>7, <1>9, LenProperties, SMT(*SeqThm_SeqWhenFunc*)
  <1>11. Len(Q) = n  BY <1>7, <1>9, LenProperties, SMT(*SeqThm_LenFromFunc*)
  (*************************************************************************)
  (* Prove that each element of S appears on Q.                            *)
  (*************************************************************************)
  <1>12. \A s \in S : \E i \in 1..Len(Q) : Q[i] = s
    <2> SUFFICES ASSUME NEW s \in S  PROVE \E i \in 1..n : Q[i] = s  BY <1>11
    <2>1. CASE s \in S1
      <3>1. PICK i1 \in 1..Len(Q1) : Q1[i1] = s  BY <2>1, <1>1
      <3>2. i1 \leq Len(Q1)  BY <1>2, SMT
      <3>3. i1 \in 1..n  BY <1>2, <1>5, SMT
      <3>4. Q[i1] = s  BY <3>1, <3>2, <3>3, <1>8
      <3> QED BY <3>3, <3>4
    <2>2. CASE s \in S2
      <3>1. PICK i2 \in 1..Len(Q2) : Q2[i2] = s  BY <2>2, <1>4
      <3>2. ~(i2 + Len(Q1) \leq Len(Q1))  BY <1>2, <1>5, SMT
      <3>3. i2 + Len(Q1) \in 1..n  BY <1>2, <1>5, SMT
      <3>4. Q[i2 + Len(Q1)] = s
        <4>1. (i2 + Len(Q1)) - Len(Q1) = i2  BY <1>2, <1>5, SMT
        <4>2. Q[i2 + Len(Q1)] = Q2[i2]  BY <4>1, <3>2, <3>3, <1>8
        <4> QED BY <4>2, <3>1
      <3> QED BY <3>3, <3>4
    <2> QED BY <2>1, <2>2, ZenonT(20)
  <1> QED BY <1>10, <1>12, FiniteSetThm_IsFiniteSetDef



(***************************************************************************)
(* `.  .'                                                                  *)
(*                                                                         *)
(* The intersection of a finite set with an arbitrary set is finite.       *)
(*                                                                         *)
(* `.  .'                                                                  *)
(***************************************************************************)
  

THEOREM FiniteSetThm_Intersection == 
  ASSUME NEW A, IsFiniteSet(A), NEW B
  PROVE  /\ IsFiniteSet(A \cap B)
         /\ IsFiniteSet(B \cap A) 
BY FiniteSetThm_Subset



(***************************************************************************)
(* `.  .'                                                                  *)
(*                                                                         *)
(* The difference between a finite set and an arbitrary set is finite.     *)
(*                                                                         *)
(* `.  .'                                                                  *)
(***************************************************************************)
  

THEOREM FiniteSetThm_Difference == 
  ASSUME NEW A, IsFiniteSet(A), NEW B
  PROVE  IsFiniteSet(A \ B)
BY FiniteSetThm_Subset



(***************************************************************************)
(* `.  .'                                                                  *)
(*                                                                         *)
(* The crossproduct of two finite sets is finite.                          *)
(*                                                                         *)
(* We prove this via surjection.  Since S1 is finite, there must exist a   *)
(* surjection M1 from 1..n1 to S1 for some n1 \in Nat.  Since S2 is        *)
(* finite, there must exist a surjection M2 from 1..n2 to S2 for some n2   *)
(* \in Nat.  From these two surjections we construct a surjection from     *)
(* 1..(n1*n2) to (S1 \X S2), which proves that S1 \X S2 is finite.         *)
(*                                                                         *)
(* `.  .'                                                                  *)
(***************************************************************************)
(* Some trivial properties of Modulus Operator which will be used in 
following proof are assumed as axioms for the time being *)
AXIOM ModDistrPlus == \A a,b,c \in Nat : (a+b)%c =( (a%c) + (b%c) )
AXIOM ModProp == \A a,b \in Nat : (a*b)%b = 0

THEOREM FiniteSetThm_Crossproduct ==
  ASSUME
    NEW S1, IsFiniteSet(S1),
    NEW S2, IsFiniteSet(S2)
  PROVE IsFiniteSet(S1 \X S2)
PROOF
  <1>1. PICK n1 \in Nat : Surjection(1..n1,S1) # {}  BY FiniteSetThm_NatSurjection
  <1>2. PICK n2 \in Nat : Surjection(1..n2,S2) # {}  BY FiniteSetThm_NatSurjection

  <1>3. PICK M1 : M1 \in Surjection(1..n1,S1)  BY <1>1
  <1>4. PICK M2 : M2 \in Surjection(1..n2,S2)  BY <1>2
  
  <1> HIDE DEF JectionThm_SurjProp_Qed
  <1>5. JectionThm_SurjProp_Qed(1..n1,S1,M1)  BY <1>3, JectionThm_SurjProp
  <1>6. JectionThm_SurjProp_Qed(1..n2,S2,M2)  BY <1>4, JectionThm_SurjProp
  <1> USE DEF JectionThm_SurjProp_Qed
  
  (*************************************************************************)
  (* Construct the crossproduct set S3 and the surjection M3.  We use      *)
  (* standard row and column indexing to convert indexes in 1..n3 into a   *)
  (* row index in 1..n1 and a column index in 1..n2.                       *)
  (*************************************************************************)
  <1>7. PICK S3 : S3 = S1 \X S2  OBVIOUS
  <1>8. PICK n3 \in Nat : n3 = n1*n2  BY SMT
  <1>9. PICK M3 : M3 =
         [ i \in 1..n3 |->
           LET
             i1 == ((i-1) % n1) + 1
             i2 == ((i-1) \div n1) + 1
           IN
           << M1[i1],M2[i2] >>
         ]
        OBVIOUS

  (*************************************************************************)
  (* M3 is a function from 1..n3 to S3.                                    *)
  (*************************************************************************)
  <1>10. M3 \in [1..n3 -> S3]
    <2> SUFFICES ASSUME NEW i \in 1..n3  PROVE M3[i] \in S3  BY <1>9
    <2>1. M1 \in [1..n1 -> S1]  BY <1>5
    <2>2. M2 \in [1..n2 -> S2]  BY <1>6
    <2> DEFINE
        i1 == ((i-1) % n1) + 1
        i2 == ((i-1) \div n1) + 1
    <2>3. i1 \in 1..n1  BY <1>8, Z3T(60)
    <2>4. i2 \in 1..n2  BY <1>8, Z3T(60)
    <2>5. M1[i1] \in S1  BY <2>1, <2>3
    <2>6. M2[i2] \in S2  BY <2>2, <2>4
    <2> QED BY <2>5, <2>6, <1>7, <1>9
    
  (*************************************************************************)
  (* M3 is surjective.                                                     *)
  (*************************************************************************)
  <1>11. ASSUME NEW s3 \in S3  PROVE \E i \in 1..n3 : M3[i] = s3
    <2>1. \A s1 \in S1 : \E i \in 1..n1 : M1[i] = s1  BY <1>5
    <2>2. \A s2 \in S2 : \E i \in 1..n2 : M2[i] = s2  BY <1>6
    <2>3. PICK s1 \in S1, s2 \in S2 : s3 = <<s1,s2>>  BY <1>7, Isa
    <2>4. PICK i1 \in 1..n1 : M1[i1] = s1  BY <2>1
    <2>5. PICK i2 \in 1..n2 : M2[i2] = s2  BY <2>2
    <2>6. PICK i3 \in Nat : i3 = i1 + (i2-1)*n1  BY SMT
    <2>7. i3 \in 1..n3
      <3>1. 1 \leq i3  BY <2>6, <1>1, <1>2, SMT
      <3>2. (i2-1)*n1 \leq (n2-1)*n1  BY <1>1, <1>2, SMT
      <3>3. i3 \leq n3  BY <3>2, <2>6, <1>1, <1>2, <1>8, SMT
      <3> QED BY <3>1, <3>3, SMT
    <2>21. i1 \in 1..n1 /\ i2 \in 1..n2
         BY <2>4, <2>5
    <2>8. i1 = ((i3-1) % n1) + 1  
          <3>1. ((i3-1) % n1) + 1 = (((i1-1) + (i2-1)*n1 )%n1) +1
                BY <2>6, SMT
          <3>2.  i1-1 \in Nat /\ (i2-1)*n1 \in Nat /\ n1 \in Nat /\ i2-1 \in Nat
                BY SMT, <2>4, <2>5, <1>1
          <3>3. (((i1-1) + (i2-1)*n1 )%n1)  =  ((i1-1)%n1) +  (((i2-1)*n1)%n1) 
                BY  ModDistrPlus, <3>2   
          <3>4. (((i2-1)*n1)%n1) = 0
                BY <3>2, ModProp     
          <3>5. (i1-1)%n1 = i1-1
                BY <2>4, Z3
          <3>6. QED  
                BY <3>1, <3>3, <3>4, <3>5, Z3     
    <2>9. i2 = ((i3-1) \div n1) + 1  \* BY <2>6, SMT 
          <3>. QED
    <2>10. M3[i3] = <<M1[i1],M2[i2]>>  BY <2>7, <2>8, <2>9, <1>9
    <2> QED BY <2>3, <2>4, <2>5, <2>7, <2>10
 
  <1>12. M3 \in Surjection(1..n3,S3)  BY <1>10, <1>11, JectionThm_IsSurj
  <1> QED BY <1>7, <1>12, FiniteSetThm_NatSurjection





(***************************************************************************)
(* `.  .'                                                                  *)
(*                                                                         *)
(* The powerset of a finite set is finite.                                 *)
(*                                                                         *)
(* `.  .'                                                                  *)
(***************************************************************************)
THEOREM FiniteSetThm_Powerset ==
  ASSUME
    NEW S, IsFiniteSet(S)
  PROVE IsFiniteSet(SUBSET S)
PROOF
  (*************************************************************************)
  (* We proceed by induction on the size of S.                             *)
  (*************************************************************************)
  <1> DEFINE
    (***********************************************************************)
    (* Size of a bijection to T.  When T is finite, there is exactly one   *)
    (* natural i that will satisfy this predicate (but we do not need to   *)
    (* establish this uniqueness).                                         *)
    (***********************************************************************)
    Size(T,i) == IsFiniteSet(T) /\ ExistsBijection(1..i,T)
    
    (***********************************************************************)
    (* Inductive property.                                                 *)
    (***********************************************************************)
    Prop(i) == \A S1 : Size(S1,i) => IsFiniteSet(SUBSET S1)
               
  <1>1. \A i \in Nat : Prop(i)
    (***********************************************************************)
    (* Base case.                                                          *)
    (***********************************************************************)
    <2>1. Prop(0)
      <3>1. SUFFICES ASSUME NEW S1, Size(S1,0)  PROVE IsFiniteSet(SUBSET S1)
            OBVIOUS
      <3>2. Bijection(1..0,S1) # {}  BY <3>1, JectionThm_ExistsBij
      <3>3. PICK M1 : M1 \in Bijection(1..0,S1)  BY <3>1, <3>2
      
      <3> HIDE DEF JectionThm_BijProp_Qed
      <3>4. JectionThm_BijProp_Qed(1..0,S1,M1)  BY <3>3, JectionThm_BijProp
      <3> USE DEF JectionThm_BijProp_Qed
      
      <3>5. M1 \in [1..0 -> S1]  BY <3>4
      <3>6. \A s \in S1 : \E a \in 1..0 : M1[a] = s  BY <3>4
      <3>7. 1..0 = {}  BY SMT
      <3>8. S1 = {}  BY <3>6, <3>7
      <3>9. SUBSET S1 = {{}}  BY <3>8
      <3> QED BY <3>9, FiniteSetThm_Singleton
    
    (***********************************************************************)
    (* Inductive case.                                                     *)
    (***********************************************************************)
    <2>2. ASSUME NEW i \in Nat, Prop(i)  PROVE Prop(i+1)
      <3> DEFINE j == i+1
      <3>1. SUFFICES ASSUME NEW S1, Size(S1,j)  PROVE IsFiniteSet(SUBSET S1)
            OBVIOUS
      (*********************************************************************)
      (* Since S1 is finite, we can pick a bijection M1 from 1..j to S1.   *)
      (*********************************************************************)
      <3>2. Bijection(1..j,S1) # {}  BY <3>1, JectionThm_ExistsBij
      <3>3. PICK M1 : M1 \in Bijection(1..j,S1)  BY <3>1, <3>2
      
      <3> HIDE DEF JectionThm_BijProp_Qed
      <3>4. JectionThm_BijProp_Qed(1..j,S1,M1)  BY <3>3, JectionThm_BijProp
      <3> USE DEF JectionThm_BijProp_Qed
      
      <3>5. M1 \in [1..j -> S1]  BY <3>4
      <3>6. \A s \in S1 : \E a \in 1..j : M1[a] = s  BY <3>4
      <3>7. \A a,b \in 1..j : M1[a] = M1[b] => a = b  BY <3>4
      
      (*********************************************************************)
      (* Construct a smaller set S2 by removing M1[j] from S1.  S2 is      *)
      (* finite and from M1 we construct a bijection M2 from 1..i to S2.   *)
      (*********************************************************************)
      <3>8. M1[j] \in S1  BY <3>5, SMT
      <3>9. PICK S2 : S2 = S1 \ {M1[j]}  OBVIOUS
      <3>10. IsFiniteSet(S2)  BY <3>1, <3>8, <3>9, FiniteSetThm_Subset
      <3>11. PICK M2 : M2 = [a \in 1..i |-> M1[a]]  OBVIOUS
      <3>12. M2 \in [1..i -> S2]
        <4> SUFFICES ASSUME NEW a \in 1..i  PROVE M2[a] \in S2  BY <3>11
        <4>1. M2[a] = M1[a]  BY <3>11
        <4>2. M1[a] # M1[j]  BY <3>7, SMT
        <4>3. M1[a] \in S1  BY <3>5, SMT
        <4> QED BY <4>1, <4>2, <4>3, <3>9 
      <3>13. ASSUME NEW s \in S2  PROVE \E a \in 1..i : M2[a] = s
        <4>1. s \in S1  BY <3>9
        <4>2. PICK a \in 1..j : M1[a] = s  BY <4>1, <3>6
        <4>3. s # M1[j]  BY <3>9
        <4>4. a # j  BY <4>2, <4>3, <3>7
        <4>5. a \in 1..i  BY <4>4, SMT
        <4> QED BY <4>2, <4>5, <3>11
      <3>14. ASSUME NEW a \in 1..i, NEW b \in 1..i, M2[a] = M2[b]  PROVE a = b
        <4>1. M1[a] = M1[b]  BY <3>11, <3>14
        <4>2. a \in 1..j  BY SMT
        <4>3. b \in 1..j  BY SMT 
        <4> QED BY <4>1, <4>2, <4>3, <3>7
      <3>15. M2 \in Bijection(1..i,S2)  BY <3>12, <3>13, <3>14, JectionThm_IsBij
      
      (*********************************************************************)
      (* Apply the inductive hypothesis to establish SUBSET S2 is finite.  *)
      (* Hence we can pick a surjection N2 from 1..n2 to SUBSET S2.        *)
      (*********************************************************************)
      <3>16. IsFiniteSet(SUBSET S2)  BY <3>10, <3>15, <2>2, JectionThm_ExistsBij
      <3>17. PICK n2 \in Nat : Surjection(1..n2,SUBSET S2) # {}  BY <3>16, FiniteSetThm_NatSurjection
      <3>18. PICK N2 : N2 \in Surjection(1..n2,SUBSET S2)  BY <3>17
      
      <3> HIDE DEF JectionThm_SurjProp_Qed
      <3>19. JectionThm_SurjProp_Qed(1..n2,SUBSET S2,N2)  BY <3>18, JectionThm_SurjProp
      <3> USE DEF JectionThm_SurjProp_Qed

      <3>20. N2 \in [1..n2 -> SUBSET S2]  BY <3>19
      <3>21. \A s \in SUBSET S2 : \E a \in 1..n2 : N2[a] = s  BY <3>19 

      (*********************************************************************)
      (* From N2 we can construct a surjection N1 from 1..n1 to SUBSET S1. *)
      (* This proves that SUBSET S1 is finite.                             *)
      (*********************************************************************)
      <3>22. PICK n1 \in Nat : n1 = n2*2  BY SMT
      <3>23. PICK N1 : N1 =
             [ a \in 1..n1 |-> IF a \leq n2 THEN N2[a] ELSE N2[a-n2] \cup {M1[j]} ]
             OBVIOUS
      <3>24. N1 \in [1..n1 -> SUBSET S1]
        <4> SUFFICES ASSUME NEW a \in 1..n1  PROVE N1[a] \in SUBSET S1  BY <3>23
        <4>1. CASE a \leq n2  BY <4>1, <3>8, <3>9, <3>20, <3>22, <3>23, SMT
        <4>2. CASE ~(a \leq n2)  BY <4>1, <3>8, <3>9, <3>20, <3>22, <3>23, SMT
        <4> QED BY <4>1, <4>2
      <3>25. ASSUME NEW s \in SUBSET S1  PROVE \E a \in 1..n1 : N1[a] = s
        <4>1. CASE M1[j] \notin s
          <5>1. s \in SUBSET S2  BY <4>1, <3>9
          <5>2. PICK a \in 1..n2 : N2[a] = s  BY <5>1, <3>21
          <5>3. a \in 1..n1  BY <3>22, SMT
          <5>4. N1[a] = N2[a]  BY <5>3, <3>23, SMT
          <5> QED BY <5>2, <5>3, <5>4
        <4>2. CASE M1[j] \in s
          <5>1. PICK t : t = s \ {M1[j]}  OBVIOUS
          <5>2. t \in SUBSET S2  BY <5>1, <3>9
          <5>3. PICK a \in 1..n2 : N2[a] = t  BY <5>2, <3>21
          <5>4. PICK b : b = a+n2  OBVIOUS
          <5>5. b \in 1..n1  BY <5>4, <3>22, SMT
          <5>6. N1[b] = N2[a] \cup {M1[j]}  BY <5>4, <5>5, <3>23, SMT
          <5>7. N1[b] = s  BY <5>1, <5>3, <5>6, <4>2
          <5> QED BY <5>3, <5>5, <5>7
        <4> QED BY <4>1, <4>2
      <3>26. N1 \in Surjection(1..n1,SUBSET S1)  BY <3>24, <3>25, JectionThm_IsSurj
      <3> QED BY <3>26, FiniteSetThm_NatSurjection
    
    <2> HIDE DEF Prop
    <2> QED BY <2>1, <2>2, NatInduction
  
  <1> QED BY <1>1, FiniteSetThm_NatBijection
      
  
  
   


(***************************************************************************)
(* `.  .'                                                                  *)
(*                                                                         *)
(* a..b is a finite set for any a,b \in Int.                               *)
(*                                                                         *)
(* `.  .'                                                                  *)
(***************************************************************************)
THEOREM FiniteSetThm_DotDot ==
  ASSUME
    NEW a \in Int,
    NEW b \in Int
  PROVE IsFiniteSet(a..b)
PROOF
  <1>1. CASE a > b
    <2>1. a..b = {}  BY <1>1, SMT
    <2> QED BY <2>1, FiniteSetThm_Empty
    
  <1>2. CASE a \leq b
    <2>1. PICK n \in Nat : n = (b-a)+1  BY <1>2, SMT
    <2>2. PICK M \in [1..n -> a..b] : M = [i \in 1..n |-> i+a-1]
      <3> SUFFICES ASSUME NEW i \in 1..n  PROVE i+a-1 \in a..b  OBVIOUS
      <3> QED BY <2>1, SMT
    <2>3. M \in Surjection(1..n,a..b)
      <3>1. \A c \in a..b : (c-a)+1 \in 1..n  BY <2>1, SMT
      <3>2. \A c \in a..b : M[(c-a)+1] = ((c-a)+1)+a-1  BY <3>1, <2>2
      <3>3. \A c \in a..b : ((c-a)+1)+a-1 = c BY Z3T(60)
      <3>4. \A c \in a..b : M[(c-a)+1] = c BY <3>2, <3>3      
      <3>5. QED BY <3>1, <3>4, JectionThm_IsSurj
    <2> QED BY <2>3, FiniteSetThm_NatSurjection

  <1> QED BY <1>1, <1>2, SMT




-----------------------------------------------------------------------------
(***************************************************************************)
(* `^{\large\bf \vspace{12pt}                                              *)
(*  Facts about cardinality.                                               *)
(*  \vspace{12pt}}^'                                                       *)
(***************************************************************************)





(***************************************************************************)
(* `.  .'                                                                  *)
(*                                                                         *)
(* If there exists n \in Nat such that a bijection exists from 1..n to S,  *)
(* then Cardinality(S) = n.                                                *)
(*                                                                         *)
(* `.  .'                                                                  *)
(***************************************************************************)
THEOREM FiniteSetThm_NatBijCardinality ==
  ASSUME
    NEW S, NEW n \in Nat, ExistsBijection(1..n,S)
  PROVE
  Cardinality(S) = n
PROOF
  <1> DEFINE
    (***********************************************************************)
    (* Size of set T.                                                      *)
    (***********************************************************************)
    Size(T)  == CHOOSE i \in Nat : ExistsBijection(1..i,T)
    
    (***********************************************************************)
    (* Size function for subsets of S.                                     *)
    (***********************************************************************)
    SZ       == [ T \in SUBSET S |-> Size(T) ]
    
    (***********************************************************************)
    (* Formula part of the CS property for element T.                      *)
    (***********************************************************************)
    fn(CS,T) == IF T = {} THEN 0 ELSE 1 + CS[T \ {CHOOSE x : x \in T}] 
    
    (***********************************************************************)
    (* The CS property.                                                    *)
    (***********************************************************************)
    IsCS(CS) == CS = [T \in SUBSET S |-> fn(CS,T)]
    
    (***********************************************************************)
    (* CS function for subsets of S.  Since this is defined as CHOOSE      *)
    (* something that satisfies the CS property, we do not know that the   *)
    (* CS function actually satisfies the CS property until we know that   *)
    (* there exists something that satisfies the CS property.              *)
    (***********************************************************************)
    CS       == CHOOSE CS : IsCS(CS) 
  
  <1> HIDE DEF SZ, CS, fn
  

  (*************************************************************************)
  (* The SZ function satisfies the CS property.                            *)
  (*************************************************************************)
  <1>1. IsCS(SZ)
    (***********************************************************************)
    (* Use induction on the size of T to show that the values match at     *)
    (* each T \in SUBSET S.                                                *)
    (***********************************************************************)
    <2> DEFINE
      Prop(i) == \A T \in SUBSET S : ExistsBijection(1..i,T) => SZ[T] = fn(SZ,T)

    <2>1. \A i \in Nat : Prop(i)
      <3>1. Prop(0)
        (*******************************************************************)
        (* Base step.                                                      *)
        (*******************************************************************)
        <4>1. SUFFICES ASSUME NEW T \in SUBSET S, ExistsBijection(1..0,T)
              PROVE SZ[T] = fn(SZ,T)
              OBVIOUS
        <4>2. Size(T) = 0  BY <4>1, JectionThm_NatBijSame
        <4>3. T = {}  BY <4>1, JectionThm_NatBijEmpty
        <4>4. SZ[T] = 0  BY <4>2  DEF SZ
        <4>5. fn(SZ,T) = 0  BY <4>3  DEF fn
        <4> QED BY <4>4, <4>5
        
      <3>2. ASSUME NEW i \in Nat, Prop(i)  PROVE Prop(i+1)
        (*******************************************************************)
        (* Inductive step.                                                 *)
        (*******************************************************************)
        <4>1. PICK j \in Nat : j = i+1  BY Isa
        <4>2. j # 0  BY <4>1, SMT
        <4>3. i = j-1  BY <4>1, SMT
        <4>4. SUFFICES ASSUME NEW T \in SUBSET S, ExistsBijection(1..j,T)
              PROVE SZ[T] = fn(SZ,T)
              BY <4>1
        <4>5. ~ExistsBijection(1..0,T)  BY <4>2, <4>4, JectionThm_NatBijSame
        <4>6. T # {}  BY <4>5, JectionThm_NatBijEmpty
        <4>7. Size(T) = j  BY <4>4, JectionThm_NatBijSame
        <4>8. PICK t \in T : t = CHOOSE x : x \in T  BY <4>6
        <4>9. PICK U \in SUBSET S : U = T \ {t}  OBVIOUS
        <4>10. ExistsBijection(1..i,U)  BY <4>3, <4>4, <4>9, JectionThm_NatBijSubElem
        <4>11. SZ[U] = fn(SZ,U)  BY <4>10, <3>2
        <4>12. SZ[U] = i  BY <4>10, JectionThm_NatBijSame  DEF SZ
        <4>13. fn(SZ,T) = 1 + SZ[U]  BY <4>6, <4>8, <4>9  DEF fn
        <4>14. fn(SZ,T) = j  BY <4>1, <4>12, <4>13, SMT
        <4>15. SZ[T] = j  BY <4>7  DEF SZ
        <4> QED BY <4>14, <4>15
        
      <3> HIDE DEF Prop
      <3> QED BY <3>1, <3>2, NatInduction
    
    <2> SUFFICES ASSUME NEW T \in SUBSET S  PROVE SZ[T] = fn(SZ,T)  BY DEF SZ
    <2>2. PICK i \in Nat : ExistsBijection(1..i,T)  BY JectionThm_NatBijSubset
    <2> QED BY <2>1, <2>2

    
  (*************************************************************************)
  (* Any two things that satisfy the CS property must be equal.            *)
  (*************************************************************************)
  <1>2. ASSUME
          NEW CS1, IsCS(CS1),
          NEW CS2, IsCS(CS2)
        PROVE CS1 = CS2
    (***********************************************************************)
    (* Use induction on the size of T to show that the values match at     *)
    (* each T \in SUBSET S.                                                *)
    (***********************************************************************)
    <2> DEFINE
      Prop(i) == \A T \in SUBSET S : ExistsBijection(1..i,T) => CS1[T] = CS2[T]

    <2>1. \A i \in Nat : Prop(i)
      <3>1. Prop(0)
        (*******************************************************************)
        (* Base step.                                                      *)
        (*******************************************************************)
        <4>1. SUFFICES ASSUME NEW T \in SUBSET S, ExistsBijection(1..0,T)
              PROVE CS1[T] = CS2[T]
              OBVIOUS
        <4>2. T = {}  BY <4>1, JectionThm_NatBijEmpty
        <4>3. fn(CS1,T) = 0  BY <4>2  DEF fn
        <4>4. fn(CS2,T) = 0  BY <4>2  DEF fn
        <4> QED BY <4>3, <4>4, <1>2
        
      <3>2. ASSUME NEW i \in Nat, Prop(i)  PROVE Prop(i+1)
        (*******************************************************************)
        (* Inductive step.                                                 *)
        (*******************************************************************)
        <4>1. PICK j \in Nat : j = i+1  BY Isa
        <4>2. j # 0  BY <4>1, SMT
        <4>3. i = j-1  BY <4>1, SMT
        <4>4. SUFFICES ASSUME NEW T \in SUBSET S, ExistsBijection(1..j,T)
              PROVE CS1[T] = CS2[T]
              BY <4>1
        <4>5. ~ExistsBijection(1..0,T)  BY <4>2, <4>4, JectionThm_NatBijSame
        <4>6. T # {}  BY <4>5, JectionThm_NatBijEmpty
        <4>7. PICK t \in T : t = CHOOSE x : x \in T  BY <4>6
        <4>8. PICK U \in SUBSET S : U = T \ {t}  OBVIOUS
        <4>9. ExistsBijection(1..i,U)  BY <4>3, <4>4, <4>8, JectionThm_NatBijSubElem
        <4>10. CS1[U] = CS2[U]  BY <4>9, <3>2
        <4>11. CS1[T] = 1 + CS1[U]  BY <4>6, <4>7, <4>8, <1>2  DEF fn
        <4>12. CS2[T] = 1 + CS2[U]  BY <4>6, <4>7, <4>8, <1>2  DEF fn
        <4> QED BY <4>10, <4>11, <4>12
        
      <3> HIDE DEF Prop
      <3> QED BY <3>1, <3>2, NatInduction
    
    <2> SUFFICES ASSUME NEW T \in SUBSET S  PROVE CS1[T] = CS2[T]  BY <1>2
    <2>2. PICK i \in Nat : ExistsBijection(1..i,T)  BY JectionThm_NatBijSubset
    <2> QED BY <2>1, <2>2
  
    
  (*************************************************************************)
  (* Since SZ satisfies the CS property, the CS function must satisfy the  *)
  (* CS property.  And it must be the same as SZ.                          *)
  (*************************************************************************)
  <1>3. IsCS(CS)  BY <1>1  DEF CS
  <1>4. CS = SZ  BY <1>1, <1>2, <1>3


  <1>5. Cardinality(S) = CS[S]  BY DEF Cardinality, CS, fn
  <1>6. S \in SUBSET S  OBVIOUS
  <1>7. SZ[S] = Size(S)  BY <1>6  DEF SZ
  <1>8. Size(S) = n  BY JectionThm_NatBijSame
  <1> QED BY <1>4, <1>5, <1>7, <1>8





(***************************************************************************)
(* `.  .'                                                                  *)
(*                                                                         *)
(* For any finite set S, Cardinality(S) \in Nat.                           *)
(*                                                                         *)
(* `.  .'                                                                  *)
(***************************************************************************)
THEOREM FiniteSetThm_CardinalityType ==
  ASSUME NEW S, IsFiniteSet(S)
  PROVE  Cardinality(S) \in Nat
<1>1. PICK n \in Nat : ExistsBijection(1..n,S)  BY FiniteSetThm_NatBijection
<1>2. Cardinality(S) = n  BY <1>1, FiniteSetThm_NatBijCardinality
<1> QED BY <1>2



(***************************************************************************)
(* `.  .'                                                                  *)
(*                                                                         *)
(* For any finite set S, there exists a bijection from 1..Cardinality(S)   *)
(* to S.                                                                   *)
(*                                                                         *)
(* `.  .'                                                                  *)
(***************************************************************************)
THEOREM FiniteSetThm_CardinalityNatBij ==
  ASSUME NEW S, IsFiniteSet(S)
  PROVE  ExistsBijection(1..Cardinality(S),S)
<1>1. PICK n \in Nat : ExistsBijection(1..n,S)  BY FiniteSetThm_NatBijection
<1>2. Cardinality(S) = n  BY <1>1, FiniteSetThm_NatBijCardinality
<1> QED BY <1>1, <1>2


(***************************************************************************)
(* `.  .'                                                                  *)
(*                                                                         *)
(* The cardinality of a finite set S is 0 iff S is empty.                  *)
(*                                                                         *)
(* `.  .'                                                                  *)
(***************************************************************************)

THEOREM FiniteSetThm_CardinalityEmpty == 
  ASSUME NEW S, IsFiniteSet(S)
  PROVE  Cardinality(S)=0 <=> S={}
PROOF 
<1>1. ASSUME S={} PROVE Cardinality(S)=0
      BY <1>1 DEF Cardinality
<1>2. ASSUME Cardinality(S)=0 PROVE S={}
  <2>1. ExistsBijection(1..0, S)
    BY FiniteSetThm_CardinalityNatBij, <1>2
  <2>2. QED
    BY JectionThm_NatBijEmpty, <2>1
<1>3. QED
      BY <1>1, <1>2                  

      
(***************************************************************************)
(* `.  .'                                                                  *)
(*                                                                         *)
(* Cardinality of a finite set after removing or adding an element.        *)
(*                                                                         *)
(* `.  .'                                                                  *)
(***************************************************************************)

THEOREM FiniteSetThm_CardinalityRemoveElement ==
  ASSUME NEW S, IsFiniteSet(S), NEW x
  PROVE  /\ IsFiniteSet(S \ {x})
         /\ Cardinality(S \ {x}) = 
            IF x \in S THEN Cardinality(S) - 1 ELSE Cardinality(S)
<1>1. IsFiniteSet(S \ {x})
  BY FiniteSetThm_Subset
<1>2. ASSUME x \in S
      PROVE  Cardinality(S \ {x}) = Cardinality(S) - 1
  <2>1. /\ Cardinality(S) \in Nat
        /\ Cardinality(S) - 1 \in Nat
    BY SMT, <1>2, FiniteSetThm_CardinalityType, FiniteSetThm_CardinalityEmpty
  <2>2. PICK enumS \in Bijection(1 .. Cardinality(S), S) : TRUE
    BY FiniteSetThm_CardinalityNatBij DEF ExistsBijection
  <2>3. PICK cntx \in 1 .. Cardinality(S) : enumS[cntx] = x
    BY Blast, <1>2, <2>2, JectionThm_BijProp DEF JectionThm_BijProp_Qed
  <2>. DEFINE enum == [i \in 1 .. Cardinality(S)-1 |-> 
                         IF i < cntx THEN enumS[i] ELSE enumS[i+1]]
  <2>4. enum \in Bijection(1 .. Cardinality(S)-1, S \ {x})
    <3>1. /\ enumS \in [1 .. Cardinality(S) -> S]
          /\ \A i \in 1 .. Cardinality(S) : enumS[i] = x => i = cntx
      BY <2>2, <2>3, JectionThm_BijProp DEF JectionThm_BijProp_Qed
    <3>2. \A i,j \in 1 .. Cardinality(S) : enumS[i] = enumS[j] => i = j
      BY <2>2, <2>3, JectionThm_BijProp DEF JectionThm_BijProp_Qed
    <3>3. \A s \in S : \E i \in 1 .. Cardinality(S) : enumS[i] = s
      BY <2>2, <2>3, JectionThm_BijProp DEF JectionThm_BijProp_Qed
    <3>4. \A i \in 1 .. Cardinality(S)-1 : \E j \in 1 .. Cardinality(S) :
              /\ enum[i] = enumS[j]
              /\ enum[i] # x
      BY SMT, <2>1, <3>1
    <3>5. enum \in [1 .. Cardinality(S)-1 -> S \ {x}]
      BY <3>1, <3>4
    <3>6. \A i,j \in 1 .. Cardinality(S)-1 : enum[i] = enum[j] => i=j
      BY SMT, <2>1, <3>2
    <3>7. ASSUME NEW s \in S \ {x}
           PROVE  \E i \in 1 .. Cardinality(S)-1 : enum[i] = s
      <4>1. PICK j \in 1 .. Cardinality(S) : enumS[j] = s
        BY <3>3
      <4>2. j # cntx
        BY <4>1, <3>1, <2>3
      <4>3. CASE j < cntx
        <5>1. j \in 1 .. Cardinality(S)-1
          BY <4>3, <2>1, SMT
        <5>. QED
          BY <5>1, <4>3, <4>1
      <4>4. CASE j > cntx
        <5>1. j-1 \in 1 .. Cardinality(S)-1
          BY <4>4, <2>1, SMT
        <5>2. enum[j-1] = s
          BY SMT, <5>1, <4>4, <4>1
        <5>. QED
          BY <5>1, <5>2
      <4>. QED
        BY <4>2, <4>3, <4>4, SMT
    <3>. QED
      BY <3>5, <3>6, <3>7, JectionThm_IsBij
  <2>. QED
    BY <2>1, <2>4, FiniteSetThm_NatBijCardinality DEF ExistsBijection
<1>. QED  BY <1>1, <1>2



THEOREM FiniteSetThm_SetUnionElement == 
  ASSUME NEW S, IsFiniteSet(S), NEW x
  PROVE  /\ IsFiniteSet(S \cup {x}) 
         /\ Cardinality(S \cup {x}) = 
            IF x \in S THEN Cardinality(S) ELSE Cardinality(S) + 1
<1>1. IsFiniteSet(S \cup {x})
  BY FiniteSetThm_Singleton, FiniteSetThm_Union
<1>2. ASSUME x \notin S PROVE Cardinality(S \cup {x}) = Cardinality(S) + 1
      <2>2. ExistsBijection(1..Cardinality(S),S)
            BY FiniteSetThm_CardinalityNatBij
      <2>3. ExistsBijection(1..Cardinality(S)+1, S \cup {x})     
            <3>1. PICK f : f \in Bijection(1..Cardinality(S),S) 
                  BY <2>2 DEF ExistsBijection
            <3>2. DEFINE g == [i \in 1..(Cardinality(S)+1) |-> IF i < Cardinality(S)+1 THEN f[i] ELSE x]
            <3>3. g \in [1..Cardinality(S)+1->S\cup{x}]
                  <4>1. \A i \in 1..Cardinality(S)+1: g[i] \in S \cup {x}
                        <5>1. TAKE i \in 1..(Cardinality(S)+1)
                        <5>2. CASE i < Cardinality(S)+1
                              <6>1. g[i] = f[i]
                                    BY <5>2 DEF g
                              <6>2.  f \in [1..Cardinality(S) -> S]
                                    BY <3>1, JectionThm_BijProp DEF JectionThm_BijProp_Qed
                              <6>3.  i \in 1..Cardinality(S)
                                    BY <5>1, <5>2, FiniteSetThm_CardinalityType, SMT
                              <6>4. f[i] \in S 
                                    BY <6>2, <6>3      
                              <6>5. QED
                                    BY <6>3, <6>4
                        <5>3. CASE i = Cardinality(S)+1
                              <6>1. g[i]=x
                                    BY <5>3 DEF g
                              <6>2. QED
                                    BY <6>1     
                        <5>4 QED                              
                             BY <5>3, <5>2
                  <4>2. QED
                        BY <4>1      
            <3>4. g \in Bijection(1..Cardinality(S)+1,S \cup {x})
                  <4>1. g \in Surjection(1..Cardinality(S)+1,S \cup {x})
                        <5>1. \A s \in S \cup {x} : \E t \in 1..Cardinality(S)+1 : g[t] = s
                              <6>1. TAKE s \in S \cup {x} 
                              <6>2. CASE s \in S
                                    <7>1. PICK i0 \in 1..Cardinality(S) : f[i0]=s
                                          BY <3>1, <6>2 DEF Bijection, Surjection
                                    <7>2. i0 \in 1..Cardinality(S)+1
                                          BY <7>1, FiniteSetThm_CardinalityType, SMT
                                    <7>3. g[i0]=s
                                    
                                          <8>1. i0 < Cardinality(S)+1
                                                BY <7>1, SMT, FiniteSetThm_CardinalityType
                                          <8>2. g[i0]=f[i0]
                                                BY <8>1, <7>2 DEF g
                                          <8>3. QED
                                                BY <8>2, <7>1           
                                    <7>. QED
                                         BY <7>2, <7>3
                              <6>3. CASE s=x
                                    <7>1. DEFINE i1==Cardinality(S)+1
                                    <7>2. i1 \in 1..Cardinality(S)+1
                                          BY SMT, FiniteSetThm_CardinalityType
                                    <7>3. g[i1]=s
                                          BY <6>3, <7>2 DEF g
                                    <7>4. QED
                                          BY <7>2, <7>3      
                              <6>4. QED
                                    BY <6>2, <6>3
                        <5>2. QED
                              BY <5>1, <3>3, JectionThm_IsSurj
                              
                  <4>2. g \in Injection(1..Cardinality(S)+1,S \cup {x})
                        <5>1. \A a,b \in 1..Cardinality(S)+1 : g[a]=g[b] => a=b
                              <6>1. TAKE a \in 1..Cardinality(S)+1
                              <6>2. TAKE b \in 1..Cardinality(S)+1
                              <6>3. ASSUME g[a]=g[b] PROVE a=b
                                    <7>1. CASE g[a] \in S /\ g[b] \in S
                                          <8>1. ASSUME a=Cardinality(S)+1 PROVE FALSE
                                                <9>1. g[a] \notin S
                                                      BY <1>2, <8>1 DEF g
                                                <9>2. QED
                                                      BY <9>1, <7>1     
                                          <8>2. ASSUME b=Cardinality(S)+1 PROVE FALSE
                                                <9>1. g[b] \notin S
                                                      BY <1>2, <8>2 DEF g
                                                <9>2. QED
                                                      BY <9>1, <7>1
                                          <8>3. a \in 1..Cardinality(S) /\ b \in 1..Cardinality(S)
                                                BY <8>1, <8>2, <6>1, <6>2, SMT, FiniteSetThm_CardinalityType 
                                          <8>4. g[a]=f[a] /\ g[b]=f[b]
                                                BY <8>3, FiniteSetThm_CardinalityType, SMT  DEF g
                                          <8>5. f[a]=f[b] => a=b
                                                BY <8>3, <3>1 DEF Bijection, Injection 
                                          <8>6. QED
                                               BY <8>4, <8>5, <6>3
                                                
                                    <7>2. CASE g[a] \in S /\ g[b]=x
                                          <8>1. FALSE
                                                BY <7>2, <6>3, <1>2 
                                          <8>2. QED
                                                BY <8>1      
                                    <7>3. CASE g[a]=x /\ g[b] \in S
                                          <8>1. FALSE
                                                BY <7>3, <6>3, <1>2 
                                          <8>2. QED
                                                BY <8>1                                          
                                    <7>4. CASE g[a]=x /\ g[b]=x
                                          <8>1. ASSUME a \in 1..Cardinality(S) PROVE FALSE
                                                <9>1. g[a]=f[a]
                                                      BY <8>1, FiniteSetThm_CardinalityType, SMT DEF g
                                                <9>2. f \in [1..Cardinality(S) -> S]
                                                      BY <3>1, JectionThm_BijProp DEF JectionThm_BijProp_Qed
                                                <9>3. f[a] \in S
                                                      BY <9>2, <8>1
                                                <9>4.  QED
                                                      BY <9>1, <9>3, <1>2, <7>4     
                                          <8>2. ASSUME b \in 1..Cardinality(S) PROVE FALSE      
                                                <9>1. g[b]=f[b]
                                                      BY <8>2, FiniteSetThm_CardinalityType, SMT DEF g
                                                <9>2. f \in [1..Cardinality(S) -> S]
                                                      BY <3>1, JectionThm_BijProp DEF JectionThm_BijProp_Qed
                                                <9>3. f[b] \in S
                                                      BY <9>2, <8>2
                                                <9>4.  QED
                                                      BY <9>1, <9>3, <1>2, <7>4
                                          <8>3. a = Cardinality(S)+1
                                                BY <8>1, <6>1, SMT, FiniteSetThm_CardinalityType
                                          <8>4. b = Cardinality(S)+1
                                                BY <8>2, <6>1, SMT, FiniteSetThm_CardinalityType
                                          <8>5. QED
                                               BY <8>3, <8>4, <7>4      
                                    <7>5. QED
                                          BY <7>1, <7>2, <7>3, <7>4, <3>3
                              <6>4. QED
                                    BY <6>3
                                    
                        <5>2. QED
                              BY <5>1, <3>3, JectionThm_IsInj 
                  <4>3. QED
                        BY <4>1, <4>2 DEF Bijection
            <3>5. QED
                  BY <3>4 DEF ExistsBijection 
      <2>4. Cardinality(S)+1 \in Nat
            <3>1. Cardinality(S) \in Nat
                  BY FiniteSetThm_CardinalityType
            <3>2. QED
                  BY SMT, <3>1                  
      <2>5. QED
            BY <2>3, <2>4, FiniteSetThm_NatBijCardinality    

<1>3. ASSUME x \in S PROVE Cardinality(S \cup {x}) = Cardinality(S)
  BY <1>3

<1>4. QED
      BY <1>1, <1>2, <1>3




(***************************************************************************)
(* `.  .'                                                                  *)
(*                                                                         *)
(* Induction for finite sets.                                              *)
(*                                                                         *)
(* `.  .'                                                                  *)
(***************************************************************************)

THEOREM FiniteSetThm_Induction == 
  ASSUME NEW S, IsFiniteSet(S),
         NEW P(_), P({}),
         \A T : \A x : IsFiniteSet(T) /\ P(T) => P(T \cup {x})
  PROVE  P(S)
<1>.  DEFINE Q(n) == \A T : IsFiniteSet(T) /\ Cardinality(T)=n => P(T)
<1>1. SUFFICES \A n \in Nat : Q(n)
  BY FiniteSetThm_CardinalityType
<1>2. Q(0) 
  BY FiniteSetThm_CardinalityEmpty
<1>3. ASSUME NEW n \in Nat, Q(n),
             NEW T, IsFiniteSet(T), Cardinality(T)=n+1
      PROVE  P(T)
  <2>1. PICK x \in T : TRUE
    BY <1>3, FiniteSetThm_CardinalityEmpty, SMT
  <2>2. /\ IsFiniteSet(T \ {x})
        /\ Cardinality(T \ {x}) = n
    BY Isa, <1>3, FiniteSetThm_CardinalityRemoveElement
  <2>3. P(T \ {x})
    BY <2>2, Q(n)
  <2>4. P((T \ {x}) \cup {x})
    BY <2>2, <2>3
  <2>. QED
    BY <2>4
<1>4. QED
  BY <1>2, <1>3, NatInduction, Isa



(***************************************************************************)
(* `.  .'                                                                  *)
(*                                                                         *)
(* The finite subsets form a well-founded ordering with respect to strict  *)
(* set inclusion.                                                          *)
(*                                                                         *)
(* `.  .'                                                                  *)
(***************************************************************************)

FiniteSubsetsOf(S) == { T \in SUBSET S : IsFiniteSet(T) }
StrictSubsetOrdering(S) == { ss \in (SUBSET S) \X (SUBSET S) : 
                                ss[1] \subseteq ss[2] /\ ss[1] # ss[2] }

(***************************************************************************************
CARDINALITY UNION OF SETS : CARDINLATY(A\UNION B) = CARDINALITY(A)+Cardinality(B) - CARDINALITY(A\INTERSECT B)
****************************************************************************************)      


THEOREM FiniteSetThm_UnionCardinality == \A A: \A B : IsFiniteSet(A)/\IsFiniteSet(B) => Cardinality(A \cup B) = Cardinality(A) + Cardinality(B) - Cardinality(A \cap B)
PROOF 
<1>1. TAKE A       
<1>2. DEFINE P(B)== Cardinality(A \cup B) = Cardinality(A) + Cardinality(B) - Cardinality(A \cap B)

<1>3. ASSUME IsFiniteSet(A) PROVE \A B : IsFiniteSet(B) => P(B)
      (* Proof by INDUCTION  *)
      \*BASECASE
      <2>1. P({})
            <3>1. Cardinality(A \cup {})= Cardinality(A)
                  OBVIOUS
            <3>2. Cardinality(A \cap {})= 0
                  BY FiniteSetThm_CardinalityEmpty, FiniteSetThm_Empty
            <3>3. Cardinality(A \cup {}) \in Nat /\ Cardinality(A \cap {}) \in Nat /\ Cardinality({}) \in Nat /\ Cardinality(A) \in Nat
                  BY FiniteSetThm_Empty, <1>3, FiniteSetThm_CardinalityType
            <3>4.  QED
                  BY <3>1, <3>2, <3>3, SMT       
      \*INDUCTION STEP
      <2>2. \A B : \A x : IsFiniteSet(B) => (P(B)=> P(B \cup {x}))
             <3>1. TAKE B
             <3>2. TAKE x
             <3>3. ASSUME IsFiniteSet(B) /\ P(B) PROVE P(B \cup {x})
                         <4>1. CASE x \in A /\ x \in B
                               BY <3>3, <4>1 DEF P           
                         <4>2. CASE x \in A /\ x \notin B
                               <5>1. Cardinality(A \cup (B \cup {x}))= Cardinality(A \cup B)
                                     BY <4>2
                               <5>2. Cardinality(A \cup (B \cup {x}))= Cardinality(A) + Cardinality(B) - Cardinality(A \cap B)
                                     BY <5>1, <3>3 DEF P
                               <5>3. Cardinality(B \cup {x})-1= Cardinality(B)
                                     BY <3>3, <4>2, FiniteSetThm_SetUnionElement, FiniteSetThm_CardinalityType        
                               <5>4. Cardinality(A \cap (B \cup {x})) = Cardinality((A \cap B) \cup {x})
                                     BY <4>2
                               <5>5. Cardinality((A \cap B) \cup {x}) = Cardinality(A \cap B)+1       
                                     BY <3>3, <4>2, FiniteSetThm_SetUnionElement, FiniteSetThm_Intersection
                               <5>6. Cardinality(A \cap (B \cup {x})) = Cardinality(A \cap B)+1
                                     BY <5>4, <5>5
                               <5>.  IsFiniteSet(A \cap (B \cup {x})) /\ IsFiniteSet(A \cap B) /\ IsFiniteSet(B \cup {x}) /\ IsFiniteSet(A \cup (B \cup {x})) 
                                     BY <3>3, <1>3, FiniteSetThm_Singleton, FiniteSetThm_SetUnionElement, FiniteSetThm_Intersection, FiniteSetThm_Union
                               <5>7. Cardinality(A \cap B)= Cardinality(A \cap (B \cup {x})) - 1
                                     BY <5>6, <3>3, FiniteSetThm_CardinalityType
                               <5>8. Cardinality(A \cup (B \cup {x})) = Cardinality(A) + (Cardinality(B \cup {x})-1) - (Cardinality(A \cap (B \cup {x})) - 1)
                                     BY <5>2, <5>3, <5>7
                               <5>9. QED
                                     BY <5>8, SMT, FiniteSetThm_CardinalityType DEF P      
                         <4>3. CASE x \notin A /\ x \in B
                               BY <3>3, <4>3 DEF P
                         <4>4. CASE x \notin A /\ x \notin B
                               <5>1. Cardinality(A \cup (B \cup {x}))= Cardinality((A \cup B)\cup{x})
                                     BY <4>4
                               <5>2. Cardinality(A \cup (B \cup {x}))= Cardinality(A \cup B)+1
                                     BY <5>1, <4>4, FiniteSetThm_SetUnionElement, <3>3, <1>3, FiniteSetThm_Union
                               <5>3. Cardinality(A \cup (B \cup {x}))= Cardinality(A) + Cardinality(B) -Cardinality(A \cap B) +1
                                     BY <5>2, <3>3 DEF P
                               <5>4. Cardinality(B \cup {x})-1= Cardinality(B)
                                     BY <3>3, <4>4, FiniteSetThm_SetUnionElement, FiniteSetThm_CardinalityType      
                               <5>5. Cardinality(A \cap B)= Cardinality(A \cap (B \cup {x}))
                                     BY <4>4
                               <5>6. Cardinality(A \cup (B \cup {x}))= Cardinality(A) + (Cardinality(B \cup {x})-1) - Cardinality(A \cap (B \cup {x})) +1
                                     BY <5>3, <5>4, <5>5
                               <5>.  IsFiniteSet(A \cap (B \cup {x})) /\ IsFiniteSet(A \cap B) /\ IsFiniteSet(B \cup {x}) /\ IsFiniteSet(A \cup (B \cup {x})) /\ IsFiniteSet(A) 
                                     BY <3>3, <1>3, FiniteSetThm_Singleton, FiniteSetThm_SetUnionElement, FiniteSetThm_Intersection, FiniteSetThm_Union                                     
                               <5>7.  QED
                                     BY <5>6, SMT, FiniteSetThm_CardinalityType DEF P 
                         <4>.  QED 
                               BY <4>1, <4>2, <4>3, <4>4 
                         
             <3>4. QED
                   BY <3>3
                              
      <2>.  HIDE DEF P
      <2>3. QED
            BY  Blast, <2>1, <2>2, FiniteSetThm_Induction 
<1>4. QED     
      BY <1>3 DEF P



(***************************************************************************)
(*Cardinality of Subset <= Cardinality of Set                              *)
(***************************************************************************)

      
THEOREM FiniteSetThm_SubsetCardinality == ASSUME NEW A, NEW B, IsFiniteSet(A), IsFiniteSet(B), B \subseteq A
                                          PROVE Cardinality(B) \leq Cardinality(A)
PROOF 
<1>1. B \in SUBSET A
      OBVIOUS
<1>2. ExistsBijection(1..Cardinality(A), A)
      BY FiniteSetThm_CardinalityNatBij
<1>3. \E n \in Nat : ExistsBijection(1..n,B) /\ n \leq Cardinality(A)
      BY <1>1, <1>2, FiniteSetThm_CardinalityType, JectionThm_NatBijSubset
<1>4. PICK n \in Nat : ExistsBijection(1..n, B) /\ n \leq Cardinality(A)
      BY <1>3
<1>5. n=Cardinality(B)
      BY <1>4, JectionThm_NatBijSubset, FiniteSetThm_NatBijCardinality
<1>6. QED
      BY <1>4, <1>5




(*********************************************************************************************)
(* CADRINALITY OF DIFFERENCE OF SETS : IsFiniteSet(S)=> Card(S\T) = Card(S) - Card(S \cap T) *)
(*********************************************************************************************)

THEOREM FiniteSetThm_DifferenceCardinality == ASSUME NEW A, NEW B, IsFiniteSet(A), IsFiniteSet(B) 
                                              PROVE /\ IsFiniteSet(A\B)
                                                    /\ Cardinality(A\B)= Cardinality(A) - Cardinality(A \cap B)
PROOF
<1>1. IsFiniteSet(A\B)
      <2>1. A\B \subseteq A
            OBVIOUS
      <2>2. QED
            BY <2>1, FiniteSetThm_Subset   
                      
<1>2. Cardinality(A\B)= Cardinality(A) - Cardinality(A \cap B)
      <2>1. A \cup B= B \cup (A\B) /\ Cardinality(A\cup B)= Cardinality(B \cup (A\B))
            OBVIOUS
      
      <2>2. Cardinality(A) + Cardinality(B) - Cardinality(A \cap B) = Cardinality(B \cup (A\B))
            BY <2>1, FiniteSetThm_UnionCardinality, <1>1
      <2>3. Cardinality(A) + Cardinality(B) - Cardinality(A \cap B) = Cardinality(B) + Cardinality(A\B) - Cardinality(B \cap (A\B))
            BY <2>2, FiniteSetThm_UnionCardinality, <1>1
      <2>4. /\IsFiniteSet(A \cap B) /\ IsFiniteSet(B \cap (A\B)) /\ B \cap (A\B) ={}
            BY <2>1, FiniteSetThm_Intersection                 
      <2>5. QED 
            BY <1>1, <2>3, <2>4, FiniteSetThm_CardinalityEmpty, FiniteSetThm_CardinalityType, SMT     
<1>3. QED      
      BY <1>1, <1>2

      



(*************************************************************************************)
(* Given A,B are finite Prove f: A->B is Bijection IFF Cardinality(A)=Cardinality(B) *)
(*************************************************************************************)

THEOREM FiniteSetThm_BjectionCardinalityEqual == ASSUME NEW A, NEW B, IsFiniteSet(A), IsFiniteSet(B)
                                                 PROVE ExistsBijection(A,B) <=> Cardinality(A)=Cardinality(B)
PROOF 
<1>1. ASSUME ExistsBijection(A,B) PROVE Cardinality(A)=Cardinality(B)
      <2>1. ExistsBijection(1..Cardinality(A), A)
            BY FiniteSetThm_CardinalityNatBij 
      <2>2. ExistsBijection(1..Cardinality(A), B)
            BY <2>1, <1>1, JectionThm_ExistsBijTransitive
      <2>3. QED     
            BY <2>2, FiniteSetThm_NatBijCardinality, FiniteSetThm_CardinalityType                                          
<1>2. ASSUME Cardinality(A)=Cardinality(B) PROVE ExistsBijection(A, B)
      <2>1. ExistsBijection(A, 1..Cardinality(A))
            BY FiniteSetThm_CardinalityNatBij, JectionThm_ExistsBijSymmetric 
      <2>2. ExistsBijection(1..Cardinality(B), B)
            BY FiniteSetThm_CardinalityNatBij
      <2>3. QED
            BY <1>2, <2>1, <2>2, JectionThm_ExistsBijTransitive
<1>3. QED 
      BY <1>1, <1>2      

(****************************************************************************)
(*  Finte UNION of Finite Sets is Finite                                    *)
(****************************************************************************)

THEOREM FiniteSetThm_FiniteUNIONCardinality ==  ASSUME NEW S, IsFiniteSet(S)
                                                PROVE (\A T \in S: IsFiniteSet(T)) => IsFiniteSet(UNION S)
PROOF OMITTED



=============================================================================
\* Modification History
\* Last modified Wed Jun 26 11:48:43 CEST 2013 by bhargav
\* Last modified Tue Jun 25 14:48:20 CEST 2013 by merz
\* Last modified Tue Jun 04 11:44:51 CEST 2013 by bhargav
\* Last modified Fri May 03 12:02:51 PDT 2013 by tomr
\* Created Fri Oct 05 15:04:18 PDT 2012 by tomr