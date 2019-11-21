---------------------- MODULE Utils -------------------------------
EXTENDS Integers, TLAPS, FiniteSetTheorems

(*************************************************************************)
(*           Auxiliary Definitions and Lemmas for Quicksort proofs       *)
(*************************************************************************)


(*************************************************************************)
(*                      Max Definition and Lemmata                       *)


(* Max stolen from "Implementing and Combining Specifications" *)
Max(S) == CHOOSE n \in S : \A m \in S : m =< n


(* for any non-empty finite set of Ints, S,
        Max(S) is in S, 
    and Max(S) is greater-equal than all elements of S *)
LEMMA finite_Max ==
  ASSUME NEW S \in SUBSET Int, S # {}, IsFiniteSet(S)
  PROVE  /\ Max(S) \in S
         /\ \A m \in S : m <= Max(S)
<1>. DEFINE P(T) == T \in SUBSET Int /\ T # {} => Max(T) \in T /\ \A m \in T : m <= Max(T)
<1>1. P({})  OBVIOUS
<1>2. ASSUME NEW T, NEW x, IsFiniteSet(T), P(T), x \notin T
      PROVE  P(T \cup {x})
  <2>. SUFFICES ASSUME T \in SUBSET Int, x \in Int
                PROVE  /\ Max(T \cup {x}) \in T \cup {x}
                       /\ \A m \in T \cup {x} : m <= Max(T \cup {x})
    OBVIOUS
  <2>1. CASE T = {}
    <3>1. Max(T \cup {x}) = x  BY <2>1 DEF Max
    <3>. QED  BY <2>1, <3>1
  <2>2. T # {} => x <= Max(T) \/ x > Max(T)
    <3>1. T # {} => Max(T) \in Int  BY <1>2
    <3>. QED  BY <3>1
  <2>3. CASE T # {} /\ x <= Max(T)
    <3>. DEFINE MT == Max(T)
    <3>2. /\ MT \in T \cup {x}
          /\ \A m \in T \cup {x} : m <= MT
      BY <1>2, <2>3
    <3>. HIDE DEF MT
    <3>3. Max(T \cup {x}) = MT
      BY <3>2 DEF Max
    <3>. QED  BY <3>2, <3>3
  <2>4. CASE T # {} /\ x > Max(T)
    <3>. DEFINE MT == Max(T)
    <3>1. /\ MT \in Int
          /\ \A m \in T : m <= MT
      BY <1>2, <2>4
    <3>2. \A m \in T \cup {x} : m <= x
      BY <3>1, <2>4
    <3>3. Max(T \cup {x}) = x
      BY <3>2 DEF Max
    <3>. QED  BY <3>2, <3>3
  <2>. QED  BY <2>1, <2>2, <2>3, <2>4
<1>. HIDE DEF P
<1>3. P(S)  BY <1>1, <1>2, FS_Induction, IsaM("blast")
<1>. QED  BY <1>3 DEF P

LEMMA leq_Max == 
  ASSUME NEW m \in Int, NEW S \in SUBSET Int, IsFiniteSet(S),
         NEW x \in S, m <= x
  PROVE  m <= Max(S)
<1>1. /\ Max(S) \in Int
      /\ x <= Max(S)
  BY finite_Max
<1>. QED  BY <1>1


(* for any finite subset of Ints, S, Max(S) is an Int *)
LEMMA MaxTypeOK == \A S : S \in SUBSET Int /\ IsFiniteSet(S) => Max(S) \in Int
  <1> SUFFICES ASSUME NEW S,
                      S \in SUBSET Int,
                      IsFiniteSet(S)
               PROVE  (* Max(S) \in Int *)
                      \A n \in S : n \in Int
    BY DEF Max
  <1>1 ASSUME NEW n \in S
       PROVE n \in Int
       OBVIOUS  
  <1> QED
    BY <1>1
    
(* For any finite subset of Ints, S, and any non-empty subset of S, T, Max(T) is less-than-or-equal Max(S) *)
LEMMA subset_Max == \A S : S \in SUBSET Int /\ IsFiniteSet(S) => \A  T : T \in SUBSET S /\ T # {} => Max(T) <= Max(S)
  <1> SUFFICES ASSUME NEW S,
                      S \in SUBSET Int,
                      IsFiniteSet(S),
                      NEW T,
                      T \in SUBSET S,
                      T # {}
               PROVE  Max(T) <= Max(S)
    OBVIOUS
    
  <1>1 Max(T) \in T
    BY T \in SUBSET Int, FS_Subset, IsFiniteSet(T), finite_Max

  <1>2 \A x \in T : \E y \in S : x <= y 
    <2> SUFFICES ASSUME NEW x \in T
                 PROVE  \E y \in S : x <= y
      OBVIOUS
    <2>1 Max(S) \in S
        BY finite_Max
    <2>2 x \in S
        OBVIOUS
    <2> QED
        BY <2>1, <2>2

  <1>3 \A x \in S : x <= Max(S)
    BY finite_Max
  
  <1> QED
    BY <1>1, <1>2, <1>3





(*************************************************************************)
(*                      Min Definition and Lemmata                       *)

Min(S) == CHOOSE n \in S : \A m \in S : n =< m

LEMMA finite_Min ==
  ASSUME NEW S \in SUBSET Int, S # {}, IsFiniteSet(S)
  PROVE  /\ Min(S) \in S
         /\ \A m \in S : m >= Min(S)
<1>. DEFINE P(T) == T \in SUBSET Int /\ T # {} => Min(T) \in T /\ \A m \in T : m >= Min(T)
<1>1. P({})  OBVIOUS
<1>2. ASSUME NEW T, NEW x, IsFiniteSet(T), P(T), x \notin T
      PROVE  P(T \cup {x})
  <2>. SUFFICES ASSUME T \in SUBSET Int, x \in Int
                PROVE  /\ Min(T \cup {x}) \in T \cup {x}
                       /\ \A m \in T \cup {x} : m >= Min(T \cup {x})
    OBVIOUS
  <2>1. CASE T = {}
    <3>1. Min(T \cup {x}) = x  
        BY <2>1 DEF Min
    <3>. QED  
        BY <2>1, <3>1
  <2>2. T # {} => x >= Min(T) \/ x < Min(T)
    <3>1. T # {} => Min(T) \in Int  BY <1>2
    <3>. QED  BY <3>1
  <2>3. CASE T # {} /\ x >= Min(T)
    <3>. DEFINE MT == Min(T)
    <3>2. /\ MT \in T \cup {x}
          /\ \A m \in T \cup {x} : m >= MT
      BY <1>2, <2>3
    <3>. HIDE DEF MT
    <3>3. Min(T \cup {x}) = MT
      BY <3>2 DEF Min
    <3>. QED  
        BY <3>2, <3>3
  <2>4. CASE T # {} /\ x < Min(T)
    <3>. DEFINE MT == Min(T)
    <3>1. /\ MT \in Int
          /\ \A m \in T : m >= MT
      BY <1>2, <2>4
    <3>2. \A m \in T \cup {x} : m >= x
      BY <3>1, <2>4
    <3>3. Min(T \cup {x}) = x
      BY <3>2 DEF Min
    <3>. QED  BY <3>2, <3>3
  <2>. QED  BY <2>1, <2>2, <2>3, <2>4
<1>. HIDE DEF P
<1>3. P(S)  BY <1>1, <1>2, FS_Induction, IsaM("blast")
<1>. QED  BY <1>3 DEF P

LEMMA leq_Min ==
  ASSUME NEW m \in Int, 
         NEW S \in SUBSET Int, 
         IsFiniteSet(S),
         NEW x \in S, 
         m >= x
  PROVE  m >= Min(S)
 <1>1 /\ Min(S) \in Int
      /\ x >= Min(S)
  BY finite_Min
<1>. QED  BY <1>1



LEMMA MinTypeOK == \A S :  S \in SUBSET Int /\ IsFiniteSet(S) => Min(S) \in Int
 <1> SUFFICES ASSUME NEW S,
                      S \in SUBSET Int,
                      IsFiniteSet(S)
               PROVE  (* Min(S) \in Int *)
                      \A n \in S : n \in Int
    BY DEF Min
  <1>1 ASSUME NEW n \in S
       PROVE n \in Int
       OBVIOUS  
  <1> QED
    BY <1>1


LEMMA subset_Min == \A S : S \in SUBSET Int /\ IsFiniteSet(S) => \A  T : T \in SUBSET S /\ T # {} => Min(S) <=  Min(T) 
 <1> SUFFICES ASSUME NEW S,
                      S \in SUBSET Int,
                      IsFiniteSet(S),
                      NEW T,
                      T \in SUBSET S,
                      T # {}
               PROVE  Min(S) <= Min(T)
    OBVIOUS
    
  <1>1 Min(T) \in T
    BY T \in SUBSET Int, FS_Subset, IsFiniteSet(T), finite_Min

  <1>2 \A x \in T : \E y \in S : x >= y 
    <2> SUFFICES ASSUME NEW x \in T
                 PROVE  \E y \in S : x >= y
      OBVIOUS
    <2>1 Min(S) \in S
        BY finite_Min
    <2>2 x \in S
        OBVIOUS
    <2> QED
        BY <2>1, <2>2

  <1>3 \A x \in S : x >= Min(S)
    BY finite_Min
  
  <1> QED
    BY <1>1, <1>2, <1>3





=============================================================================
\* Modification History
\* Last modified Wed Jan 22 11:15:57 CET 2014 by jael
\* Created Wed Jan 22 09:08:48 CET 2014 by jael

