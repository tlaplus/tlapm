-------------------------- MODULE SequencesTheorems -------------------------
EXTENDS Integers, Sequences

THEOREM Arithmetic == TRUE
   (*{by (cooper) }*)
PROOF OMITTED

THEOREM Force == TRUE
   (*{ by (isabelle "force") }*)
PROOF OMITTED

THEOREM Auto == TRUE
   (*{ by (isabelle "auto") }*)
PROOF OMITTED

THEOREM SetEquality == TRUE (*{ by (isabelle "(auto intro: setEqualI)") }*)
PROOF OMITTED

THEOREM DotDotDef == \A a, b : a..b = {x \in Int : a \leq x /\ x \leq b}
PROOF OMITTED
------------------------------------------------------------------

AXIOM SeqDef == \A S : Seq(S) = UNION {[1..n -> S] : n \in Nat}

AXIOM LenAxiom == \A S :
                   \A seq \in Seq(S) :  /\ Len(seq) \in Nat
                                        /\ seq \in [1..Len(seq) -> S]
THEOREM LenDomain == \A S :
                       \A s \in Seq(S) :
                         \A n \in Nat : DOMAIN s = 1..n => n = Len(s)
<1>1. \A m, n \in Nat : (1..n = 1..m) => (n=m)
  <2>1. \A m, n \in Nat : (\A x \in Nat : (x \in 1..n) <=> (x \in 1..m))
                           => (n = m)
    BY Arithmetic
  <2>2. QED
    BY <2>1, SetEquality
<1>2. SUFFICES ASSUME NEW S,
                      NEW s \in Seq(S),
                      NEW n \in Nat,
                      DOMAIN s = 1..n
               PROVE  n = Len(s)
  BY <1>2
<1>3. /\ Len(s) \in Nat
      /\ s \in [1..Len(s) -> S]
  BY LenAxiom
<1>4. DOMAIN s = 1..Len(s)
  BY <1>3
<1>6. QED
  BY <1>1, <1>2, <1>3, <1>4


AXIOM LenDef == \A S : \A seq \in Seq(S) : DOMAIN seq = 1..Len(seq)

AXIOM HeadDef == \A s : Head(s) = s[1]
AXIOM TailDef == \A s : Tail(s) = [i \in 1..(Len(s)-1) |-> s[i+1]]

AXIOM SubSeqDef ==
        \A s, m, n : SubSeq(s, m, n) = [i \in 1..(1+n-m) |-> s[i+m-1]]

THEOREM InitialSubSeq ==
          \A S :
            \A s \in Seq(S) :
              \A j \in 0..Len(s) :
                  /\ SubSeq(s, 1, j) = [i \in 1..j |-> s[i]]
                  /\ SubSeq(s, 1, j) \in Seq(S)
                  /\ Len(SubSeq(s, 1, j)) = j
<1>1. SUFFICES ASSUME NEW S,
                      NEW s \in Seq(S),
                      NEW j \in 0..Len(s)
               PROVE  /\ SubSeq(s, 1, j) = [i \in 1..j |-> s[i]]
                      /\ SubSeq(s, 1, j) \in Seq(S)
                      /\ Len(SubSeq(s, 1, j)) = j
  BY <1>1
<1>2. SubSeq(s, 1, j) = [i \in 1..j |-> s[i]]
  <2>1. SubSeq(s, 1, j) = [i \in 1..(1+j-1) |-> s[i+1-1]]
    BY SubSeqDef
  <2>2. \A k \in Int : /\ (1+k-1) =k
                       /\ k+1-1 = k
    BY Arithmetic
  <2>3. j \in Int
    BY DotDotDef
  <2>4. SubSeq(s, 1, j) = [i \in 1..j |-> s[i+1-1]]
    BY <2>1, <2>2, <2>3
  <2>5. ASSUME NEW i \in 1..j
        PROVE  s[i+1-1] = s[i]
    <3>1. i \in Int
      BY DotDotDef
    <3>2. QED
      BY <3>1, <2>2
  <2>6. QED
    BY <2>4, <2>5
<1>3. /\ SubSeq(s, 1, j) \in Seq(S)
      /\ Len(SubSeq(s, 1, j)) = j
  <2>1. /\ s \in [1..Len(s) -> S]
        /\ Len(s) \in Nat
    BY LenAxiom
  <2>2. \A i \in 1..Len(s) : s[i] \in S
    BY <2>1
  <2>6. /\ j \in Nat
        /\ j \leq Len(s)
    <3>1. \A n \in Nat : \A m \in 0..n : /\ m \in Nat
                                         /\ m \leq n
      BY Arithmetic
    <3>2. QED
      BY <2>1, <3>1
  <2>3. 1..j \subseteq 1..Len(s)
    <3>1. \A m, n \in Nat : m \leq n => \A p \in 1..m: p \in 1..n
      BY Arithmetic
    <3>2. QED
      BY <3>1, <2>1, <2>6
  <2>4. \A i \in 1..j : s[i] \in S
    BY <2>2, <2>3
  <2>5. SubSeq(s, 1, j) \in  [1..j -> S]
    BY <2>4, <1>2
  <2>7. SubSeq(s, 1, j) \in Seq(S)
    <3> DEFINE F(i) == 1..i
    <3>1. Seq(S) = UNION {[F(n) -> S] : n \in Nat}
      BY SeqDef
    <3>2. SubSeq(s, 1, j) \in [F(j) -> S]
      BY <2>5
    <3> HIDE DEF F
    <3>3. QED
      BY <3>1, <3>2, <2>6
  <2>8. Len(SubSeq(s, 1, j)) = j
    <3>1. DOMAIN SubSeq(s, 1, j) = 1..Len(SubSeq(s,1,j))
      BY <2>7, LenDef
    <3>2. 1..j = 1..Len(SubSeq(s,1,j))
      BY <3>1, <2>5
    <3>3. ASSUME NEW m \in Nat,
                 NEW n \in Nat,
                 1..m = 1..n
          PROVE m = n
       <4>1. (\A p \in Int : (1 \leq p) => ((p \leq m) <=> (p \leq n)))
                => (m = n)
         BY Arithmetic
       <4>2. \A p \in Int : (p \in 1..m) <=> (p \in 1..n)
         BY <3>3
       <4>3. \A p \in Int : /\ (p \in 1..m) <=> (1 \leq p) /\ (p \leq m)
                            /\ (p \in 1..n) <=> (1 \leq p) /\ (p \leq n)
         BY DotDotDef
       <4>4. \A p \in Int : ((1 \leq p) /\ (p \leq m)) <=>
                               ((1 \leq p) /\ (p \leq n))
         BY <4>2, <4>3
       <4>5. \A p \in Int : (1 \leq p) =>
                               ((p \leq m) <=> (p \leq n))
         BY <4>4
       <4>6. QED
         BY <4>1, <4>5
    <3>4. Len(SubSeq(s, 1, j)) \in Nat
      BY <2>7, LenAxiom
    <3>5. QED
      BY <3>2, <3>3, <3>4, <2>6
  <2>9. QED
    BY <2>7, <2>8
<1>4. QED
  BY <1>2, <1>3


------------------------------------------------------------------
THEOREM LenInNat == \A S : \A seq \in Seq(S) : Len(seq) \in Nat
BY LenAxiom
-----------------------------------------------------------------------------
THEOREM ElementOfSeq == \A S :
                          \A seq \in Seq(S) :
                            \A n \in 1..Len(seq) : seq[n] \in S
<1>1. SUFFICES ASSUME NEW S,
                      NEW seq \in Seq(S),
                      NEW n \in 1..Len(seq)
               PROVE  seq[n] \in S
  BY <1>1
<1>2. seq \in [1..Len(seq) -> S]
 BY LenAxiom
<1>3. QED
  BY <1>2
------------------------------------------------------------------
THEOREM EmptySeq ==
           \A S : /\ << >> \in Seq(S)
                  /\ \A seq \in Seq(S) : (seq = << >>) <=> (Len(seq) = 0)
<1>1. SUFFICES ASSUME NEW S
               PROVE /\ << >> \in Seq(S)
                     /\ \A seq \in Seq(S) : (seq = << >>) <=> (Len(seq) = 0)
  BY <1>1
<1>2. << >> \in Seq(S)
  OBVIOUS
<1>3. ASSUME NEW seq \in Seq(S)
      PROVE  (seq = << >>) <=> (Len(seq) = 0)
  <2>0. \A n \in Nat : (1..n = {}) <=> (n = 0)
    <3>1. \A  n \in Nat : (\E j \in 1..n : TRUE ) <=> (n>0)
      BY Arithmetic
    <3>2. SUFFICES ASSUME NEW n \in Nat
                   PROVE  (1..n = {}) <=> (n=0)
      BY <3>2
    <3>3. (1..n # {}) <=> \E j \in 1..n : TRUE
      OBVIOUS
    <3>4. (\E j \in 1..n : TRUE) <=> (n > 0)
      BY <3>1
    <3>5. (1..n = {}) <=> ~ (n > 0)
      BY <3>3, <3>4
    <3>6. \A i \in Nat : ~(i > 0) <=> (i = 0)
      BY Arithmetic
    <3>7. QED
      BY <3>5, <3>6
  <2>1. ASSUME seq = << >>
        PROVE  Len(seq) = 0
    <3>1. 1..0 = {}
      <4>1. (0 \in Nat)
        BY Arithmetic
      <4>2. QED
        BY <4>1, <2>0
    <3>2. << >> \in [{} -> S]
      OBVIOUS
    <3>3. \A T : T # {} => << >> \notin [T -> S]
      BY <3>2
    <3>4. /\ Len(<<>>) \in Nat
          /\ << >> \in [1..Len(<<>>) -> S]
      BY LenAxiom, <2>1
    <3>5. 1..Len(<<>>) = {}
      BY <3>2, <3>3, <3>4
    <3>6. QED
      BY <3>5, <3>4, <2>0, <2>1
  <2>2. ASSUME Len(seq) = 0
        PROVE  seq = << >>
    <3>1. \A f : f \in [{} -> S] => f = << >>
      OBVIOUS
    <3>2. seq \in [1..0 -> S]
      BY LenAxiom, <2>2
    <3>3. 1..0 = {}
      <4>1. (0 \in Nat)
        BY Arithmetic
      <4>2. QED
        BY <4>1, <2>0
    <3>4. QED
      BY <3>1, <3>2, <3>3
  <2>3. QED
    BY <2>1, <2>2
<1>4. QED
  BY <1>2, <1>3
------------------------------------------------------------------
THEOREM HeadAndTailOfSeq ==
          \A S :
            \A seq \in Seq(S) :
               (seq # << >>) => /\ Head(seq) \in S
                                /\ Tail(seq) \in Seq(S)
  (*************************************************************************)
  (* Note: the way Tail is defined, Tail(<< >>) \in Seq(S) is actually     *)
  (* valid (because Tail(<< >>) = << >>).                                  *)
  (*************************************************************************)
<1>1. SUFFICES ASSUME NEW S,
                      NEW seq \in Seq(S),
                      seq # << >>
               PROVE  /\ Head(seq) \in S
                      /\ Tail(seq) \in Seq(S)
  BY <1>1
<1>2. /\ Len(seq) \in Nat
      /\ Len(seq) # 0
  BY LenAxiom, EmptySeq, <1>1
<1>3. Head(seq) \in S
  <2>1. 1 \in 1..Len(seq)
    <3>1. \A n \in Nat : n # 0 => 1 \in 1..n
      BY Arithmetic
    <3>2. QED
      BY <3>1, <1>2
 <2>2. seq \in [1..Len(seq) -> S]
   BY LenAxiom
  <2>3. QED
    BY <2>1, <2>2, HeadDef
<1>4. Tail(seq) \in Seq(S)
  <2>1. \A i \in Nat : /\ \A j \in 1..(i-1) : j+1 \in 1..i
                       /\ i # 0 => (i-1) \in Nat
    BY Arithmetic
  <2>2. \A i \in 1..(Len(seq)-1) : i+1 \in 1..Len(seq)
    BY <2>1, <1>2
  <2>3. Tail(seq) = [i \in 1..(Len(seq)-1) |-> seq[i+1]]
    BY TailDef
  <2>4. /\ seq \in [1..Len(seq) -> S]
    BY LenAxiom
  <2>5. \A i \in 1..(Len(seq)-1) : Tail(seq)[i] \in S
    BY <2>2, <2>3, <2>4
  <2>6. Tail(seq) \in [1..(Len(seq)-1) -> S]
    BY <2>3, <2>5
  <2>7. Len(seq)-1 \in Nat
    BY <1>2, <2>1
  <2>7a. Seq(S) = UNION {[1..n -> S] : n \in Nat}
    BY SeqDef
  <2>8 QED
    BY <2>6, <2>7, <2>7a
<1>5. QED
  BY <1>3, <1>4
------------------------------------------------------------------
Remove(i, seq) == [j \in 1..(Len(seq)-1) |->
                                   IF j < i THEN seq[j] ELSE seq[j+1]]
THEOREM RemoveSeq ==
           \A S :
            \A seq \in Seq(S) :
             \A i \in 1..Len(seq) : Remove(i, seq) \in Seq(S)
<1>1. SUFFICES ASSUME NEW S,
                      NEW seq \in Seq(S),
                      NEW i \in 1..Len(seq)
               PROVE   Remove(i, seq) \in Seq(S)
  BY <1>1 
<1>2. /\ Len(seq) \in Nat
      /\ seq \in [1..Len(seq) -> S]
  BY LenAxiom
<1>3. \A j \in 1..(Len(seq)-1) :
         /\ j < i => j \in 1..Len(seq)
         /\ ~(j < i) => j+1 \in 1..Len(seq)
  <2>1. \A lenseq \in Nat :
         \A ii \in 1..lenseq:
           \A j \in 1..(lenseq-1) :
               /\ j < i => j \in 1..lenseq
               /\ ~(j < i) => j+1 \in 1..lenseq
    BY Arithmetic
  <2>2. QED
    BY <2>1
<1>4. \A j \in 1..(Len(seq)-1) :
          (IF j < i THEN seq[j] ELSE seq[j+1]) \in S
  BY <1>3, <1>2
<1>5. Remove(i, seq) \in [1..(Len(seq)-1) -> S]
  BY <1>4 DEF Remove

<1>6. CASE Len(seq)-1 \in Nat
\* This seems to be another Zenon bug  BY <1>5, SeqDef
PROOF OMITTED
<1>7. CASE Len(seq)-1 \notin Nat
  <2>1. \A n \in Nat : n-1 \notin Nat => 1..(n-1) = 1..0
    <3>1. SUFFICES ASSUME NEW n \in Nat,
                          n-1 \notin Nat
                   PROVE 1..(n-1) = 1..0
      BY <3>1
    <3>2. n-1 < 0
      BY Arithmetic, <3>1
    <3>3. \A j \in Int : (1 \leq j /\ j \leq n-1)
                           <=> (1 \leq j /\ j \leq 0)
      BY Arithmetic, <3>1
    <3>4. QED
      BY <3>3, DotDotDef
  <2>2. 1..Len(seq)-1 = 1..0
    BY <2>1, <1>2, <1>7
  <2>3.  Remove(i, seq) \in [1..0 -> S]
    BY <1>5, <2>2
  <2>4. (0 \in Nat)
    BY Arithmetic
  <2>5. QED
\* XXX Zenon bug again:    BY <2>3, <2>4, SeqDef
PROOF OMITTED
<1>8. QED
  BY <1>6, <1>7

-----------------------------------------------------------------------------
(***************************************************************************)
(*                                    Append                               *)
(***************************************************************************)
THEOREM AppendDef ==
          \A seq, elt :
             Append(seq, elt) =
                [i \in 1..(Len(seq)+1) |-> IF i \leq Len(seq) THEN seq[i]
                                                              ELSE elt]
PROOF OMITTED

THEOREM AppendProperties ==
          \A S :
            \A seq \in Seq(S), elt \in S :
                /\ Append(seq, elt) \in Seq(S)
                /\ Len(Append(seq, elt)) = Len(seq)+1
                /\ \A i \in 1.. Len(seq) : Append(seq, elt)[i] = seq[i]
                /\ Append(seq, elt)[Len(seq)+1] = elt
PROOF OMITTED
-----------------------------------------------------------------------------
(***************************************************************************)
(*                           Concatenation (\o)                            *)
(***************************************************************************)
THEOREM ConcatDef ==
           \A s1, s2 : s1 \o s2 =
                         [i \in 1..(Len(s1)+Len(s2)) |->
                           IF i \leq Len(s1) THEN s1[i]
                                             ELSE s2[i-Len(s1)]]
PROOF OMITTED

THEOREM ConcatProperties ==
           \A S :
             \A s1, s2 \in Seq(S) :
                 /\ s1 \o s2 \in Seq(S)
                 /\ Len(s1 \o s2) = Len(s1) + Len(s2)
PROOF OMITTED

THEOREM ConcatEmptySeq ==
          \A S : \A seq \in Seq(S) : /\ seq \o << >> = seq
                                     /\ << >> \o seq = seq
PROOF OMITTED
-----------------------------------------------------------------------------
(***************************************************************************)
(*                           Head and Tail                                 *)
(***************************************************************************)
THEOREM TailProp == \A S :
                    \A seq \in Seq(S) :
                       seq # << >> =>
                         /\ Tail(seq) \in Seq(S)
                         /\ Len(Tail(seq)) = Len(seq) - 1
                         /\ \A i \in 1..Len(Tail(seq)) :
                                 /\ i+1 \in 1..Len(seq)
                                 /\ Tail(seq)[i] = seq[i+1]
PROOF OMITTED


=============================================================================
