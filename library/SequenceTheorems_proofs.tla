----------------------- MODULE SequenceTheorems_proofs ----------------------
(***************************************************************************)
(* This module contains the proofs for theorems about sequences and the    *)
(* corresponding operations.                                               *)
(***************************************************************************)
EXTENDS Sequences, Functions
LOCAL INSTANCE NaturalsInduction
LOCAL INSTANCE TLAPS


(***************************************************************************)
(* Elementary properties about Seq(S)                                      *)
(***************************************************************************)

LEMMA SeqDef == \A S : Seq(S) = UNION {[1..n -> S] : n \in Nat}
OBVIOUS

THEOREM SeqMonotonic ==
  ASSUME NEW S, NEW T, NEW seq \in Seq(S),
         S \subseteq T
  PROVE  seq \in Seq(T)
OBVIOUS

THEOREM ElementOfSeq ==
   ASSUME NEW S, NEW seq \in Seq(S),
          NEW n \in 1..Len(seq)
   PROVE  seq[n] \in S
OBVIOUS
 
THEOREM EmptySeq ==
   ASSUME NEW S
   PROVE /\ << >> \in Seq(S)
         /\ Len(<< >>) = 0
         /\ \A seq \in Seq(S) : (seq # << >>) => (Len(seq) \in Nat \ {0})
OBVIOUS

THEOREM LenProperties == 
  ASSUME NEW S, NEW seq \in Seq(S)
  PROVE  /\ Len(seq) \in Nat
         /\ seq \in [1..Len(seq) -> S]
         /\ DOMAIN seq = 1 .. Len(seq) 
OBVIOUS

THEOREM IsASeq ==
  ASSUME NEW n \in Nat, NEW e(_), NEW S,
         \A i \in 1..n : e(i) \in S
  PROVE  [i \in 1..n |-> e(i)] \in Seq(S)
OBVIOUS

THEOREM ExceptSeq ==
  ASSUME NEW S, NEW seq \in Seq(S), NEW i \in 1 .. Len(seq), NEW e \in S
  PROVE  /\ [seq EXCEPT ![i] = e] \in Seq(S)
         /\ Len([seq EXCEPT ![i] = e]) = Len(seq)
         /\ \A j \in 1 .. Len(seq) : [seq EXCEPT ![i] = e][j] = IF j=i THEN e ELSE seq[j]
OBVIOUS

THEOREM SeqEqual ==
  ASSUME NEW S, NEW s \in Seq(S), NEW t \in Seq(S),
         Len(s) = Len(t), \A i \in 1 .. Len(s) : s[i] = t[i]
  PROVE  s = t
OBVIOUS

(**************************************************************************)
(* Properties of concatenation (\o)                                       *)
(**************************************************************************)

THEOREM ConcatProperties ==
  ASSUME NEW S, NEW s1 \in Seq(S), NEW s2 \in Seq(S)
  PROVE  /\ s1 \o s2 \in Seq(S)
         /\ Len(s1 \o s2) = Len(s1) + Len(s2)
         /\ \A i \in 1 .. Len(s1) + Len(s2) : (s1 \o s2)[i] =
                     IF i <= Len(s1) THEN s1[i] ELSE s2[i - Len(s1)]
OBVIOUS

THEOREM ConcatEmptySeq ==
  ASSUME NEW S, NEW seq \in Seq(S)
  PROVE  /\ seq \o << >> = seq
         /\ << >> \o seq = seq
OBVIOUS

THEOREM ConcatEqualIffEmpty ==
  ASSUME NEW S, NEW s \in Seq(S), NEW t \in Seq(S)
  PROVE  /\ s \o t = s <=> t = << >>
         /\ s \o t = t <=> s = << >>
         /\ s \o t = << >> <=> s = << >> /\ t = << >>
OBVIOUS

THEOREM ConcatAssociative ==
  ASSUME NEW S, NEW s \in Seq(S), NEW t \in Seq(S), NEW u \in Seq(S)
  PROVE  (s \o t) \o u = s \o (t \o u)
OBVIOUS
(*
<1>. DEFINE lhs == (s \o t) \o u
            rhs == s \o (t \o u)
<1>. lhs \in Seq(S) /\ rhs \in Seq(S)  OBVIOUS
<1>1. Len(lhs) = Len(rhs)  OBVIOUS
<1>2. \A i \in 1 .. Len(lhs) : lhs[i] = rhs[i]  OBVIOUS
<1>. QED  BY <1>1, <1>2, SeqEqual, Zenon
*)

(****************************************************************************)
(* Intentionally not written as an ASSUME ... PROVE such that the conjuncts *)
(* can be named individually.                                               *)
(****************************************************************************)
THEOREM ConcatSimplifications ==
  /\ idRight:: \A S : \A s,t \in Seq(S) : s \o t = s => t = <<>>
  /\ idLeft:: \A S : \A s,t \in Seq(S) : s \o t = t => s = <<>>
  /\ concIsEmpty:: \A S : \A s,t \in Seq(S) : s \o t = <<>> => s = <<>> /\ t = <<>>
  /\ cancelLeft:: \A S : \A s,t,v \in Seq(S) : s \o t = s \o v => t = v
  /\ cancelRight:: \A S : \A s,t,v \in Seq(S) : s \o v = t \o v => s = t
OBVIOUS

(***************************************************************************)
(*                     SubSeq, Head and Tail                               *)
(***************************************************************************)

THEOREM SubSeqProperties ==
  ASSUME NEW S, NEW s, NEW m \in Int, NEW n \in Int,
         \A i \in m .. n : s[i] \in S
   PROVE /\ SubSeq(s,m,n) \in Seq(S)
         /\ Len(SubSeq(s,m,n)) = IF m<=n THEN n-m+1 ELSE 0
         /\ \A i \in 1 .. n-m+1 : SubSeq(s,m,n)[i] = s[m+i-1]
OBVIOUS

THEOREM SubSeqEmpty ==
  ASSUME NEW s, NEW m \in Int, NEW n \in Int, n < m
  PROVE  SubSeq(s,m,n) = << >>
OBVIOUS

THEOREM SubSeqRange ==
  ASSUME NEW S, NEW s \in Seq(S), NEW m \in 1 .. Len(s), NEW n \in 1 .. Len(s)
  PROVE  Range(SubSeq(s,m,n)) \subseteq Range(s)
BY DEF Range

THEOREM HeadTailProperties ==
   ASSUME NEW S,
          NEW s \in Seq(S), s # << >>
   PROVE  /\ Head(s) \in S
          /\ Head(s) \in Range(s)
          /\ Tail(s) \in Seq(S)
          /\ Len(Tail(s)) = Len(s)-1
          /\ \A i \in 1 .. Len(Tail(s)) : Tail(s)[i] = s[i+1]
          /\ Range(Tail(s)) \subseteq Range(s)
BY DEF Range

THEOREM TailIsSubSeq ==
  ASSUME NEW S,
         NEW s \in Seq(S), s # << >>
  PROVE  Tail(s) = SubSeq(s, 2, Len(s))
OBVIOUS

THEOREM SubSeqRestrict ==
  ASSUME NEW S, NEW seq \in Seq(S), NEW n \in 0 .. Len(seq)
  PROVE  SubSeq(seq, 1, n) = Restrict(seq, 1 .. n)
BY DEF Restrict

THEOREM HeadTailOfSubSeq ==
  ASSUME NEW S, NEW seq \in Seq(S),
         NEW m \in 1 .. Len(seq), NEW n \in m .. Len(seq)
  PROVE  /\ Head(SubSeq(seq,m,n)) = seq[m]
         /\ Tail(SubSeq(seq,m,n)) = SubSeq(seq, m+1, n)
OBVIOUS

THEOREM SubSeqRecursive ==
  ASSUME NEW S, NEW seq \in Seq(S),
         NEW m \in 1 .. Len(seq), NEW n \in m .. Len(seq)
  PROVE  /\ SubSeq(seq, m, n) = << seq[m] >> \o SubSeq(seq, m+1, n)
         /\ SubSeq(seq, m, n) = SubSeq(seq, m, n-1) \o << seq[n] >>
OBVIOUS

(***************************************************************************)
(* Subsequences of subsequences.                                           *)
(***************************************************************************)
THEOREM SubSeqOfSubSeq ==
  ASSUME NEW S, NEW s \in Seq(S), NEW t \in Seq(S),
         NEW i \in 1 .. Len(s), NEW j \in 1 .. Len(s),
         NEW m \in 1 .. j-i+1, NEW n \in 1 .. j-i+1
  PROVE  SubSeq(SubSeq(s,i,j),m,n) = SubSeq(s, i+m-1, i+n-1)
OBVIOUS

(*****************************************************************************)
(* Adjacent subsequences can be concatenated to obtain a longer subsequence. *)
(*****************************************************************************)
THEOREM ConcatAdjacentSubSeq ==
  ASSUME NEW S, NEW seq \in Seq(S), 
         NEW m \in 1 .. Len(seq)+1, 
         NEW k \in m-1 .. Len(seq), 
         NEW n \in k .. Len(seq)
  PROVE  SubSeq(seq, m, k) \o SubSeq(seq, k+1, n) = SubSeq(seq, m, n)
OBVIOUS

(***************************************************************************)
(* Special cases of subsequences of concatenations.                        *)
(***************************************************************************)
THEOREM SubSeqOfConcat1 ==
  ASSUME NEW S, NEW s \in Seq(S), NEW t \in Seq(S),
         NEW m \in 1 .. Len(s), NEW n \in 1 .. Len(s)
  PROVE  SubSeq(s \o t, m, n) = SubSeq(s, m, n)
OBVIOUS

THEOREM SubSeqOfConcat2 ==
  ASSUME NEW S, NEW s \in Seq(S), NEW t \in Seq(S),
         NEW m \in Len(s)+1 .. Len(s)+Len(t), NEW n \in Len(s)+1 .. Len(s)+Len(t)
  PROVE  SubSeq(s \o t, m, n) = SubSeq(t, m - Len(s), n - Len(s))
OBVIOUS

(***************************************************************************)
(* Theorems about Append                                                   *)
(***************************************************************************)

THEOREM AppendProperties ==
  ASSUME NEW S, NEW seq \in Seq(S), NEW elt \in S
  PROVE  /\ Append(seq, elt) \in Seq(S)
         /\ Append(seq, elt) # << >>
         /\ Len(Append(seq, elt)) = Len(seq)+1
         /\ \A i \in 1.. Len(seq) : Append(seq, elt)[i] = seq[i]
         /\ Append(seq, elt)[Len(seq)+1] = elt
         /\ Range(Append(seq, elt)) = Range(seq) \cup {elt}
BY DEF Range

THEOREM AppendIsConcat ==
  ASSUME NEW S, NEW seq \in Seq(S), NEW elt \in S
  PROVE  Append(seq, elt) = seq \o <<elt>>
OBVIOUS

THEOREM HeadTailAppend ==
  ASSUME NEW S, NEW seq \in Seq(S), NEW elt
  PROVE  /\ Head(Append(seq, elt)) = IF seq = <<>> THEN elt ELSE Head(seq)
         /\ Tail(Append(seq, elt)) = IF seq = <<>> THEN <<>> ELSE Append(Tail(seq), elt)
OBVIOUS

THEOREM AppendInjective ==
  ASSUME NEW S, NEW e \in S, NEW s \in Seq(S), NEW f \in S, NEW t \in Seq(S)
  PROVE  Append(s,e) = Append(t,f) <=> s = t /\ e = f
OBVIOUS

THEOREM SequenceEmptyOrAppend == 
  ASSUME NEW S, NEW seq \in Seq(S), seq # << >>
  PROVE \E s \in Seq(S), elt \in S : seq = Append(s, elt)
<1>. DEFINE front == [i \in 1 .. Len(seq)-1 |-> seq[i]]
            last == seq[Len(seq)]
<1>. /\ front \in Seq(S)
     /\ last \in S
     /\ seq = Append(front, last)
  OBVIOUS
<1>. QED  BY Zenon

(***************************************************************************)
(* Inductive reasoning for sequences                                       *)
(***************************************************************************)

THEOREM SequencesInductionAppend ==
  ASSUME NEW P(_), NEW S, 
         P(<< >>),
         \A s \in Seq(S), e \in S : P(s) => P(Append(s,e))
  PROVE  \A seq \in Seq(S) : P(seq)
<1>. DEFINE Q(n) == \A seq \in Seq(S) : Len(seq) = n => P(seq)
<1>. SUFFICES \A k \in Nat : Q(k)
  OBVIOUS
<1>1. Q(0)
  OBVIOUS
<1>2. ASSUME NEW n \in Nat, Q(n)
      PROVE  Q(n+1)
  <2>. SUFFICES ASSUME NEW s \in Seq(S), Len(s) = n+1
                PROVE P(s)
    OBVIOUS
  <2>. PICK seq \in Seq(S), e \in S : s = Append(seq,e) /\ Len(seq) = n
    BY SequenceEmptyOrAppend
  <2>. QED  BY <1>2
<1>3. QED  BY <1>1, <1>2, NatInduction, Isa

THEOREM SequencesInductionTail ==
  ASSUME NEW S,  NEW P(_),
         P(<< >>), 
         \A s \in Seq(S) : (s # << >>) /\ P(Tail(s)) => P(s)
  PROVE  \A s \in Seq(S) : P(s)
<1>. DEFINE Q(n) == \A s \in Seq(S) : Len(s) = n => P(s)
<1>. SUFFICES \A k \in Nat : Q(k)
  OBVIOUS
<1>1. Q(0)
  OBVIOUS
<1>2. ASSUME NEW n \in Nat,  Q(n) 
      PROVE  Q(n+1)
  <2>. SUFFICES ASSUME NEW s \in Seq(S), Len(s) = n+1
                PROVE  P(s)
    OBVIOUS
  <2>1. /\ Tail(s) \in Seq(S)
        /\ Len(Tail(s)) = n
    OBVIOUS
  <2>. QED  BY <2>1, <1>2, Zenon
<1>3. QED  BY <1>1, <1>2, NatInduction, Isa


(***************************************************************************)
(*                          RANGE OF SEQUENCE                              *)
(***************************************************************************)

THEOREM RangeOfSeq == 
  ASSUME NEW S, NEW seq \in Seq(S)
  PROVE  Range(seq) \in SUBSET S
BY DEF Range

THEOREM RangeEquality == 
  ASSUME NEW S, NEW seq \in Seq(S)
  PROVE Range(seq) = { seq[i] : i \in 1 .. Len(seq) }
BY DEF Range

THEOREM SeqOfRange ==
  ASSUME NEW S, NEW seq \in Seq(S)
  PROVE  seq \in Seq(Range(seq))
BY DEF Range

(* The range of the concatenation of two sequences is the union of the ranges *)
THEOREM RangeConcatenation == 
  ASSUME NEW S, NEW s1 \in Seq(S), NEW s2 \in Seq(S)
  PROVE  Range(s1 \o s2) = Range(s1) \cup Range(s2)
<1>1. Range(s1) \subseteq Range(s1 \o s2)
  BY DEF Range
<1>2. Range(s2) \subseteq Range(s1 \o s2)
  <2>1. SUFFICES ASSUME NEW i \in 1 .. Len(s2)
                 PROVE  s2[i] \in Range(s1 \o s2)
    BY RangeEquality
  <2>2. /\ Len(s1)+i \in 1 .. Len(s1 \o s2)
        /\ (s1 \o s2)[Len(s1)+i] = s2[i]
    OBVIOUS
  <2>. QED  BY <2>2 DEF Range
<1>3. Range(s1 \o s2) \subseteq Range(s1) \cup Range(s2)
  BY DEF Range
<1>. QED  BY <1>1, <1>2, <1>3

(***************************************************************************)
(* Theorems about injective sequences, i.e. sequences without duplicates.  *)
(***************************************************************************)

LEMMA EmptySingletonIsInjective ==
  /\ IsInjective(<< >>)
  /\ \A e : IsInjective(<< e >>)
BY DEF IsInjective

LEMMA ConcatInjectiveSeq ==
  ASSUME NEW S, NEW s \in Seq(S), NEW t \in Seq(S)
  PROVE  IsInjective(s \o t) <=> 
         IsInjective(s) /\ IsInjective(t) /\ Range(s) \cap Range(t) = {}
<1>. DEFINE st == s \o t
<1>1. ASSUME IsInjective(st)  PROVE IsInjective(s)
  BY <1>1 DEF IsInjective
<1>2. ASSUME IsInjective(st)  PROVE IsInjective(t)
  <2>1. SUFFICES ASSUME NEW i \in DOMAIN t, NEW j \in DOMAIN t, t[i] = t[j]
                 PROVE  i = j
    BY DEF IsInjective
  <2>2. /\ i + Len(s) \in DOMAIN st
        /\ j + Len(s) \in DOMAIN st
        /\ st[i+Len(s)] = st[j + Len(s)]
    BY <2>1
  <2>. QED  BY <1>2, <2>2 DEF IsInjective
<1>3. ASSUME IsInjective(st), NEW e \in Range(s) \cap Range(t)
      PROVE  FALSE
  <2>1. PICK i \in DOMAIN s : s[i] = e
    BY <1>3 DEF Range
  <2>2. PICK j \in DOMAIN t : t[j] = e
    BY <1>3 DEF Range
  <2>3. /\ i \in DOMAIN st /\ st[i] = e
        /\ j+Len(s) \in DOMAIN st /\ st[j+Len(s)] = e
    BY <2>1, <2>2
  <2>. QED  BY <1>3, <2>3 DEF IsInjective
<1>4. ASSUME IsInjective(s), IsInjective(t), Range(s) \cap Range(t) = {}
      PROVE  IsInjective(st)
  BY <1>4 DEF IsInjective, Range
<1>. QED  BY <1>1, <1>2, <1>3, <1>4

LEMMA AppendInjectiveSeq ==
  ASSUME NEW S, NEW seq \in Seq(S), NEW e \in S
  PROVE  IsInjective(Append(seq,e)) <=> IsInjective(seq) /\ e \notin Range(seq)
<1>. DEFINE app == Append(seq,e)
<1>1. ASSUME IsInjective(app)
      PROVE  IsInjective(seq)
  BY <1>1 DEF IsInjective
<1>2. ASSUME IsInjective(app), e \in Range(seq)
      PROVE  FALSE
  <2>1. PICK i \in DOMAIN seq : seq[i] = e
    BY <1>2 DEF Range
  <2>2. app[i] = e /\ app[Len(seq)+1] = e
    BY <2>1
  <2>. QED
    BY <1>2, <2>2 DEF IsInjective
<1>3. ASSUME IsInjective(seq), e \notin Range(seq)
      PROVE  IsInjective(app)
  BY <1>3 DEF IsInjective, Range
<1>. QED  BY <1>1, <1>2, <1>3

LEMMA TailInjectiveSeq ==
  ASSUME NEW S, NEW seq \in Seq(S), IsInjective(seq), seq # << >>
  PROVE  /\ IsInjective(Tail(seq))
         /\ Range(Tail(seq)) = Range(seq) \ {Head(seq)}
<1>. DEFINE tl == Tail(seq)
<1>1. IsInjective(tl)
  BY DEF IsInjective
<1>2. ASSUME NEW e \in Range(tl)
      PROVE  e \in Range(seq) \ {Head(seq)}
  BY DEF Range, IsInjective
<1>3. ASSUME NEW e \in Range(seq) \ {Head(seq)}
      PROVE  e \in Range(tl)
  <2>1. PICK i \in 2 .. Len(seq) : seq[i] = e
    BY DEF Range
  <2>2. i-1 \in DOMAIN tl /\ tl[i-1] = e
    BY <2>1
  <2>. QED  BY <2>2, Zenon DEF Range
<1>. QED  BY <1>1, <1>2, <1>3

=============================================================================
