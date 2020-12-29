-------------------------- MODULE SequenceTheorems --------------------------
(***************************************************************************)
(* This module contains theorems about operations on sequences.            *)
(***************************************************************************)
EXTENDS Sequences, Functions
LOCAL INSTANCE NaturalsInduction
LOCAL INSTANCE TLAPS


(***************************************************************************)
(* Elementary properties about Seq(S)                                      *)
(***************************************************************************)

LEMMA SeqDef == \A S : Seq(S) = UNION {[1..n -> S] : n \in Nat}

THEOREM SeqMonotonic ==
  ASSUME NEW S, NEW T, NEW seq \in Seq(S),
         S \subseteq T
  PROVE  seq \in Seq(T)

THEOREM ElementOfSeq ==
   ASSUME NEW S, NEW seq \in Seq(S),
          NEW n \in 1..Len(seq)
   PROVE  seq[n] \in S
 
THEOREM EmptySeq ==
   ASSUME NEW S
   PROVE /\ << >> \in Seq(S)
         /\ Len(<< >>) = 0
         /\ \A seq \in Seq(S) : (seq # << >>) => (Len(seq) \in Nat \ {0})

THEOREM LenProperties == 
  ASSUME NEW S, NEW seq \in Seq(S)
  PROVE  /\ Len(seq) \in Nat
         /\ seq \in [1..Len(seq) -> S]
         /\ DOMAIN seq = 1 .. Len(seq) 

THEOREM IsASeq ==
  ASSUME NEW n \in Nat, NEW e(_), NEW S,
         \A i \in 1..n : e(i) \in S
  PROVE  [i \in 1..n |-> e(i)] \in Seq(S)

THEOREM ExceptSeq ==
  ASSUME NEW S, NEW seq \in Seq(S), NEW i \in 1 .. Len(seq), NEW e \in S
  PROVE  /\ [seq EXCEPT ![i] = e] \in Seq(S)
         /\ Len([seq EXCEPT ![i] = e]) = Len(seq)
         /\ \A j \in 1 .. Len(seq) : [seq EXCEPT ![i] = e][j] = IF j=i THEN e ELSE seq[j]

THEOREM SeqEqual ==
  ASSUME NEW S, NEW s \in Seq(S), NEW t \in Seq(S),
         Len(s) = Len(t), \A i \in 1 .. Len(s) : s[i] = t[i]
  PROVE  s = t

(**************************************************************************)
(* Properties of concatenation (\o)                                       *)
(**************************************************************************)

THEOREM ConcatProperties ==
  ASSUME NEW S, NEW s1 \in Seq(S), NEW s2 \in Seq(S)
  PROVE  /\ s1 \o s2 \in Seq(S)
         /\ Len(s1 \o s2) = Len(s1) + Len(s2)
         /\ \A i \in 1 .. Len(s1) + Len(s2) : (s1 \o s2)[i] =
                     IF i <= Len(s1) THEN s1[i] ELSE s2[i - Len(s1)]

THEOREM ConcatEmptySeq ==
  ASSUME NEW S, NEW seq \in Seq(S)
  PROVE  /\ seq \o << >> = seq
         /\ << >> \o seq = seq

THEOREM ConcatEqualIffEmpty ==
  ASSUME NEW S, NEW s \in Seq(S), NEW t \in Seq(S)
  PROVE  /\ s \o t = s <=> t = << >>
         /\ s \o t = t <=> s = << >>
         /\ s \o t = << >> <=> s = << >> /\ t = << >>

THEOREM ConcatAssociative ==
  ASSUME NEW S, NEW s \in Seq(S), NEW t \in Seq(S), NEW u \in Seq(S)
  PROVE  (s \o t) \o u = s \o (t \o u)

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

(***************************************************************************)
(*                     SubSeq, Head and Tail                               *)
(***************************************************************************)

THEOREM SubSeqProperties ==
  ASSUME NEW S, NEW s, NEW m \in Int, NEW n \in Int,
         \A i \in m .. n : s[i] \in S
   PROVE /\ SubSeq(s,m,n) \in Seq(S)
         /\ Len(SubSeq(s,m,n)) = IF m<=n THEN n-m+1 ELSE 0
         /\ \A i \in 1 .. n-m+1 : SubSeq(s,m,n)[i] = s[m+i-1]

THEOREM SubSeqEmpty ==
  ASSUME NEW s, NEW m \in Int, NEW n \in Int, n < m
  PROVE  SubSeq(s,m,n) = << >>

THEOREM SubSeqRange ==
  ASSUME NEW S, NEW s \in Seq(S), NEW m \in 1 .. Len(s), NEW n \in 1 .. Len(s)
  PROVE  Range(SubSeq(s,m,n)) \subseteq Range(s)

THEOREM HeadTailProperties ==
   ASSUME NEW S,
          NEW s \in Seq(S), s # << >>
   PROVE  /\ Head(s) \in S
          /\ Head(s) \in Range(s)
          /\ Tail(s) \in Seq(S)
          /\ Len(Tail(s)) = Len(s)-1
          /\ \A i \in 1 .. Len(Tail(s)) : Tail(s)[i] = s[i+1]
          /\ Range(Tail(s)) \subseteq Range(s)

THEOREM TailIsSubSeq ==
  ASSUME NEW S,
         NEW s \in Seq(S), s # << >>
  PROVE  Tail(s) = SubSeq(s, 2, Len(s))

THEOREM SubSeqRestrict ==
  ASSUME NEW S, NEW seq \in Seq(S), NEW n \in 0 .. Len(seq)
  PROVE  SubSeq(seq, 1, n) = Restrict(seq, 1 .. n)

THEOREM HeadTailOfSubSeq ==
  ASSUME NEW S, NEW seq \in Seq(S),
         NEW m \in 1 .. Len(seq), NEW n \in m .. Len(seq)
  PROVE  /\ Head(SubSeq(seq,m,n)) = seq[m]
         /\ Tail(SubSeq(seq,m,n)) = SubSeq(seq, m+1, n)

THEOREM SubSeqRecursive ==
  ASSUME NEW S, NEW seq \in Seq(S),
         NEW m \in 1 .. Len(seq), NEW n \in m .. Len(seq)
  PROVE  /\ SubSeq(seq, m, n) = << seq[m] >> \o SubSeq(seq, m+1, n)
         /\ SubSeq(seq, m, n) = SubSeq(seq, m, n-1) \o << seq[n] >>

(***************************************************************************)
(* Subsequences of subsequences.                                           *)
(***************************************************************************)
THEOREM SubSeqOfSubSeq ==
  ASSUME NEW S, NEW s \in Seq(S), NEW t \in Seq(S),
         NEW i \in 1 .. Len(s), NEW j \in 1 .. Len(s),
         NEW m \in 1 .. j-i+1, NEW n \in 1 .. j-i+1
  PROVE  SubSeq(SubSeq(s,i,j),m,n) = SubSeq(s, i+m-1, i+n-1)

(*****************************************************************************)
(* Adjacent subsequences can be concatenated to obtain a longer subsequence. *)
(*****************************************************************************)
THEOREM ConcatAdjacentSubSeq ==
  ASSUME NEW S, NEW seq \in Seq(S), 
         NEW m \in 1 .. Len(seq)+1, 
         NEW k \in m-1 .. Len(seq), 
         NEW n \in k .. Len(seq)
  PROVE  SubSeq(seq, m, k) \o SubSeq(seq, k+1, n) = SubSeq(seq, m, n)

(***************************************************************************)
(* Special cases of subsequences of concatenations.                        *)
(***************************************************************************)
THEOREM SubSeqOfConcat1 ==
  ASSUME NEW S, NEW s \in Seq(S), NEW t \in Seq(S),
         NEW m \in 1 .. Len(s), NEW n \in 1 .. Len(s)
  PROVE  SubSeq(s \o t, m, n) = SubSeq(s, m, n)

THEOREM SubSeqOfConcat2 ==
  ASSUME NEW S, NEW s \in Seq(S), NEW t \in Seq(S),
         NEW m \in Len(s)+1 .. Len(s)+Len(t), NEW n \in Len(s)+1 .. Len(s)+Len(t)
  PROVE  SubSeq(s \o t, m, n) = SubSeq(t, m - Len(s), n - Len(s))

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

THEOREM AppendIsConcat ==
  ASSUME NEW S, NEW seq \in Seq(S), NEW elt \in S
  PROVE  Append(seq, elt) = seq \o <<elt>>

THEOREM HeadTailAppend ==
  ASSUME NEW S, NEW seq \in Seq(S), NEW elt
  PROVE  /\ Head(Append(seq, elt)) = IF seq = <<>> THEN elt ELSE Head(seq)
         /\ Tail(Append(seq, elt)) = IF seq = <<>> THEN <<>> ELSE Append(Tail(seq), elt)

THEOREM AppendInjective ==
  ASSUME NEW S, NEW e \in S, NEW s \in Seq(S), NEW f \in S, NEW t \in Seq(S)
  PROVE  Append(s,e) = Append(t,f) <=> s = t /\ e = f

THEOREM SequenceEmptyOrAppend == 
  ASSUME NEW S, NEW seq \in Seq(S), seq # << >>
  PROVE \E s \in Seq(S), elt \in S : seq = Append(s, elt)

(***************************************************************************)
(* Inductive reasoning for sequences                                       *)
(***************************************************************************)

THEOREM SequencesInductionAppend ==
  ASSUME NEW P(_), NEW S, 
         P(<< >>),
         \A s \in Seq(S), e \in S : P(s) => P(Append(s,e))
  PROVE  \A seq \in Seq(S) : P(seq)

THEOREM SequencesInductionTail ==
  ASSUME NEW S,  NEW P(_),
         P(<< >>), 
         \A s \in Seq(S) : (s # << >>) /\ P(Tail(s)) => P(s)
  PROVE  \A s \in Seq(S) : P(s)


(***************************************************************************)
(*                          RANGE OF SEQUENCE                              *)
(***************************************************************************)

THEOREM RangeOfSeq == 
  ASSUME NEW S, NEW seq \in Seq(S)
  PROVE  Range(seq) \in SUBSET S

THEOREM RangeEquality == 
  ASSUME NEW S, NEW seq \in Seq(S)
  PROVE Range(seq) = { seq[i] : i \in 1 .. Len(seq) }

THEOREM SeqOfRange ==
  ASSUME NEW S, NEW seq \in Seq(S)
  PROVE  seq \in Seq(Range(seq))

(* The range of the concatenation of two sequences is the union of the ranges *)
THEOREM RangeConcatenation == 
  ASSUME NEW S, NEW s1 \in Seq(S), NEW s2 \in Seq(S)
  PROVE  Range(s1 \o s2) = Range(s1) \cup Range(s2)

(***************************************************************************)
(* Theorems about injective sequences, i.e. sequences without duplicates.  *)
(***************************************************************************)

LEMMA EmptySingletonIsInjective ==
  /\ IsInjective(<< >>)
  /\ \A e : IsInjective(<< e >>)

LEMMA ConcatInjectiveSeq ==
  ASSUME NEW S, NEW s \in Seq(S), NEW t \in Seq(S)
  PROVE  IsInjective(s \o t) <=> 
         IsInjective(s) /\ IsInjective(t) /\ Range(s) \cap Range(t) = {}

LEMMA AppendInjectiveSeq ==
  ASSUME NEW S, NEW seq \in Seq(S), NEW e \in S
  PROVE  IsInjective(Append(seq,e)) <=> IsInjective(seq) /\ e \notin Range(seq)

LEMMA TailInjectiveSeq ==
  ASSUME NEW S, NEW seq \in Seq(S), IsInjective(seq), seq # << >>
  PROVE  /\ IsInjective(Tail(seq))
         /\ Range(Tail(seq)) = Range(seq) \ {Head(seq)}

=============================================================================
