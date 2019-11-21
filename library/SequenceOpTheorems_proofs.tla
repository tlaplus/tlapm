--------------------- MODULE SequenceOpTheorems_proofs ---------------------
(**************************************************************************)
(* This module contains theorems about the operators on sequences defined *)
(* in module SequenceOps.                                                 *)
(**************************************************************************)
EXTENDS SequenceOps, SequenceTheorems, Integers, NaturalsInduction, 
        WellFoundedInduction, TLAPS

(***************************************************************************)
(* Theorems about Cons.                                                    *)
(* Cons(elt, seq) == <<elt>> \o seq                                        *)
(***************************************************************************)

THEOREM ConsProperties ==
  ASSUME NEW S, NEW seq \in Seq(S), NEW elt \in S
  PROVE /\ Cons(elt, seq) \in Seq(S)
        /\ Cons(elt, seq) # <<>> 
        /\ Len(Cons(elt, seq)) = Len(seq)+1
        /\ Head(Cons(elt, seq)) = elt
        /\ Tail(Cons(elt, seq)) = seq
        /\ Cons(elt, seq)[1] = elt
        /\ \A i \in 1 .. Len(seq) : Cons(elt, seq)[i+1] = seq[i]
        /\ \A i \in 2 .. Len(seq)+1 : Cons(elt, seq)[i] = seq[i-1]
BY DEF Cons

THEOREM ConsEmpty ==
  \A x : Cons(x, << >>) = << x >>
BY DEF Cons

THEOREM ConsHeadTail ==
  ASSUME NEW S, NEW seq \in Seq(S), seq # << >>
  PROVE  Cons(Head(seq), Tail(seq)) = seq
BY DEF Cons

THEOREM ConsAppend ==
  ASSUME NEW S, NEW seq \in Seq(S), NEW x \in S, NEW y \in S
  PROVE  Cons(x, Append(seq, y)) = Append(Cons(x,seq), y)
BY DEF Cons

THEOREM ConsInjective ==
  ASSUME NEW S, NEW e \in S, NEW s \in Seq(S), NEW f \in S, NEW t \in Seq(S)
  PROVE  Cons(e,s) = Cons(f,t) <=> e = f /\ s = t
BY (*Z3*) DEF Cons

THEOREM SequencesInductionCons == 
  ASSUME NEW P(_), NEW S,
         P(<< >>),
         \A s \in Seq(S), e \in S : P(s) => P(Cons(e,s))
  PROVE \A seq \in Seq(S) : P(seq)
<1>. DEFINE Q(n) == \A seq \in Seq(S) : Len(seq) = n => P(seq)
<1>1. SUFFICES \A k \in Nat : Q(k)
  OBVIOUS
<1>2. Q(0)
  OBVIOUS
<1>3. ASSUME NEW n \in Nat, Q(n)
      PROVE  Q(n+1)
  <2>1. ASSUME NEW s \in Seq(S), Len(s) = n+1
        PROVE P(s)
    <3>1. /\ Tail(s) \in Seq(S)
          /\ Head(s) \in S
          /\ Len(Tail(s)) = n
          /\ Cons(Head(s), Tail(s)) = s
      BY <2>1, ConsHeadTail 
    <3>2. P(Tail(s))
      BY <1>3, <3>1, Zenon
    <3>. QED  BY <3>1, <3>2, Zenon                  
  <2>. QED  BY <2>1          
<1>. QED  BY <1>2, <1>3, NatInduction, Isa

(***************************************************************************)
(* Theorems about InsertAt and RemoveAt.                                   *)
(* InsertAt(seq,i,elt) ==                                                  *)
(*   SubSeq(seq, 1, i-1) \o <<elt>> \o SubSeq(seq, i, Len(seq))            *)
(* RemoveAt(seq, i) == SubSeq(seq, 1, i-1) \o SubSeq(seq, i+1, Len(seq))   *)
(***************************************************************************)

THEOREM InsertAtProperties ==
  ASSUME NEW S, NEW seq \in Seq(S), NEW i \in 1 .. Len(seq)+1, NEW elt \in S
  PROVE  /\ InsertAt(seq,i,elt) \in Seq(S)
         /\ Len(InsertAt(seq,i,elt)) = Len(seq)+1
         /\ \A j \in 1 .. Len(seq)+1 : InsertAt(seq,i,elt)[j] =
                     IF j<i THEN seq[j]
                     ELSE IF j=i THEN elt
                     ELSE seq[j-1]
<1>. DEFINE left == SubSeq(seq, 1, i-1)
            mid  == <<elt>>
            right == SubSeq(seq, i, Len(seq))
<1>1. /\ left \in Seq(S) /\ Len(left) = i-1
      /\ mid \in Seq(S)
      /\ right \in Seq(S) /\ Len(right) = Len(seq)-i+1
      /\ InsertAt(seq,i,elt) \in Seq(S)
  BY DEF InsertAt
<1>2. Len(InsertAt(seq,i,elt)) = Len(seq)+1
  <2>1. Len(InsertAt(seq,i,elt)) = Len(left) + 1 + Len(right)
    BY DEF InsertAt
  <2>. HIDE DEF left, right
  <2>. QED  BY <1>1, <2>1
<1>3. ASSUME NEW j \in 1 .. Len(seq)+1
      PROVE  InsertAt(seq,i,elt)[j] = IF j<i THEN seq[j]
                                      ELSE IF j=i THEN elt
                                      ELSE seq[j-1]
  BY ConcatProperties, SubSeqProperties, Z3 DEF InsertAt
<1>. QED
  BY <1>1, <1>2, <1>3

THEOREM RemoveAtProperties ==
   ASSUME NEW S, NEW seq \in Seq(S),
          NEW i \in 1..Len(seq)
   PROVE  /\ RemoveAt(seq,i) \in Seq(S)
          /\ Len(RemoveAt(seq,i)) = Len(seq) - 1
          /\ \A j \in 1 .. Len(seq)-1 : RemoveAt(seq,i)[j] = IF j<i THEN seq[j] ELSE seq[j+1]
BY Z3 DEF RemoveAt

(***************************************************************************)
(* Theorems about Front and Last.                                          *)
(* Front(seq) == SubSeq(seq, 1, Len(seq)-1)                                *)
(* Last(seq) == seq[Len(seq)]                                              *)
(***************************************************************************)

THEOREM FrontProperties ==
  ASSUME NEW S, NEW seq \in Seq(S)
  PROVE  /\ Front(seq) \in Seq(S)
         /\ Len(Front(seq)) = IF seq = << >> THEN 0 ELSE Len(seq)-1
         /\ \A i \in 1 .. Len(seq)-1 : Front(seq)[i] = seq[i]
BY DEF Front

THEOREM FrontOfEmpty == Front(<< >>) = << >>
BY DEF Front

THEOREM LastProperties ==
  ASSUME NEW S, NEW seq \in Seq(S), seq # << >>
  PROVE  /\ Last(seq) \in S 
         /\ Append(Front(seq), Last(seq)) = seq 
BY DEF Front, Last

THEOREM FrontLastOfSubSeq ==
  ASSUME NEW S, NEW seq \in Seq(S),
         NEW m \in 1 .. Len(seq), NEW n \in m .. Len(seq)
  PROVE  /\ Front(SubSeq(seq,m,n)) = SubSeq(seq, m, n-1)
         /\ Last(SubSeq(seq,m,n)) = seq[n]
BY DEF Front, Last

THEOREM FrontLastAppend ==
  ASSUME NEW S, NEW seq \in Seq(S), NEW e \in S
  PROVE  /\ Front(Append(seq, e)) = seq
         /\ Last(Append(seq, e)) = e
BY DEF Front, Last

THEOREM SequencesInductionFront ==
  ASSUME NEW S,  NEW P(_),
         P(<< >>), 
         \A s \in Seq(S) : (s # << >>) /\ P(Front(s)) => P(s)
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
  <2>1. /\ Front(s) \in Seq(S)
        /\ Len(Front(s)) = n
    BY FrontProperties
  <2>. QED  BY <2>1, <1>2
<1>3. QED  BY <1>1, <1>2, NatInduction, Isa

(***************************************************************************)
(* Theorems about Reverse.                                                 *)
(* Reverse(seq) == [j \in 1 .. Len(seq) |-> seq[Len(seq)-j+1] ]            *)
(***************************************************************************)

THEOREM ReverseProperties ==
  ASSUME NEW S, NEW seq \in Seq(S)
  PROVE  /\ Reverse(seq) \in Seq(S)
         /\ Len(Reverse(seq)) = Len(seq)
         /\ Reverse(Reverse(seq)) = seq
BY DEF Reverse

THEOREM ReverseEmpty == Reverse(<< >>) = << >>
BY DEF Reverse

THEOREM ReverseEqual ==
  ASSUME NEW S, NEW s \in Seq(S), NEW t \in Seq(S), Reverse(s) = Reverse(t)
  PROVE  s = t
<1>1. Len(s) = Len(t)  BY DEF Reverse
<1>2. ASSUME NEW i \in 1 .. Len(s)
      PROVE  s[i] = t[i]
  <2>1. Reverse(s)[Len(s)-i+1] = Reverse(t)[Len(s)-i+1]  OBVIOUS
  <2>. QED  BY <2>1 DEF Reverse
<1>. QED  BY <1>1, <1>2, SeqEqual

THEOREM ReverseEmptyIffEmpty ==
  ASSUME NEW S, NEW seq \in Seq(S), Reverse(seq) = <<>>
  PROVE  seq = <<>>
BY DEF Reverse

THEOREM ReverseConcat == 
  ASSUME NEW S, NEW s1 \in Seq(S), NEW s2 \in Seq(S)
  PROVE  Reverse(s1 \o s2) = Reverse(s2) \o Reverse(s1)
BY Z3 DEF Reverse

THEOREM ReverseAppend ==
  ASSUME NEW S, NEW seq \in Seq(S), NEW e \in S
  PROVE  Reverse(Append(seq,e)) = Cons(e, Reverse(seq))
BY DEF Reverse, Cons

THEOREM ReverseCons ==
  ASSUME NEW S, NEW seq \in Seq(S), NEW e \in S
  PROVE  Reverse(Cons(e,seq)) = Append(Reverse(seq), e)
BY DEF Reverse, Cons

THEOREM ReverseSingleton == \A x : Reverse(<< x >>) = << x >>
BY DEF Reverse

THEOREM ReverseSubSeq ==
  ASSUME NEW S, NEW seq \in Seq(S),
         NEW m \in 1..Len(seq), NEW n \in 1..Len(seq)
  PROVE  Reverse(SubSeq(seq, m , n)) = SubSeq(Reverse(seq), Len(seq)-n+1, Len(seq)-m+1)
BY DEF Reverse

THEOREM ReversePalindrome ==
  ASSUME NEW S, NEW seq \in Seq(S),
         Reverse(seq) = seq
  PROVE  Reverse(seq \o seq) = seq \o seq
BY ReverseConcat

THEOREM LastEqualsHeadReverse ==
  ASSUME NEW S, NEW seq \in Seq(S), seq # << >>
  PROVE  Last(seq) = Head(Reverse(seq))
BY DEF Last, Reverse

THEOREM ReverseFrontEqualsTailReverse ==
  ASSUME NEW S, NEW seq \in Seq(S), seq # << >>
  PROVE  Reverse(Front(seq)) = Tail(Reverse(seq))
BY Z3 DEF Reverse, Front

(* The range of the reverse sequence equals that of the original one. *)
THEOREM RangeReverse == 
  ASSUME NEW S, NEW seq \in Seq(S)
  PROVE Range(Reverse(seq)) = Range(seq)
BY Z3 DEF Range, Reverse

(***************************************************************************)
(* Theorems about prefixes and suffixes of sequences.                      *)
(* IsPrefix(s,t) == \E u \in Seq(Range(t)) : t = s \o u                    *)
(* IsStrictPrefix(s,t) == IsPrefix(s,t) /\ s # t                           *)
(* IsSuffix(s,t) == \E u \in Seq(Range(t)) : t = u \o s                    *)
(* IsStrictSuffix(s,t) == IsSuffix(s,t) /\ s # t                           *)
(***************************************************************************)

(***************************************************************************)
(* The following theorem gives three alternative characterizations of      *)
(* prefixes. It also implies that any prefix of a sequence t is at most    *)
(* as long as t.                                                           *)
(***************************************************************************)
THEOREM IsPrefixProperties ==
  ASSUME NEW S, NEW s \in Seq(S), NEW t \in Seq(S)
  PROVE  /\ IsPrefix(s,t) <=> \E u \in Seq(S) : t = s \o u
         /\ IsPrefix(s,t) <=> Len(s) <= Len(t) /\ s = SubSeq(t, 1, Len(s))
         /\ IsPrefix(s,t) <=> Len(s) <= Len(t) /\ s = Restrict(t, DOMAIN s)
<1>1. IsPrefix(s,t) <=> \E u \in Seq(S) : t = s \o u
  <2>1. ASSUME NEW u \in Seq(Range(t)), t = s \o u
        PROVE  u \in Seq(S)
    BY DEF Range
  <2>2. ASSUME NEW u \in Seq(S), t = s \o u
        PROVE  u \in Seq(Range(t))
    BY <2>2, RangeConcatenation, SeqOfRange
  <2>. QED  BY <2>1, <2>2 DEF IsPrefix
<1>2. IsPrefix(s,t) <=> Len(s) <= Len(t) /\ s = SubSeq(t, 1, Len(s))
  <2>1. ASSUME IsPrefix(s,t) 
        PROVE Len(s) <= Len(t) /\ s = SubSeq(t, 1, Len(s))
    BY <2>1 DEF IsPrefix
  <2>2. ASSUME Len(s) <= Len(t), s = SubSeq(t, 1, Len(s))
        PROVE IsPrefix(s,t)
    <3>1. t = s \o SubSeq(t, Len(s)+1, Len(t))
      BY <2>2
    <3>2. SubSeq(t, Len(s)+1, Len(t)) \in Seq(S)  OBVIOUS
    <3>. QED  BY <3>1, <3>2, <1>1, Zenon
  <2>. QED  BY <2>1, <2>2
<1>3. IsPrefix(s,t) <=> Len(s) <= Len(t) /\ s = Restrict(t, DOMAIN s)
  BY <1>2 DEF Restrict
<1>. QED  BY <1>1, <1>2, <1>3

THEOREM IsStrictPrefixProperties ==
  ASSUME NEW S, NEW s \in Seq(S), NEW t \in Seq(S)
  PROVE  /\ IsStrictPrefix(s,t) <=> \E u \in Seq(S) : u # << >> /\ t = s \o u
         /\ IsStrictPrefix(s,t) <=> Len(s) < Len(t) /\ s = SubSeq(t, 1, Len(s))
         /\ IsStrictPrefix(s,t) <=> Len(s) < Len(t) /\ s = Restrict(t, DOMAIN s)
         /\ IsStrictPrefix(s,t) <=> IsPrefix(s,t) /\ Len(s) < Len(t)
<1>1. IsStrictPrefix(s,t) => Len(s) < Len(t)
  BY DEF IsStrictPrefix, IsPrefix
<1>2. IsStrictPrefix(s,t) <=> \E u \in Seq(S) : u # << >> /\ t = s \o u
  <2>1. ASSUME IsStrictPrefix(s,t)
        PROVE  \E u \in Seq(S) : u # << >> /\ t = s \o u
    <3>1. PICK u \in Seq(S) : t = s \o u
      BY <2>1, IsPrefixProperties DEF IsStrictPrefix
    <3>2. u # << >>
      BY <2>1, <3>1 DEF IsStrictPrefix
    <3>. QED  BY <3>1, <3>2
  <2>2. ASSUME NEW u \in Seq(S), u # << >>, t = s \o u
        PROVE  IsStrictPrefix(s,t)
    <3>1. IsPrefix(s,t)
      BY <2>2, IsPrefixProperties, Zenon
    <3>2. s # t
      BY <2>2
    <3>.  QED  BY <3>1, <3>2 DEF IsStrictPrefix
  <2>. QED  BY <2>1, <2>2, Zenon
<1>. QED  BY <1>1, <1>2, IsPrefixProperties DEF IsStrictPrefix

THEOREM IsPrefixElts ==
  ASSUME NEW S, NEW s \in Seq(S), NEW t \in Seq(S), NEW i \in 1 .. Len(s),
         IsPrefix(s,t)
  PROVE  s[i] = t[i]
BY IsPrefixProperties

THEOREM EmptyIsPrefix ==
  ASSUME NEW S, NEW s \in Seq(S)
  PROVE  /\ IsPrefix(<<>>, s)
         /\ IsPrefix(s, <<>>) <=> s = <<>>
         /\ IsStrictPrefix(<<>>, s) <=> s # <<>>
         /\ ~ IsStrictPrefix(s, <<>>)
BY IsPrefixProperties, IsStrictPrefixProperties

THEOREM IsPrefixConcat ==
  ASSUME NEW S, NEW s \in Seq(S), NEW t \in Seq(S)
  PROVE  IsPrefix(s, s \o t)
BY IsPrefixProperties, ConcatProperties, Zenon

THEOREM IsStrictPrefixAppend ==
  ASSUME NEW S, NEW s \in Seq(S), NEW e \in S
  PROVE  IsStrictPrefix(s, Append(s,e))
<1>1. /\ Append(s,e) = s \o <<e>>
      /\ Append(s,e) \in Seq(S)
      /\ <<e>> \in Seq(S)
      /\ <<e>> # << >>
  OBVIOUS
<1>. QED  BY <1>1, IsStrictPrefixProperties, Zenon

THEOREM FrontIsPrefix ==
  ASSUME NEW S, NEW s \in Seq(S)
  PROVE  /\ IsPrefix(Front(s), s)
         /\ s # <<>> => IsStrictPrefix(Front(s), s)
<1>1. /\ Front(s) \in Seq(S)
      /\ Len(Front(s)) <= Len(s)
      /\ Front(s) = SubSeq(s, 1, Len(Front(s)))
      /\ s # << >> => Len(Front(s)) < Len(s)
  BY DEF Front
<1>. QED  BY <1>1, IsPrefixProperties, IsStrictPrefixProperties

(***************************************************************************)
(* (Strict) prefixes on sequences form a (strict) partial order, and       *)
(* the strict ordering is well-founded.                                    *)
(***************************************************************************)
THEOREM IsPrefixPartialOrder ==
  ASSUME NEW S
  PROVE  /\ \A s \in Seq(S) : IsPrefix(s,s)
         /\ \A s,t \in Seq(S) : IsPrefix(s,t) /\ IsPrefix(t,s) => s = t
         /\ \A s,t,u \in Seq(S) : IsPrefix(s,t) /\ IsPrefix(t,u) => IsPrefix(s,u)
BY IsPrefixProperties, Z3

THEOREM ConcatIsPrefix ==
  ASSUME NEW S, NEW s \in Seq(S), NEW t \in Seq(S), NEW u \in Seq(S),
         IsPrefix(s \o t, u)
  PROVE  IsPrefix(s, u)
<1>1. /\ s \o t \in Seq(S)
      /\ IsPrefix(s, s \o t)
  BY IsPrefixConcat
<1>. QED  BY <1>1, IsPrefixPartialOrder, Zenon

THEOREM ConcatIsPrefixCancel ==
  ASSUME NEW S, NEW s \in Seq(S), NEW t \in Seq(S), NEW u \in Seq(S)
  PROVE  /\ IsPrefix(s \o t, s \o u) <=> IsPrefix(t, u)
<1>1. ASSUME IsPrefix(t,u) PROVE IsPrefix(s \o t, s \o u)
  <2>1. PICK v \in Seq(S) : u = t \o v  BY <1>1, IsPrefixProperties, Zenon
  <2>2. s \o u = (s \o t) \o v  BY <2>1, Z3
  <2>. QED  BY <2>2, IsPrefixProperties, Z3
<1>2. ASSUME IsPrefix(s \o t, s \o u) PROVE IsPrefix(t,u)
  <2>1. PICK v \in Seq(S) : s \o u = (s \o t) \o v
    BY <1>2, s \o t \in Seq(S), s \o u \in Seq(S), IsPrefixProperties, Isa
  <2>2. s \o u = s \o (t \o v)
    BY <2>1, Z3
  <2>3. u = t \o v
    BY t \o v \in Seq(S), <2>2, ConcatSimplifications, IsaM("blast")
  <2>. QED  BY <2>3, IsPrefixProperties, Zenon
<1>. QED  BY <1>1, <1>2

THEOREM ConsIsPrefixCancel ==
  ASSUME NEW S, NEW e \in S, NEW s \in Seq(S), NEW t \in Seq(S)
  PROVE  IsPrefix(Cons(e,s), Cons(e,t)) <=> IsPrefix(s,t)
BY <<e>> \in Seq(S), ConcatIsPrefixCancel, Zenon DEF Cons

THEOREM ConsIsPrefix ==
  ASSUME NEW S, NEW e \in S, NEW s \in Seq(S), NEW u \in Seq(S),
         IsPrefix(Cons(e,s), u)
  PROVE  /\ e = Head(u)
         /\ IsPrefix(s, Tail(u))
<1>. <<e>> \in Seq(S)
  OBVIOUS
<1>1. IsPrefix(<<e>>, u)
  BY ConcatIsPrefix, Zenon DEF Cons
<1>2. PICK v \in Seq(S) : u = Cons(e, v)
  BY <1>1, IsPrefixProperties, Isa DEF Cons
<1>3. /\ e = Head(u)
      /\ v = Tail(u)
      /\ IsPrefix(Cons(e,s), Cons(e, Tail(u)))
  BY <1>2, ConsProperties, Isa
<1>. QED
  BY <1>3, ConsIsPrefixCancel, Zenon

THEOREM IsStrictPrefixStrictPartialOrder ==
  ASSUME NEW S
  PROVE  /\ \A s \in Seq(S) : ~ IsStrictPrefix(s,s)
         /\ \A s,t \in Seq(S) : IsStrictPrefix(s,t) => ~ IsStrictPrefix(t,s)
         /\ \A s,t,u \in Seq(S) : IsStrictPrefix(s,t) /\ IsStrictPrefix(t,u) => IsStrictPrefix(s,u)
BY IsStrictPrefixProperties, Z3

THEOREM IsStrictPrefixWellFounded ==
  ASSUME NEW S
  PROVE  IsWellFoundedOn(OpToRel(IsStrictPrefix, Seq(S)), Seq(S))
<1>1. IsWellFoundedOn(PreImage(Len, Seq(S), OpToRel(<, Nat)), Seq(S))
  BY NatLessThanWellFounded, PreImageWellFounded, IsaM("blast")
<1>2. OpToRel(IsStrictPrefix, Seq(S)) \subseteq PreImage(Len, Seq(S), OpToRel(<, Nat))
  BY IsStrictPrefixProperties DEF PreImage, OpToRel
<1>. QED
  BY <1>1, <1>2, IsWellFoundedOnSubrelation, Zenon

THEOREM SeqStrictPrefixInduction ==
  ASSUME NEW P(_), NEW S,
         \A t \in Seq(S) : (\A s \in Seq(S) : IsStrictPrefix(s,t) => P(s)) => P(t)
  PROVE  \A s \in Seq(S) : P(s)
<1>1. \A t \in Seq(S) : 
         (\A s \in SetLessThan(t, OpToRel(IsStrictPrefix, Seq(S)), Seq(S)) : P(s))
         => P(t)
  BY Zenon DEF SetLessThan, OpToRel
<1>. QED  BY WFInduction, IsStrictPrefixWellFounded, <1>1, IsaM("blast")

(***************************************************************************)
(* Similar theorems about suffixes.                                        *)
(***************************************************************************)

THEOREM IsSuffixProperties ==
  ASSUME NEW S, NEW s \in Seq(S), NEW t \in Seq(S)
  PROVE  /\ IsSuffix(s,t) <=> \E u \in Seq(S) : t = u \o s
         /\ IsSuffix(s,t) <=> Len(s) <= Len(t) /\ s = SubSeq(t, Len(t)-Len(s)+1, Len(t))
         /\ IsSuffix(s,t) <=> IsPrefix(Reverse(s), Reverse(t))
<1>1. IsSuffix(s,t) <=> \E u \in Seq(S) : t = u \o s
  <2>1. ASSUME NEW u \in Seq(Range(t)), t = u \o s
        PROVE  u \in Seq(S)
    BY DEF Range
  <2>2. ASSUME NEW u \in Seq(S), t = u \o s
        PROVE  u \in Seq(Range(t))
    BY <2>2, RangeConcatenation, SeqOfRange
  <2>. QED  BY <2>1, <2>2 DEF IsSuffix
<1>2. IsSuffix(s,t) <=> Len(s) <= Len(t) /\ s = SubSeq(t, Len(t)-Len(s)+1, Len(t))
  <2>1. ASSUME IsSuffix(s,t)
        PROVE  Len(s) <= Len(t) /\ s = SubSeq(t, Len(t)-Len(s)+1, Len(t))
    BY <2>1 DEF IsSuffix
  <2>2. ASSUME Len(s) <= Len(t), s = SubSeq(t, Len(t)-Len(s)+1, Len(t))
        PROVE  IsSuffix(s,t)
    <3>2. t = SubSeq(t, 1, Len(t) - Len(s)) \o s
      BY <2>2, Z3
    <3>3. SubSeq(t, 1, Len(t) - Len(s)) \in Seq(S)  OBVIOUS
    <3>. QED  BY <3>2, <3>3, <1>1, Zenon
  <2>. QED  BY <2>1, <2>2
<1>3. IsSuffix(s,t) <=> IsPrefix(Reverse(s), Reverse(t))
  <2>. /\ Reverse(s) \in Seq(S)
       /\ Reverse(t) \in Seq(S)
    BY ReverseProperties
  <2>1. ASSUME IsSuffix(s,t)
        PROVE  IsPrefix(Reverse(s), Reverse(t))
    <3>1. PICK u \in Seq(S) : t = u \o s
      BY <2>1, <1>1
    <3>2. /\ Reverse(u) \in Seq(S)
          /\ Reverse(t) = Reverse(s) \o Reverse(u)
      BY <3>1, ReverseProperties, ReverseConcat, Zenon
    <3>. QED  BY <3>2, IsPrefixProperties, Zenon
  <2>2. ASSUME IsPrefix(Reverse(s), Reverse(t))
        PROVE  IsSuffix(s,t)
    <3>1. PICK u \in Seq(S) : Reverse(t) = Reverse(s) \o u
      BY <2>2, IsPrefixProperties
    <3>2. /\ Reverse(u) \in Seq(S)
          /\ Reverse(Reverse(t)) = Reverse(u) \o Reverse(Reverse(s))
      BY <3>1, ReverseProperties, ReverseConcat, Zenon
    <3>. QED  BY <3>2, <1>1, ReverseProperties, Zenon
  <2>. QED  BY <2>1, <2>2
<1>. QED  BY <1>1, <1>2, <1>3

THEOREM IsStrictSuffixProperties ==
  ASSUME NEW S, NEW s \in Seq(S), NEW t \in Seq(S)
  PROVE  /\ IsStrictSuffix(s,t) <=> \E u \in Seq(S) : u # << >> /\ t = u \o s
         /\ IsStrictSuffix(s,t) <=> Len(s) < Len(t) /\ IsSuffix(s,t)
         /\ IsStrictSuffix(s,t) <=> Len(s) < Len(t) /\ s = SubSeq(t, Len(t)-Len(s)+1, Len(t))
         /\ IsStrictSuffix(s,t) <=> IsStrictPrefix(Reverse(s), Reverse(t))
<1>1. IsStrictSuffix(s,t) => Len(s) < Len(t)
  BY Z3 DEF IsStrictSuffix, IsSuffix
<1>2. IsStrictSuffix(s,t) <=> \E u \in Seq(S) : u # << >> /\ t = u \o s
  <2>1. ASSUME IsStrictSuffix(s,t)
        PROVE  \E u \in Seq(S) : u # << >> /\ t = u \o s
    <3>1. PICK u \in Seq(S) : t = u \o s
      BY <2>1, IsSuffixProperties DEF IsStrictSuffix
    <3>2. u # << >>
      BY <2>1, <3>1 DEF IsStrictSuffix
    <3>. QED  BY <3>1, <3>2
  <2>2. ASSUME NEW u \in Seq(S), u # << >> /\ t = u \o s
        PROVE  IsStrictSuffix(s,t)
    <3>1. IsSuffix(s,t)
      BY <2>2, IsSuffixProperties, Zenon
    <3>2. s # t
      BY <2>2
    <3>. QED  BY <3>1, <3>2 DEF IsStrictSuffix
  <2>. QED  BY <2>1, <2>2
<1>. QED  BY <1>1, <1>2, IsSuffixProperties DEF IsStrictPrefix, IsStrictSuffix

THEOREM IsSuffixElts ==
  ASSUME NEW S, NEW s \in Seq(S), NEW t \in Seq(S), NEW i \in 1 .. Len(s),
         IsSuffix(s,t)
  PROVE  s[i] = t[Len(t) - Len(s) + i]
BY IsSuffixProperties, Z3

THEOREM EmptyIsSuffix ==
  ASSUME NEW S, NEW s \in Seq(S)
  PROVE  /\ IsSuffix(<<>>, s)
         /\ IsSuffix(s, <<>>) <=> s = <<>>
         /\ IsStrictSuffix(<<>>, s) <=> s # <<>>
         /\ ~ IsStrictSuffix(s, <<>>)
BY IsSuffixProperties, IsStrictSuffixProperties

THEOREM IsSuffixConcat ==
  ASSUME NEW S, NEW s \in Seq(S), NEW t \in Seq(S)
  PROVE  IsSuffix(s, t \o s)
BY IsSuffixProperties, ConcatProperties, Zenon

THEOREM IsStrictSuffixCons ==
  ASSUME NEW S, NEW s \in Seq(S), NEW e \in S
  PROVE  IsStrictSuffix(s, Cons(e,s))
BY IsStrictSuffixProperties, Z3 DEF Cons

THEOREM TailIsSuffix ==
  ASSUME NEW S, NEW s \in Seq(S)
  PROVE  /\ IsSuffix(Tail(s), s)
         /\ s # <<>> => IsStrictSuffix(Tail(s), s)
<1>1. /\ Tail(s) \in Seq(S)
      /\ Len(Tail(s)) <= Len(s)
      /\ Tail(s) = SubSeq(s, 2, Len(Tail(s)))
      /\ s # << >> => Len(Tail(s)) < Len(s)
  OBVIOUS
<1>. QED  BY <1>1, IsSuffixProperties, IsStrictSuffixProperties

THEOREM IsSuffixPartialOrder ==
  ASSUME NEW S
  PROVE  /\ \A s \in Seq(S) : IsSuffix(s,s)
         /\ \A s,t \in Seq(S) : IsSuffix(s,t) /\ IsSuffix(t,s) => s = t
         /\ \A s,t,u \in Seq(S) : IsSuffix(s,t) /\ IsSuffix(t,u) => IsSuffix(s,u)
<1>1. ASSUME NEW s \in Seq(S) PROVE IsSuffix(s,s)
  BY IsSuffixProperties
<1>2. ASSUME NEW s \in Seq(S), NEW t \in Seq(S), IsSuffix(s,t), IsSuffix(t,s)
      PROVE  s = t
  <2>1. PICK v \in Seq(S) : t = v \o s
    BY <1>2, IsSuffixProperties
  <2>2. PICK w \in Seq(S) : s = w \o t
    BY <1>2, IsSuffixProperties
  <2>. QED  BY <2>1, <2>2, Z3
<1>3. ASSUME NEW s \in Seq(S), NEW t \in Seq(S), NEW u \in Seq(S),
             IsSuffix(s,t), IsSuffix(t,u)
      PROVE  IsSuffix(s,u)
  <2>1. PICK v \in Seq(S) : t = v \o s
    BY <1>3, IsSuffixProperties, Zenon
  <2>2. PICK w \in Seq(S) : u = w \o t
    BY <1>3, IsSuffixProperties, Zenon
  <2>3. /\ w \o v \in Seq(S)
        /\ u = (w \o v) \o s
    BY <2>1, <2>2, Z3
  <2>. QED  BY <2>3, IsSuffixProperties, Zenon
<1>. QED  BY <1>1, <1>2, <1>3

THEOREM ConcatIsSuffix ==
  ASSUME NEW S, NEW s \in Seq(S), NEW t \in Seq(S), NEW u \in Seq(S),
         IsSuffix(s \o t, u)
  PROVE  IsSuffix(t, u)
<1>1. /\ s \o t \in Seq(S)
      /\ IsSuffix(t, s \o t)
  BY IsSuffixConcat
<1>. QED  BY <1>1, IsSuffixPartialOrder, Zenon

THEOREM ConcatIsSuffixCancel ==
  ASSUME NEW S, NEW s \in Seq(S), NEW t \in Seq(S), NEW u \in Seq(S)
  PROVE  IsSuffix(s \o t, u \o t) <=> IsSuffix(s, u)
<1>1. ASSUME IsSuffix(s, u) PROVE IsSuffix(s \o t, u \o t)
  <2>1. PICK v \in Seq(S) : u = v \o s  BY <1>1, IsSuffixProperties
  <2>2. u \o t = v \o (s \o t)  BY <2>1, Z3
  <2>. QED  BY s \o t \in Seq(S), u \o t \in Seq(S), <2>2, IsSuffixProperties, IsaM("blast")
<1>2. ASSUME IsSuffix(s \o t, u \o t) PROVE IsSuffix(s, u)
  <2>1. PICK v \in Seq(S) : u \o t = v \o (s \o t)
    BY <1>2, s \o t \in Seq(S), u \o t \in Seq(S), IsSuffixProperties, Isa
  <2>2. u \o t = (v \o s) \o t
    BY <2>1, Z3
  <2>3. u = v \o s
    \* BY v \o s \in Seq(S), <2>2, ConcatSimplifications
    \* why do we need this kludge of a proof ???
    <3>. DEFINE w == v \o s
    <3>1. /\ w \in Seq(S)
          /\ u \o t = w \o t
      BY <2>2
    <3>. HIDE DEF w
    <3>2. u = w
      BY <3>1, ConcatSimplifications, Z3
    <3>. QED  BY <3>2 DEF w
  <2>. QED  BY <2>3, IsSuffixProperties, Zenon
<1>. QED  BY <1>1, <1>2

THEOREM AppendIsSuffixCancel ==
  ASSUME NEW S, NEW e \in S, NEW s \in Seq(S), NEW t \in Seq(S)
  PROVE  IsSuffix(Append(s,e), Append(t,e)) <=> IsSuffix(s,t)
BY <<e>> \in Seq(S), ConcatIsSuffixCancel, AppendIsConcat, Isa

THEOREM AppendIsSuffix ==
  ASSUME NEW S, NEW e \in S, NEW s \in Seq(S), NEW u \in Seq(S),
         IsSuffix(Append(s,e), u)
  PROVE  /\ e = Last(u)
         /\ IsSuffix(s, Front(u))
<1>. <<e>> \in Seq(S)
  OBVIOUS
<1>1. IsSuffix(<<e>>, u)
  BY ConcatIsSuffix, AppendIsConcat, Isa
<1>2. PICK v \in Seq(S) : u = Append(v,e)
  BY <1>1, IsSuffixProperties, AppendIsConcat, Isa
<1>3. /\ e = Last(u)
      /\ v = Front(u)
      /\ IsSuffix(Append(s,e), Append(Front(u),e))
  BY <1>2, FrontLastAppend
<1>. QED
  BY <1>3, AppendIsSuffixCancel, Zenon

THEOREM IsStrictSuffixStrictPartialOrder ==
  ASSUME NEW S
  PROVE  /\ \A s \in Seq(S) : ~ IsStrictSuffix(s,s)
         /\ \A s,t \in Seq(S) : IsStrictSuffix(s,t) => ~ IsStrictSuffix(t,s)
         /\ \A s,t,u \in Seq(S) : IsStrictSuffix(s,t) /\ IsStrictSuffix(t,u) => IsStrictSuffix(s,u)
BY IsStrictSuffixProperties, IsSuffixPartialOrder, Z3

THEOREM IsStrictSuffixWellFounded ==
  ASSUME NEW S
  PROVE  IsWellFoundedOn(OpToRel(IsStrictSuffix, Seq(S)), Seq(S))
<1>1. IsWellFoundedOn(PreImage(Len, Seq(S), OpToRel(<, Nat)), Seq(S))
  BY NatLessThanWellFounded, PreImageWellFounded, IsaM("blast")
<1>2. OpToRel(IsStrictSuffix, Seq(S)) \subseteq PreImage(Len, Seq(S), OpToRel(<, Nat))
  BY IsStrictSuffixProperties DEF PreImage, OpToRel
<1>. QED
  BY <1>1, <1>2, IsWellFoundedOnSubrelation, Zenon

THEOREM SeqStrictSuffixInduction ==
  ASSUME NEW P(_), NEW S,
         \A t \in Seq(S) : (\A s \in Seq(S) : IsStrictSuffix(s,t) => P(s)) => P(t)
  PROVE  \A s \in Seq(S) : P(s)
<1>1. \A t \in Seq(S) : 
         (\A s \in SetLessThan(t, OpToRel(IsStrictSuffix, Seq(S)), Seq(S)) : P(s))
         => P(t)
  BY Zenon DEF SetLessThan, OpToRel
<1>. QED  BY WFInduction, IsStrictSuffixWellFounded, <1>1, IsaM("blast")

(***************************************************************************)
(* Since the (strict) prefix and suffix orderings on sequences are         *)
(* well-founded, they can be used for defining recursive functions.        *)
(* The operators OpDefinesFcn, WFInductiveDefines, and WFInductiveUnique   *)
(* are defined in module WellFoundedInduction.                             *)
(***************************************************************************)

StrictPrefixesDetermineDef(S, Def(_,_)) ==
   \A g,h : \A seq \in Seq(S) :
      (\A pre \in Seq(S) : IsStrictPrefix(pre,seq) => g[pre] = h[pre])
      => Def(g, seq) = Def(h, seq)

LEMMA StrictPrefixesDetermineDef_WFDefOn ==
  ASSUME NEW S, NEW Def(_,_), StrictPrefixesDetermineDef(S, Def)
  PROVE  WFDefOn(OpToRel(IsStrictPrefix, Seq(S)), Seq(S), Def)
BY Isa DEF StrictPrefixesDetermineDef, WFDefOn, OpToRel, SetLessThan

THEOREM PrefixRecursiveSequenceFunctionUnique ==
  ASSUME NEW S, NEW Def(_,_), StrictPrefixesDetermineDef(S, Def)
  PROVE  WFInductiveUnique(Seq(S), Def)
BY StrictPrefixesDetermineDef_WFDefOn, IsStrictPrefixWellFounded, WFDefOnUnique

THEOREM PrefixRecursiveSequenceFunctionDef ==
  ASSUME NEW S, NEW Def(_,_), NEW f,
         StrictPrefixesDetermineDef(S, Def),
         OpDefinesFcn(f, Seq(S), Def)
  PROVE  WFInductiveDefines(f, Seq(S), Def)
BY StrictPrefixesDetermineDef_WFDefOn, IsStrictPrefixWellFounded, WFInductiveDef

THEOREM PrefixRecursiveSequenceFunctionType ==
  ASSUME NEW S, NEW T, NEW Def(_,_), NEW f,
         T # {},
         StrictPrefixesDetermineDef(S, Def),
         WFInductiveDefines(f, Seq(S), Def),
         \A g \in [Seq(S) -> T], s \in Seq(S) : Def(g,s) \in T
  PROVE  f \in [Seq(S) -> T]
<1>1. IsWellFoundedOn(OpToRel(IsStrictPrefix, Seq(S)), Seq(S))
  BY IsStrictPrefixWellFounded, Zenon
<1>2. WFDefOn(OpToRel(IsStrictPrefix, Seq(S)), Seq(S), Def)
  BY StrictPrefixesDetermineDef_WFDefOn, Zenon
<1>. QED
  BY <1>1, <1>2, WFInductiveDefType, Isa

StrictSuffixesDetermineDef(S, Def(_,_)) ==
   \A g,h : \A seq \in Seq(S) :
      (\A suf \in Seq(S) : IsStrictSuffix(suf,seq) => g[suf] = h[suf])
      => Def(g, seq) = Def(h, seq)

LEMMA StrictSuffixesDetermineDef_WFDefOn ==
  ASSUME NEW S, NEW Def(_,_), StrictSuffixesDetermineDef(S, Def)
  PROVE  WFDefOn(OpToRel(IsStrictSuffix, Seq(S)), Seq(S), Def)
BY Isa DEF StrictSuffixesDetermineDef, WFDefOn, OpToRel, SetLessThan

THEOREM SuffixRecursiveSequenceFunctionUnique ==
  ASSUME NEW S, NEW Def(_,_), StrictSuffixesDetermineDef(S, Def)
  PROVE  WFInductiveUnique(Seq(S), Def)
BY StrictSuffixesDetermineDef_WFDefOn, IsStrictSuffixWellFounded, WFDefOnUnique

THEOREM SuffixRecursiveSequenceFunctionDef ==
  ASSUME NEW S, NEW Def(_,_), NEW f,
         StrictSuffixesDetermineDef(S, Def),
         OpDefinesFcn(f, Seq(S), Def)
  PROVE  WFInductiveDefines(f, Seq(S), Def)
BY StrictSuffixesDetermineDef_WFDefOn, IsStrictSuffixWellFounded, WFInductiveDef

THEOREM SuffixRecursiveSequenceFunctionType ==
  ASSUME NEW S, NEW T, NEW Def(_,_), NEW f,
         T # {},
         StrictSuffixesDetermineDef(S, Def),
         WFInductiveDefines(f, Seq(S), Def),
         \A g \in [Seq(S) -> T], s \in Seq(S) : Def(g,s) \in T
  PROVE  f \in [Seq(S) -> T]
<1>1. IsWellFoundedOn(OpToRel(IsStrictSuffix, Seq(S)), Seq(S))
  BY IsStrictSuffixWellFounded, Zenon
<1>2. WFDefOn(OpToRel(IsStrictSuffix, Seq(S)), Seq(S), Def)
  BY StrictSuffixesDetermineDef_WFDefOn, Zenon
<1>. QED
  BY <1>1, <1>2, WFInductiveDefType, Isa

(***************************************************************************)
(* The following theorems justify ``primitive recursive'' functions over   *)
(* sequences, with a base case for the empty sequence and recursion along  *)
(* either the Tail or the Front of a non-empty sequence.                   *)
(***************************************************************************)

TailInductiveDefHypothesis(f, S, f0, Def(_,_)) ==
  f = CHOOSE g : g = [s \in Seq(S) |-> IF s = <<>> THEN f0 ELSE Def(g[Tail(s)], s)]

TailInductiveDefConclusion(f, S, f0, Def(_,_)) ==
  f = [s \in Seq(S) |-> IF s = <<>> THEN f0 ELSE Def(f[Tail(s)], s)]

THEOREM TailInductiveDef ==
  ASSUME NEW S, NEW Def(_,_), NEW f, NEW f0,
         TailInductiveDefHypothesis(f, S, f0, Def)
  PROVE  TailInductiveDefConclusion(f, S, f0, Def)
<1>. DEFINE Op(h,s) == IF s = <<>> THEN f0 ELSE Def(h[Tail(s)], s)
<1>1. StrictSuffixesDetermineDef(S, Op)
  <2>. SUFFICES ASSUME NEW g, NEW h, NEW seq \in Seq(S),
                       \A suf \in Seq(S) : IsStrictSuffix(suf, seq) => g[suf] = h[suf]
                PROVE  Op(g, seq) = Op(h, seq)
    BY Zenon DEF StrictSuffixesDetermineDef
  <2>1. CASE seq = <<>>
    BY <2>1
  <2>2. CASE seq # <<>>
    BY <2>2, TailIsSuffix, Z3
  <2>. QED  BY <2>1, <2>2, Zenon
<1>2. OpDefinesFcn(f, Seq(S), Op)
  BY DEF OpDefinesFcn, TailInductiveDefHypothesis
<1>3. WFInductiveDefines(f, Seq(S), Op)
  BY <1>1, <1>2, SuffixRecursiveSequenceFunctionDef, Zenon
<1>. QED  BY <1>3, Zenon DEF WFInductiveDefines, TailInductiveDefConclusion

THEOREM TailInductiveDefType ==
  ASSUME NEW S, NEW Def(_,_), NEW f, NEW f0, NEW T,
         TailInductiveDefConclusion(f, S, f0, Def),
         f0 \in T,
         \A v \in T, s \in Seq(S) : s # <<>> => Def(v,s) \in T
  PROVE  f \in [Seq(S) -> T]
<1>. SUFFICES \A s \in Seq(S) : f[s] \in T
  BY DEF TailInductiveDefConclusion
<1>1. f[<<>>] \in T
  BY <<>> \in Seq(S), Zenon DEF TailInductiveDefConclusion
<1>2. ASSUME NEW seq \in Seq(S), NEW e \in S, f[seq] \in T
      PROVE  f[Cons(e, seq)] \in T
  <2>1. /\ Cons(e, seq) \in Seq(S)
        /\ Cons(e, seq) # <<>>
        /\ Tail(Cons(e, seq)) = seq
    BY ConsProperties, Zenon
  <2>2. f[Cons(e, seq)] = Def(f[seq], Cons(e,seq))
    BY <2>1, Zenon DEF TailInductiveDefConclusion
  <2>. QED  BY <1>2, <2>1, <2>2, Zenon
<1>. QED  BY <1>1, <1>2, SequencesInductionCons, Isa

FrontInductiveDefHypothesis(f, S, f0, Def(_,_)) ==
  f = CHOOSE g : g = [s \in Seq(S) |-> IF s = <<>> THEN f0 ELSE Def(g[Front(s)], s)]

FrontInductiveDefConclusion(f, S, f0, Def(_,_)) ==
  f = [s \in Seq(S) |-> IF s = <<>> THEN f0 ELSE Def(f[Front(s)], s)]

THEOREM FrontInductiveDef ==
  ASSUME NEW S, NEW Def(_,_), NEW f, NEW f0,
         FrontInductiveDefHypothesis(f, S, f0, Def)
  PROVE  FrontInductiveDefConclusion(f, S, f0, Def)
<1>. DEFINE Op(h,s) == IF s = <<>> THEN f0 ELSE Def(h[Front(s)], s)
<1>1. StrictPrefixesDetermineDef(S, Op)
  <2>. SUFFICES ASSUME NEW g, NEW h, NEW seq \in Seq(S),
                       \A pre \in Seq(S) : IsStrictPrefix(pre, seq) => g[pre] = h[pre]
                PROVE  Op(g, seq) = Op(h, seq)
    BY Zenon DEF StrictPrefixesDetermineDef, Zenon
  <2>1. CASE seq = <<>>
    BY <2>1
  <2>2. CASE seq # <<>>
    BY <2>2, FrontIsPrefix, FrontProperties, Z3
  <2>. QED  BY <2>1, <2>2, Zenon
<1>2. OpDefinesFcn(f, Seq(S), Op)
  BY DEF OpDefinesFcn, FrontInductiveDefHypothesis
<1>3. WFInductiveDefines(f, Seq(S), Op)
  BY <1>1, <1>2, PrefixRecursiveSequenceFunctionDef, Zenon
<1>. QED  BY <1>3, Zenon DEF WFInductiveDefines, FrontInductiveDefConclusion

THEOREM FrontInductiveDefType ==
  ASSUME NEW S, NEW Def(_,_), NEW f, NEW f0, NEW T,
         FrontInductiveDefConclusion(f, S, f0, Def),
         f0 \in T,
         \A v \in T, s \in Seq(S) : s # <<>> => Def(v,s) \in T
  PROVE  f \in [Seq(S) -> T]
<1>. SUFFICES \A s \in Seq(S) : f[s] \in T
  BY DEF FrontInductiveDefConclusion
<1>1. f[<<>>] \in T
  BY <<>> \in Seq(S), Zenon DEF FrontInductiveDefConclusion
<1>2. ASSUME NEW seq \in Seq(S), NEW e \in S, f[seq] \in T
      PROVE  f[Append(seq, e)] \in T
  <2>1. /\ Append(seq, e) \in Seq(S)
        /\ Append(seq, e) # <<>>
        /\ Front(Append(seq, e)) = seq
    BY AppendProperties, FrontLastAppend, Isa
  <2>2. f[Append(seq, e)] = Def(f[seq], Append(seq, e))
    BY <2>1, Zenon DEF FrontInductiveDefConclusion
  <2>. QED  BY <1>2, <2>1, <2>2, Zenon
<1>. QED  BY <1>1, <1>2, SequencesInductionAppend, Isa

============================================================================
