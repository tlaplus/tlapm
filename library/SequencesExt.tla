---------------------------- MODULE SequencesExt ----------------------------
(***************************************************************************)
(* This module is a copy taken from the Community Modules, with one        *)
(* operator commented out that depends on an operator defined in           *)
(* FiniteSetsExt.tla and for which we do not currently provide any         *)
(* lemma support.                                                          *)
(* It should be removed from the TLAPS library when the Community Modules  *)
(* have been fully integrated into the TLA+ Toolbox.                       *)
(***************************************************************************)

LOCAL INSTANCE Sequences
LOCAL INSTANCE Naturals
LOCAL INSTANCE FiniteSets
\* LOCAL INSTANCE FiniteSetsExt
LOCAL INSTANCE Functions
  (*************************************************************************)
  (* Imports the definitions from the modules, but doesn't export them.    *)
  (*************************************************************************)

-----------------------------------------------------------------------------

ToSet(s) ==
  (*************************************************************************)
  (* The image of the given sequence s. Cardinality(ToSet(s)) <= Len(s)    *)
  (* see https://en.wikipedia.org/wiki/Image_(mathematics)                 *)
  (* NB: This operator duplicates Functions!Range, which is preferred.     *)
  (*************************************************************************)
  { s[i] : i \in DOMAIN s }

SetToSeq(S) == 
  (**************************************************************************)
  (* Convert a set to some sequence that contains all the elements of the   *)
  (* set exactly once, and contains no other elements.                      *)
  (**************************************************************************)
  CHOOSE f \in [1..Cardinality(S) -> S] : IsInjective(f)

TupleOf(set, n) == 
  (***************************************************************************)
  (* TupleOf(s, 3) = s \X s \X s                                             *)
  (***************************************************************************)
  [1..n -> set]

SeqOf(set, n) == 
  (***************************************************************************)
  (* All sequences up to length n with all elements in set.  Includes empty  *)
  (* sequence.                                                               *)
  (***************************************************************************)
  UNION {[1..m -> set] : m \in 0..n}

BoundedSeq(S, n) ==
  (***************************************************************************)
  (* An alias for SeqOf to make the connection to Sequences!Seq, which is    *)
  (* the unbounded version of BoundedSeq.                                    *)
  (***************************************************************************)
  SeqOf(S, n)
  
-----------------------------------------------------------------------------

Contains(s, e) ==
  (**************************************************************************)
  (* TRUE iff the element e \in ToSet(s).                                   *)
  (**************************************************************************)
  \E i \in 1..Len(s) : s[i] = e

Reverse(s) ==
  (**************************************************************************)
  (* Reverse the given sequence s:  Let l be Len(s) (length of s).          *)
  (* Equals a sequence s.t. << S[l], S[l-1], ..., S[1]>>                    *)
  (**************************************************************************)
  [ i \in 1..Len(s) |-> s[(Len(s) - i) + 1] ]

Remove(s, e) ==
    (************************************************************************)
    (* The sequence s with e removed or s iff e \notin Range(s)             *)
    (************************************************************************)
    SelectSeq(s, LAMBDA t: t # e)

ReplaceAll(s, old, new) ==
  (*************************************************************************)
  (* Equals the sequence s except that all occurrences of element old are  *)
  (* replaced with the element new.                                        *)
  (*************************************************************************)
  LET F[i \in 0..Len(s)] == 
        IF i = 0 THEN << >>
                 ELSE IF s[i] = old THEN Append(F[i-1], new)
                                    ELSE Append(F[i-1], s[i])
  IN F[Len(s)]

-----------------------------------------------------------------------------

InsertAt(s, i, e) ==
  (**************************************************************************)
  (* Inserts element e at the position i moving the original element to i+1 *)
  (* and so on.  In other words, a sequence t s.t.:                         *)
  (*   /\ Len(t) = Len(s) + 1                                               *)
  (*   /\ t[i] = e                                                          *)
  (*   /\ \A j \in 1..(i - 1): t[j] = s[j]                                  *)
  (*   /\ \A k \in (i + 1)..Len(s): t[k + 1] = s[k]                         *)
  (**************************************************************************)
  SubSeq(s, 1, i-1) \o <<e>> \o SubSeq(s, i, Len(s))

ReplaceAt(s, i, e) ==
  (**************************************************************************)
  (* Replaces the element at position i with the element e.                 *)
  (**************************************************************************)
  [s EXCEPT ![i] = e]
  
RemoveAt(s, i) == 
  (**************************************************************************)
  (* Replaces the element at position i shortening the length of s by one.  *)
  (**************************************************************************)
  SubSeq(s, 1, i-1) \o SubSeq(s, i+1, Len(s))

-----------------------------------------------------------------------------

Cons(elt, seq) ==
  (*************************************************************************)
  (* The sequence formed by prepending elt to seq.                         *)
  (*************************************************************************) 
  <<elt>> \o seq

Front(s) == 
  (**************************************************************************)
  (* The sequence formed by removing its last element.                      *)
  (**************************************************************************)
  SubSeq(s, 1, Len(s)-1)

Last(s) ==
  (**************************************************************************)
  (* The last element of the sequence.                                      *)
  (**************************************************************************)
  s[Len(s)]

-----------------------------------------------------------------------------

IsPrefix(s, t) ==
  (**************************************************************************)
  (* TRUE iff the sequence s is a prefix of the sequence t, s.t.            *)
  (* \E u \in Seq(Range(t)) : t = s \o u. In other words, there exists      *)
  (* a suffix u that with s prepended equals t.                             *)
  (**************************************************************************)
  DOMAIN s \subseteq DOMAIN t /\ \A i \in DOMAIN s: s[i] = t[i]

IsStrictPrefix(s,t) ==
  (**************************************************************************)
  (* TRUE iff the sequence s is a prefix of the sequence t and s # t        *)
  (**************************************************************************)
  IsPrefix(s, t) /\ s # t

IsSuffix(s, t) ==
  (**************************************************************************)
  (* TRUE iff the sequence s is a suffix of the sequence t, s.t.            *)
  (* \E u \in Seq(Range(t)) : t = u \o s. In other words, there exists a    *)
  (* prefix that with s appended equals t.                                  *)
  (**************************************************************************)
  IsPrefix(Reverse(s), Reverse(t))

IsStrictSuffix(s, t) ==
  (**************************************************************************)
  (* TRUE iff the sequence s is a suffix of the sequence t and s # t        *)
  (**************************************************************************)
  IsSuffix(s,t) /\ s # t

-----------------------------------------------------------------------------

SeqMod(a, b) == 
  (***************************************************************************)
  (*   Range(a % b) = 0..b-1, but DOMAIN seq = 1..Len(seq).                  *)
  (*   So to do modular arithmetic on sequences we need to                   *)
  (*   map 0 to b.                                                           *)
  (***************************************************************************)
  IF a % b = 0 THEN b ELSE a % b

(*
ReduceSeq(op(_, _), seq, acc) == 
  (***************************************************************************)
  (* We can't just apply ReduceSet to the Range(seq) because the same        *)
  (* element might appear twice in the sequence.                             *)
  (***************************************************************************)
  ReduceSet(LAMBDA i, a: op(seq[i], a), DOMAIN seq, acc)
*)
=============================================================================
