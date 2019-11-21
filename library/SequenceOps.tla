---------------------------- MODULE SequenceOps ----------------------------
(**************************************************************************)
(* This module defines additional operators on sequences. An accompanying *)
(* module contains theorems about these operators.                        *)
(**************************************************************************)
EXTENDS Sequences, Integers, Functions

(***************************************************************************)
(* Cons prepends an element at the beginning of a sequence.                *)
(***************************************************************************)
Cons(elt, seq) == <<elt>> \o seq

(***************************************************************************)
(* InsertAt inserts an element at a given position of a sequence and       *)
(*          pushes the remaining elements of the sequence to the back.     *)
(* RemoveAt removes an element at a given position.                        *)
(***************************************************************************)
InsertAt(seq,i,elt) ==
  SubSeq(seq, 1, i-1) \o <<elt>> \o SubSeq(seq, i, Len(seq))

RemoveAt(seq, i) == SubSeq(seq, 1, i-1) \o SubSeq(seq, i+1, Len(seq))

(***************************************************************************)
(*            Front & Last                                                 *)
(*                                                                         *)
(*  Front(seq)   sequence formed by removing the last element              *)
(*  Last(seq)    last element of the sequence                              *)
(*                                                                         *)
(*  These operators are to Append what Head and Tail are to Cons.          *)
(***************************************************************************)

Front(seq) == SubSeq(seq, 1, Len(seq)-1)
Last(seq) == seq[Len(seq)]

Reverse(seq) == [j \in 1 .. Len(seq) |-> seq[Len(seq)-j+1] ]

(***************************************************************************)
(* Prefixes and suffixes of sequences.                                     *)
(***************************************************************************)

IsPrefix(s,t) == \E u \in Seq(Range(t)) : t = s \o u
IsStrictPrefix(s,t) == IsPrefix(s,t) /\ s # t

IsSuffix(s,t) == \E u \in Seq(Range(t)) : t = u \o s
IsStrictSuffix(s,t) == IsSuffix(s,t) /\ s # t

============================================================================