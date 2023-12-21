(* Builtin ordinary operators of TLA+.

Copyright (C) 2008-2010  INRIA and Microsoft Corporation
*)

(** The TLA+ builtin operators *)
type builtin =
    (* Logic *)
  | TRUE | FALSE | Implies | Equiv | Conj | Disj
  | Neg | Eq | Neq
    (* Sets *)
  | STRING | BOOLEAN | SUBSET | UNION | DOMAIN
  | Subseteq | Mem | Notmem | Setminus | Cap
  | Cup
    (* modal *)
  | Prime | StrongPrime | Leadsto | ENABLED | UNCHANGED | Cdot
  | Actplus  (* -+-> *)
  | Box of bool (* the bool indicates an application of the Box to a
  non-temporal formula and is added in a post processing step *) | Diamond
    (* arithmetic *)
  | Nat | Int | Real | Plus | Minus | Uminus
  | Times | Ratio | Quotient | Remainder | Exp
  | Infinity | Lteq | Lt | Gteq | Gt | Divides
  | Range
    (* sequences *)
  | Seq | Len | BSeq | Cat | Append | Head
  | Tail | SubSeq | SelectSeq
    (* tlc *)
  | OneArg | Extend | Print | PrintT | Assert
  | JavaTime | TLCGet | TLCSet | Permutations
  | SortSeq | RandomElement | Any | ToString
    (* special *)
  | Unprimable | Irregular
