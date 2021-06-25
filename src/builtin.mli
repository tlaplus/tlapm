(*
 * Copyright (C) 2011  INRIA and Microsoft Corporation
 *)

type builtin =
    (* Logic *)
  | TRUE
  | FALSE
  | Implies
  | Equiv
  | Conj
  | Disj
  | Neg
  | Eq
  | Neq
    (* Sets *)
  | STRING
  | BOOLEAN
  | SUBSET
  | UNION
  | DOMAIN
  | Subseteq
  | Mem  (* \in *)
  | Notmem  (* \notin *)
  | Setminus
  | Cap
  | Cup
    (* modal *)
  | Prime
  | StrongPrime
  | Leadsto  (* ~> *)
  | ENABLED
  | UNCHANGED
  | Cdot
  | Actplus  (* -+-> *)
  | Box of bool
  | Diamond
    (* arithmetic *)
  | Nat
  | Int
  | Real
  | Plus
  | Minus
  | Uminus
  | Times
  | Ratio
  | Quotient
  | Remainder
  | Exp
  | Infinity
  | Lteq
  | Lt
  | Gteq
  | Gt
  | Divides
  | Range
    (* sequences *)
  | Seq
  | Len
  | BSeq
  | Cat
  | Append
  | Head
  | Tail
  | SubSeq
  | SelectSeq
    (* tlc *)
  | OneArg
  | Extend
  | Print
  | PrintT
  | Assert
  | JavaTime
  | TLCGet
  | TLCSet
  | Permutations
  | SortSeq
  | RandomElement
  | Any
  | ToString
    (* special *)
  | Unprimable
  | Irregular
