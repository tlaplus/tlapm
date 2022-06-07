(*
 * builtin.ml --- builtin ordinary operators
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

Revision.f "$Rev$";;

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
  | Actplus | Box of bool (* the bool indicates an applitcation of the Box to a
  non-temporal formula and is added in a post processing step *) | Diamond
    (* arithmetic *)
  | Nat | Int | Real | Plus | Minus | Uminus
  | Times | Ratio | Quotient | Remainder | Exp
  | Infinity | Lteq | Lt | Gteq | Gt | Divides
  | Range
    (* sequences *)
  | Seq | Len | BSeq | Cat | Append | Head
  | Tail | SubSeq | SelectSeq
    (* finite sets *)
  | IsFiniteSet | Card
    (* tlc *)
  | OneArg | Extend | Print | PrintT | Assert
  | JavaTime | TLCGet | TLCSet | Permutations
  | SortSeq | RandomElement | Any | ToString
    (* special *)
  | Unprimable | Irregular

let builtin_to_string = function
  | TRUE -> "TRUE"
  | FALSE -> "FALSE"
  | Implies -> "Implies"
  | Equiv -> "Equiv"
  | Conj -> "Conj"
  | Disj -> "Disj"
  | Neg -> "Neg"
  | Eq -> "Eq"
  | Neq -> "Neq"
  | STRING -> "STRING"
  | BOOLEAN -> "BOOLEAN"
  | SUBSET -> "SUBSET"
  | UNION -> "UNION"
  | DOMAIN -> "DOMAIN"
  | Subseteq -> "Subseteq"
  | Mem -> "Mem"
  | Notmem -> "Notmem"
  | Setminus -> "Setminus"
  | Cap -> "Cap"
  | Cup -> "Cup"
  | Prime -> "Prime"
  | StrongPrime -> "StrongPrime"
  | Leadsto -> "Leadsto"
  | ENABLED -> "ENABLED"
  | UNCHANGED -> "UNCHANGED"
  | Cdot -> "Cdot"
  | Actplus -> "Actplus"
  | Box true -> "Box(true)"
  | Box false -> "Box(false)"
  | Diamond -> "Diamond"
  | Nat -> "Nat"
  | Int -> "Int"
  | Real -> "Real"
  | Plus -> "Plus"
  | Minus -> "Minus"
  | Uminus -> "Uminus"
  | Times -> "Times"
  | Ratio -> "Ratio"
  | Quotient -> "Quotient"
  | Remainder -> "Remainder"
  | Exp -> "Exp"
  | Infinity -> "Infinity"
  | Lteq -> "Lteq"
  | Lt -> "Lt"
  | Gteq -> "Gteq"
  | Gt -> "Gt"
  | Divides -> "Divides"
  | Range -> "Range"
  | Seq -> "Seq"
  | Len -> "Len"
  | BSeq -> "BSeq"
  | Cat -> "Cat"
  | Append -> "Append"
  | Head -> "Head"
  | Tail -> "Tail"
  | SubSeq -> "SubSeq"
  | SelectSeq -> "SelectSeq"
  | IsFiniteSet -> "IsFiniteSet"
  | Card -> "Card"
  | OneArg -> "OneArg"
  | Extend -> "Extend"
  | Print -> "Print"
  | PrintT -> "PrintT"
  | Assert -> "Assert"
  | JavaTime -> "JaveTime"
  | TLCGet -> "TLCGet"
  | TLCSet -> "TLCSet"
  | Permutations -> "Permutations"
  | SortSeq -> "SortSeq"
  | RandomElement -> "RandomElement"
  | Any -> "Any"
  | ToString -> "ToString"
  | Unprimable -> "Unprimable"
  | Irregular -> "Irregular"
