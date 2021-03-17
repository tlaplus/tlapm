(*
 * encode/table.mli --- table of symbols and axioms used to encode POs
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

open Type.T

(** This module is an inventory of every TLA+ builtin symbol that may be used
    by the Zipperposition encoding.  It is a generalization of {!Builtin} in
    that it includes second-order operators (set-comprehension,...), and
    eventual typed variants of operators ('+' as TLA+ uninterpreted addition,
    or addition between integers, or between reals,...)

    This representation is abstract, but each symbol has data associated to it,
    that should be obtained through the function {!N_smb.mk_smb}.
*)


(** Abstract type for builtin symbols.  The list is divided into three parts:
    - _UNTYPED_: The standard operators of TLA+;
    - _TYPED_: Variants of the standard operators with types;
    - _SPECIAL_: Others
*)
type tla_smb =
    (* UNTYPED *)
  (* Logic *)
  | Choose
  (* Set Theory *)
  | Mem
  | SubsetEq
  | SetEnum of int
  | Union
  | Subset
  | Cup
  | Cap
  | SetMinus
  | SetSt
  | SetOf of int
  (* Booleans *)
  | BoolSet
  (* Strings *)
  | StrSet
  | StrLit of string
  (* Arithmetic *)
  | IntSet
  | NatSet
  | IntLit of int
  | IntPlus
  | IntUminus
  | IntMinus
  | IntTimes
  | IntQuotient
  | IntRemainder
  | IntExp
  | IntLteq
  | IntLt
  | IntGteq
  | IntGt
  | IntRange
  (* Functions *)
  | FunIsafcn
  | FunSet
  | FunConstr
  | FunDom
  | FunApp
  (* Tuples *)
  | Tuple of int
  | Product of int
  (* Records *)
  | Rec of string list
  | RecSet of string list

    (* TYPED *)
  (* Strings *)
  | TStrLit of string
  (* Arithmetic *)
  | TIntPlus
  | TIntUminus
  | TIntMinus
  | TIntTimes
  | TIntQuotient
  | TIntRemainder
  | TIntExp
  | TIntLteq
  | TIntLt
  | TIntGteq
  | TIntGt
  | TIntRange

    (* SPECIAL *)
  | Cast of ty
  | True of ty
  | Anon of string * ty2

(** Inventory of the axioms that may be used in the Zipperposition encoding. *)
type tla_axm =
    (* UNTYPED *)
  (* Logic *)
  | ChooseDef
  | ChooseExt
  (* Set Theory *)
  | SetExt
  | SubsetEqDef
  | EnumDef of int
  | UnionDef
  | SubsetDef
  | CupDef
  | CapDef
  | SetMinusDef
  | SetStDef
  | SetOfDef of int
  (* Strings *)
  | StrLitIsstr of string
  | StrLitDistinct of string * string
  (* Arithmetic *)
  | IntLitIsint of int
  | IntLitDistinct of int * int
  | NatSetDef
  | IntPlusTyping
  | IntUminusTyping
  | IntMinusTyping
  | IntTimesTyping
  | IntQuotientTyping
  | IntRemainderTyping
  | IntExpTyping
  | IntRangeDef
  (* Functions *)
  | FunExt
  | FunConstrIsafcn
  | FunSetDef
  | FunDomDef
  | FunAppDef
  (* Tuples *)
  | TupIsafcn of int
  | ProductDef of int
  | TupDomDef of int
  | TupAppDef of int * int
  (* Records *)
  | RecIsafcn of string list
  | RecSetDef of string list
  | RecDomDef of string list
  | RecAppDef of string list

    (* TYPED *)
  (* Strings *)
  | TStrLitDistinct of string * string

    (* SPECIAL *)
  | CastInj of ty0
  | TypeGuard of ty0
  | Typing of tla_smb (** Only for typed symbols *)

