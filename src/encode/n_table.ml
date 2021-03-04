(*
 * encode/table.ml --- table of symbols and axioms used to encode POs
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

open Type.T


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

    (* TYPED *)

  (* Strings *)
  | TStrLitDistinct of string * string

    (* SPECIAL *)

  | CastInj of ty0
  | TypeGuard of ty0
  | Typing of tla_smb (** Only for typed symbols *)

