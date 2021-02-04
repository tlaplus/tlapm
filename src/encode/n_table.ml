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

    (* TYPED *)
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
  (* TODO *)

    (* SPECIAL *)
  | Cast of ty
  | True of ty

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
  (* Booleans *)
  | BoolSetDef
  (* Strings *)
  | StrSetDef
  | StrLitDistinct of string * string
  (* Arithmetic *)
  | IntSetDef
  | NatSetDef
  | IntLitDistinct of int * int
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
  | FunExt
  | FunConstrIsafcn
  | FunSetDef
  | FunDomDef
  | FunAppDef

    (* TYPED *)
  (* TODO *)

    (* SPECIAL *)
  | IntGuard
  | Typing of tla_smb

