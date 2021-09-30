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
  | FunExcept
  (* Tuples *)
  | Tuple of int
  | Product of int
  (* Records *)
  | Rec of string list
  | RecSet of string list
  (* Sequences *)
  | SeqSeq
  | SeqLen
  | SeqBSeq
  | SeqCat
  | SeqAppend
  | SeqHead
  | SeqTail
  | SeqSubSeq
  | SeqSelectSeq

    (* TYPED *)
  (* Set Theory *)
  | TMem of ty
  (* Strings *)
  | TStrSet
  | TStrLit of string
  (* Arithmetic *)
  | TIntSet
  | TNatSet
  | TIntLit of int
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
  | SubsetEqDef_alt1
  | SubsetEqDef_alt2
  | EnumDef_alt1 of int
  | EnumDef_alt2 of int
  (* Strings *)
  | StrLitIsstr of string
  | StrLitDistinct of string * string
  (* Arithmetic *)
  | IntLitIsint of int
  | IntLitDistinct of int * int
  | IntLitZeroCmp of int
  | NatSetDef
  | IntPlusTyping
  | IntUminusTyping
  | IntMinusTyping
  | IntTimesTyping
  | IntQuotientTyping
  | IntRemainderTyping
  | IntExpTyping
  | NatPlusTyping
  | NatTimesTyping
  | IntRangeDef
  | LteqReflexive
  | LteqTransitive
  | LteqAntisym
  (* Functions *)
  | FunExt
  | FunConstrIsafcn
  | FunSetDef
  | FunDomDef
  | FunAppDef
  | FunExceptIsafcn
  | FunExceptDomDef
  | FunExceptAppDef
  (* Tuples *)
  | TupIsafcn of int
  | ProductDef of int
  | TupDomDef of int
  | TupAppDef of int * int
  | ProductDef_alt1 of int
  | ProductDef_alt21 of int
  | ProductDef_alt22 of int
  (* Records *)
  | RecIsafcn of string list
  | RecSetDef of string list
  | RecDomDef of string list
  | RecAppDef of string list
  (* Sequences *)
  | SeqTailIsSeq

    (* TYPED *)
  (* Strings *)
  | TStrSetDef
  | TStrLitDistinct of string * string
  (* Arithmetic *)
  | TIntSetDef
  | TNatSetDef
  | TIntRangeDef

    (* SPECIAL *)
  | CastInj of ty
  | TypeGuard of ty
  | Typing of tla_smb (** Only for typed symbols *)

let axm_desc = function
  | ChooseDef -> "ChooseDef"
  | ChooseExt -> "ChooseExt"
  | SetExt -> "SetExt"
  | SubsetEqDef -> "SubsetEqDef"
  | EnumDef n -> Format.sprintf "EnumDef %d" n
  | UnionDef -> "UnionDef"
  | SubsetDef -> "SubsetDef"
  | CupDef -> "CupDef"
  | CapDef -> "CapDef"
  | SetMinusDef -> "SetMinusDef"
  | SetStDef -> "SetStDef"
  | SetOfDef n -> Format.sprintf "SetOfDef %d" n
  | SubsetEqDef_alt1 -> "SubsetEqDef_alt1"
  | SubsetEqDef_alt2 -> "SubsetEqDef_alt2"
  | EnumDef_alt1 n -> Format.sprintf "EnumDef_alt1 %d" n
  | EnumDef_alt2 n -> Format.sprintf "EnumDef_alt2 %d" n
  | StrLitIsstr s -> Format.sprintf "StrLitIsstr %s" s
  | StrLitDistinct (s1, s2) -> Format.sprintf "StrLitDistinct %s %s" s1 s2
  | IntLitIsint n -> Format.sprintf "IntLitIsint %d" n
  | IntLitDistinct (n1, n2) -> Format.sprintf "IntLitDistinct %d %d" n1 n2
  | IntLitZeroCmp n -> Format.sprintf "IntLitZeroCmp %d" n
  | NatSetDef -> "NatSetDef"
  | IntPlusTyping -> "IntPlusTyping"
  | IntUminusTyping -> "IntUminusTyping"
  | IntMinusTyping -> "IntMinusTyping"
  | IntTimesTyping -> "IntTimesTyping"
  | IntQuotientTyping -> "IntQuotientTyping"
  | IntRemainderTyping -> "IntRemainderTyping"
  | IntExpTyping -> "IntExpTyping"
  | NatPlusTyping -> "NatPlusTyping"
  | NatTimesTyping -> "NatTimesTyping"
  | IntRangeDef -> "IntRangeDef"
  | LteqReflexive -> "LteqReflexive"
  | LteqTransitive -> "LteqTransitive"
  | LteqAntisym -> "LteqAntisym"
  | FunExt -> "FunExt"
  | FunConstrIsafcn -> "FunConstrIsafcn"
  | FunSetDef -> "FunSetDef"
  | FunDomDef -> "FunDomDef"
  | FunAppDef -> "FunAppDef"
  | FunExceptIsafcn -> "FunExceptIsafcn"
  | FunExceptDomDef -> "FunExceptDomDef"
  | FunExceptAppDef -> "FunExceptAppDef"
  | TupIsafcn n -> Format.sprintf "TupIsafcn %d" n
  | ProductDef n -> Format.sprintf "ProductDef %d" n
  | TupDomDef n -> Format.sprintf "TupDomDef %d" n
  | TupAppDef (n1, n2) -> Format.sprintf "TupAppDef %d %d" n1 n2
  | ProductDef_alt1 n -> Format.sprintf "ProductDef_alt1 %d" n
  | ProductDef_alt21 n -> Format.sprintf "ProductDef_alt21 %d" n
  | ProductDef_alt22 n -> Format.sprintf "ProductDef_alt22 %d" n
  | RecIsafcn fs -> "" (*Format.sprintf "RecIsafcn %a" (Fmtutil.pp_print_delimited ~sep:Format.pp_print_space Format.pp_print_string) fs*)
  | RecSetDef fs -> "" (*Format.sprintf "RecSetDef %a" (Fmtutil.pp_print_delimited ~sep:Format.pp_print_space Format.pp_print_string) fs*)
  | RecDomDef fs -> "" (*Format.sprintf "RecDomDef %a" (Fmtutil.pp_print_delimited ~sep:Format.pp_print_space Format.pp_print_string) fs*)
  | RecAppDef fs -> "" (*Format.sprintf "RecAppDef %a" (Fmtutil.pp_print_delimited ~sep:Format.pp_print_space Format.pp_print_string) fs*)
  | SeqTailIsSeq -> "SeqTailIsSeq"
  | TStrSetDef -> "TStrSetDef"
  | TStrLitDistinct (s1, s2) -> Format.sprintf "TStrLitDistinct %s %s" s1 s2
  | TIntSetDef -> "TIntSetDef"
  | TNatSetDef -> "TNatSetDef"
  | TIntRangeDef -> "TIntRangeDef"
  | CastInj ty -> Format.sprintf "CastInj"
  | TypeGuard ty -> Format.sprintf "TypeGuard"
  | Typing tla_smb -> Format.sprintf "Typing"

