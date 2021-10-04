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
  | SubsetEqIntro
  | SubsetEqElim
  | EnumDef of int
  | EnumDefIntro of int
  | EnumDefElim of int
  | UnionDef
  | UnionIntro
  | UnionElim
  | SubsetDef
  | SubsetIntro
  | SubsetElim
  | CupDef
  | CapDef
  | SetMinusDef
  | SetStDef
  | SetOfDef of int
  | SetOfIntro of int
  | SetOfElim of int
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
  | FunSetIntro
  | FunSetElim1
  | FunSetElim2
  | FunDomDef
  | FunAppDef
  | FunExceptIsafcn
  | FunExceptDomDef
  | FunExceptAppDef
  (* Tuples *)
  | TupIsafcn of int
  | TupDomDef of int
  | TupAppDef of int * int
  | ProductDef of int
  | ProductIntro of int
  | ProductElim of int
  (* Records *)
  | RecIsafcn of string list
  | RecDomDef of string list
  | RecAppDef of string list
  | RecSetDef of string list
  | RecSetIntro of string list
  | RecSetElim of string list
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


let tla_smb_to_string = function
  | Choose -> "Choose"
  | Mem -> "Mem"
  | SubsetEq -> "SubsetEq"
  | SetEnum n -> Format.sprintf "SetEnum %d" n
  | Union -> "Union"
  | Subset -> "Subset"
  | Cup -> "Cup"
  | Cap -> "Cap"
  | SetMinus -> "SetMinus"
  | SetSt -> "SetSt"
  | SetOf n -> Format.sprintf "SetOf %d" n
  | BoolSet -> "BoolSet"
  | StrSet -> "StrSet"
  | StrLit s -> Format.sprintf "StrLit %s" s
  | IntSet -> "IntSet"
  | NatSet -> "NatSet"
  | IntLit n -> Format.sprintf "IntLit %d" n
  | IntPlus -> "IntPlus"
  | IntUminus -> "IntUminus"
  | IntMinus -> "IntMinus"
  | IntTimes -> "IntTimes"
  | IntQuotient -> "IntQuotient"
  | IntRemainder -> "IntRemainder"
  | IntExp -> "IntExp"
  | IntLteq -> "IntLteq"
  | IntLt -> "IntLt"
  | IntGteq -> "IntGteq"
  | IntGt -> "IntGt"
  | IntRange -> "IntRange"
  | FunIsafcn -> "FunIsafcn"
  | FunSet -> "FunSet"
  | FunConstr -> "FunConstr"
  | FunDom -> "FunDom"
  | FunApp -> "FunApp"
  | FunExcept -> "FunExcept"
  | Tuple n -> Format.sprintf "Tuple %d" n
  | Product n -> Format.sprintf "Product %d" n
  | Rec fs -> String.concat " " ("Rec" :: fs)
  | RecSet fs -> String.concat " " ("RecSet" :: fs)
  | SeqSeq -> "SeqSeq"
  | SeqLen -> "SeqLen"
  | SeqBSeq -> "SeqBSeq"
  | SeqCat -> "SeqCat"
  | SeqAppend -> "SeqAppend"
  | SeqHead -> "SeqHead"
  | SeqTail -> "SeqTail"
  | SeqSubSeq -> "SeqSubSeq"
  | SeqSelectSeq -> "SeqSelectSeq"
  | TMem ty -> "TMem " ^ ty_to_string ty
  | TStrSet -> "TStrSet"
  | TStrLit s -> Format.sprintf "TStrLit %s" s
  | TIntSet -> "TIntSet"
  | TNatSet -> "TNatSet"
  | TIntLit n -> Format.sprintf "TIntLit %d" n
  | TIntPlus -> "TIntPlus"
  | TIntUminus -> "TIntUminus"
  | TIntMinus -> "TIntMinus"
  | TIntTimes -> "TIntTimes"
  | TIntQuotient -> "TIntQuotient"
  | TIntRemainder -> "TIntRemainder"
  | TIntExp -> "TIntExp"
  | TIntLteq -> "TIntLteq"
  | TIntLt -> "TIntLt"
  | TIntGteq -> "TIntGteq"
  | TIntGt -> "TIntGt"
  | TIntRange -> "TIntRange"
  | Cast ty -> "Cast " ^ ty_to_string ty
  | True ty -> "True" ^ ty_to_string ty
  | Anon (s, ty2) -> "Anon " ^ s ^ " " ^ ty2_to_string ty2

let axm_desc = function
  | ChooseDef -> "ChooseDef"
  | ChooseExt -> "ChooseExt"
  | SetExt -> "SetExt"
  | SubsetEqDef -> "SubsetEqDef"
  | SubsetEqIntro -> "SubsetEqIntro"
  | SubsetEqElim -> "SubsetEqElim"
  | EnumDef n -> Format.sprintf "EnumDef %d" n
  | EnumDefIntro n -> Format.sprintf "EnumDefIntro %d" n
  | EnumDefElim n -> Format.sprintf "EnumDefElim %d" n
  | UnionDef -> "UnionDef"
  | UnionIntro -> "UnionIntro"
  | UnionElim -> "UnionElim"
  | SubsetDef -> "SubsetDef"
  | SubsetIntro -> "SubsetIntro"
  | SubsetElim -> "SubsetElim"
  | CupDef -> "CupDef"
  | CapDef -> "CapDef"
  | SetMinusDef -> "SetMinusDef"
  | SetStDef -> "SetStDef"
  | SetOfDef n -> Format.sprintf "SetOfDef %d" n
  | SetOfIntro n -> Format.sprintf "SetOfIntro %d" n
  | SetOfElim n -> Format.sprintf "SetOfElim %d" n
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
  | FunSetIntro -> "FunSetIntro"
  | FunSetElim1 -> "FunSetElim1"
  | FunSetElim2 -> "FunSetElim2"
  | FunDomDef -> "FunDomDef"
  | FunAppDef -> "FunAppDef"
  | FunExceptIsafcn -> "FunExceptIsafcn"
  | FunExceptDomDef -> "FunExceptDomDef"
  | FunExceptAppDef -> "FunExceptAppDef"
  | TupIsafcn n -> Format.sprintf "TupIsafcn %d" n
  | TupDomDef n -> Format.sprintf "TupDomDef %d" n
  | TupAppDef (n1, n2) -> Format.sprintf "TupAppDef %d %d" n1 n2
  | ProductDef n -> Format.sprintf "ProductDef %d" n
  | ProductIntro n -> Format.sprintf "ProductIntro %d" n
  | ProductElim n -> Format.sprintf "ProductElim %d" n
  | RecIsafcn fs -> String.concat " " ( "RecIsafcn" :: fs )
  | RecDomDef fs -> String.concat " " ( "RecDomDef" :: fs )
  | RecAppDef fs -> String.concat " " ( "RecAppDef" :: fs )
  | RecSetDef fs -> String.concat " " ( "RecSetDef" :: fs )
  | RecSetIntro fs -> String.concat " " ( "RecSetIntro" :: fs )
  | RecSetElim fs -> String.concat " " ( "RecSetElim" :: fs )
  | SeqTailIsSeq -> "SeqTailIsSeq"
  | TStrSetDef -> "TStrSetDef"
  | TStrLitDistinct (s1, s2) -> Format.sprintf "TStrLitDistinct %s %s" s1 s2
  | TIntSetDef -> "TIntSetDef"
  | TNatSetDef -> "TNatSetDef"
  | TIntRangeDef -> "TIntRangeDef"
  | CastInj ty -> "CastInj " ^ ty_to_string ty
  | TypeGuard ty -> "TypeGuard " ^ ty_to_string ty
  | Typing tla_smb -> "Typing " ^ tla_smb_to_string tla_smb

