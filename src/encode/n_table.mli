(*
 * encode/table.mli --- table of symbols and axioms used to encode POs
 *
 *
 * Copyright (C) 2022  INRIA and Microsoft Corporation
 *)

open Type.T

(** Inventory of all special operators that the encodings of TLA+ use to
    translate expressions.
    The backends that use the relevant encodings are: SMT, Zipper.

    This module was created because {!Builtin} doesn't include everthing.
    Not included in {!Builtin} are:
      - Second-order operators, like set-comprehension, CHOOSE...
      - Invisible operators, like isafcn;
      - Variants of the builtin operators with different types. For instance,
        the '+' of TLA+ may have to be translated as a '+ : int * int -> int'
        or a '+ : U * U -> U' (where 'U' is the universe of ZFC), depending
        on the backend/context.
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
  | Add (* unused *)
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
  | FunIm
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
  (* Finite Sets *)
  | FSIsFiniteSet
  | FSCard

    (* TYPED *)
  (* Arithmetic *)
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
  (* Finite Sets *)
  | TFSCard of ty
  | TFSMem of ty
  | TFSSubseteq of ty
  | TFSEmpty of ty
  | TFSSingleton of ty
  | TFSAdd of ty
  | TFSCup of ty
  | TFSCap of ty
  | TFSSetminus of ty

    (* SPECIAL *)
  | Cast of ty
  | Proj of ty
  | True of ty
  | Anon of string * ty2
  | ExtTrigEq of ty
  | ExtTrig
  | IsSetOf

(** Inventory of the axioms that may be used in the Zipperposition encoding. *)
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
  | SubsetDefAlt
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
  | NonNegIsPos
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
  | FunSetImIntro
  | FunSetSubs
  | FunDomDef
  | FunAppDef
  | FunTyping
  | FunExceptIsafcn
  | FunExceptDomDef
  | FunExceptAppDef1
  | FunExceptAppDef2
  | FunExceptTyping
  | FunImDef
  | FunImIntro
  | FunImElim
  (* Tuples *)
  | TupIsafcn of int
  | TupDomDef of int
  | TupAppDef of int
  | TupExcept of int * int
  | ProductDef of int
  | ProductIntro of int
  | ProductElim of int
  (* Records *)
  | RecIsafcn of string list
  | RecDomDef of string list
  | RecAppDef of string list
  | RecExcept of string list * int
  | RecSetDef of string list
  | RecSetIntro of string list
  | RecSetElim of string list
  (* Sequences *)
  | SeqSetIntro
  | SeqSetElim1
  | SeqSetElim2
  | SeqLenDef
  | SeqCatTyping
  | SeqCatLen
  | SeqCatApp1
  | SeqCatApp2
  | SeqAppendTyping
  | SeqAppendLen
  | SeqAppendApp1
  | SeqAppendApp2
  | SeqHeadDef
  | SeqTailTyping
  | SeqTailLen
  | SeqTailApp
  | SeqSubseqTyping
  | SeqSubseqLen
  | SeqSubseqApp
  | SeqSelectseqTyping
  | SeqSelectseqLen
  | SeqSelectseqNil
  | SeqSelectseqApp
  | SeqSelectseqAppend
  | SeqTupTyping of int
  | SeqTupLen of int

    (* SPECIAL *)
  | CastInj of ty
  | CastInjAlt of ty
  | TypeGuard of ty
  | TypeGuardIntro of ty
  | TypeGuardElim of ty
  | Typing of tla_smb (** Only for typed symbols *)
  | ExtTrigEqDef of ty
  | ExtTrigEqTrigger of ty
  | DisjointTrigger
  | EmptyComprehensionTrigger
  | AssertIsSetOf of int
  | CompareSetOfTrigger
  | ExtTrigEqCardPropagate


val tla_smb_to_string : tla_smb -> string

(** Short description for the axiom *)
val axm_desc : tla_axm -> string

