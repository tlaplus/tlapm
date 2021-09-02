(*
 * encode/table.mli --- table of symbols and axioms used to encode POs
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
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

