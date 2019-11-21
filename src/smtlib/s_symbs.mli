(*
 * smtlib/symbs.mli -- manage symbols and declarations
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

open S_t


(** {3 Symbol Dependencies} *)

(** The signature [S] represents an interface that permits to make requests
    and get answers, with possible side effects.
*)
module type S = sig
  type req  (** Type of requests *)
  type ans  (** Type of answers *)
  type s

  (** Return [true] is a request can be fulfilled *)
  val solved  : s -> req -> bool

  (** Recursively resolve dependencies raised by a request *)
  val resolve : s -> req -> s

  (** Return the result of a request, possibly after calling [resove] *)
  val ask     : s -> req -> s * ans
end

(** A generic module for the representation of dependencies.
    The type {!req} of requests is generic. To each request must be
    attached a particular symbol through {!get_symbol}, and a
    particular declaration through {!get_decl}.
    The functions {!deps} and {!axioms} represent, respectively,
    what requests does any request depend of, and what axioms.
*)
module type Deps = sig
  type req  (** Unspecified *)

  val get_symbol  : req -> symbol
  val get_decl    : req -> decl

  val deps        : req -> req list
  val axioms      : req -> term list
end

(** [Theories] implements [S] as a symbol manager.
    Asking for a symbol will check for depending symbols and axioms,
    make all necessary declarations in the theory and return the
    declaration of the requested symbol.
*)
module TheoryManager (D : Deps) : S
  with type req = D.req
   and type ans = decl
   and type s = theory


(** {3 Predefined Symbols} *)

(** Core theory of SMT-LIB
    Contains the sort Bool and logical operators
    true, false, not, =>, and, or, xor, =, distinct, ite
*)
val core_theory : theory

type core_smb_t =
  (* Sorts *)
  | CoreBool
  (* Operators *)
  | CoreTrue
  | CoreFalse
  | CoreNot
  | CoreImp
  | CoreAnd
  | CoreOr
  | CoreXor
  | CoreEq
  | CoreNeq
  | CoreIte

val core_smb  : core_smb_t -> symbol
val core_decl : core_smb_t -> decl

(** Ints theory of SMT-LIB
    Contains the sort Int and integer operators
    - (minus), - (substraction), +, *, div, mod, abs, <=, <, >=, >
*)
val ints_theory : theory
(** It is built on top of {!core_theory} *)

type ints_smb_t =
  (* Sorts *)
  | IntsInt
  (* Operators *)
  | IntsSubs
  | IntsPlus
  | IntsMult
  | IntsDiv
  | IntsMod
  | IntsAbs
  | IntsLe
  | IntsLt
  | IntsGe
  | IntsGt

val ints_smb  : ints_smb_t -> symbol
val ints_decl : ints_smb_t -> decl


(** {3 Symbols of Untyped Encoding} *)

(** These are the symbols for TLA+ operators that can be encoded directly to
    first-order logic. Are excluded symbols for higher-order constructs such
    as set comprehension and choose operator. Those are handled in {!Direct}.
*)

type sets_smb_t =
  (* Sorts *)
  | U
  (* Predicates *)
  | In
  | Subset
  (* Operators *)
  | SetEnum of int
  | PowerSet
  | UnionSet
  | Inter
  | Union
  | Diff

val sets_smb  : sets_smb_t -> symbol
val sets_decl : sets_smb_t -> decl


type bools_smb_t =
  | BSet
  | BCast

val bools_smb   : bools_smb_t -> symbol
val bools_decl  : bools_smb_t -> decl


type strings_smb_t =
  | SSort
  | SSet
  | SLit of string
  | SCast

val strings_smb   : strings_smb_t -> symbol
val strings_decl  : strings_smb_t -> decl


(** Not to be confused with {!ints_smt_t}. These are symbols for the operators
    of U that correspond to int operators. *)
type uints_smb_t =
  | ISet | NSet
  | ICast
  | IPlus | IMinus | IMult | IDiv | IMod
  | ILe
  | IRange

val uints_smb   : uints_smb_t -> symbol
val uints_decl  : uints_smb_t -> decl


type funs_smb_t =
  | FunSet
  | DomSet
  | FunApp
  | FunExcept

val funs_smb  : funs_smb_t -> symbol
val funs_decl : funs_smb_t -> decl


type tuples_smb_t =
  | ProdSet of int
  | Tuple of int

val tuples_smb  : tuples_smb_t -> symbol
val tuples_decl : tuples_smb_t -> decl


type recs_smb_t =
  | RecSet of int
  | Record of int

val recs_smb  : recs_smb_t -> symbol
val recs_decl : recs_smb_t -> decl

