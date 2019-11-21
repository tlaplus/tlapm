(*
 * smtlib/t.mli -- S-expressions
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

exception Double_declaration


type symbol = string

(** Make a proper SMT-LIB identifier *)
val to_symbol : string -> symbol

(** {3 Terms and Formulas of SMT-LIB} *)

type term =
  | Literal of lit
  | App of qual_ident * term list
  | Let of var_bind list * term
  | Quant of quant * sorted_bind list * term
  | Match of term * match_case list
  | Annot of term * attribute list

and lit =
  | LInt of int
  | LStr of string

and quant = Forall | Exists

and qual_ident =
  | Id of symbol
  | As of symbol * sort

and var_bind = symbol * term

and sorted_bind = symbol * sort

and match_case = pattern * term

and sort =
  | Sort of symbol * sort list

and pattern = symbol * symbol list

and attribute = symbol * attribute_val option
and attribute_val =
  | AttrLit of lit
  | AttrIdent of symbol
  | AttrList of term list


(** {4 Constructor Utilities} *)

val intlit : int -> term
val strlit : string -> term

val cst : symbol -> term
val una : symbol -> term -> term
val bin : symbol -> term -> term -> term
val ter : symbol -> term -> term -> term -> term
val app : symbol -> term list -> term

val forall : (symbol * sort) list -> term -> term
val exists : (symbol * sort) list -> term -> term
val lets : (symbol * term) list -> term -> term
val cases : term -> (pattern * term) list -> term

val pattern : term -> term list -> term

val sort : ?pars:sort list -> symbol -> sort


(** {4 Term Utilities} *)

module SmbSet : Set.S with type elt = symbol

(** Free variables of a term. The first argument is a set of symbols that
    should *not* be counted as variables, typically declared constants.
    This is necessary because there is no distinction between a variable and
    a constant in the syntax.
*)
val fv : SmbSet.t -> term -> SmbSet.t

(** [subst t x v] returns [t] with [v$ substituted for [x]. *)
val subst : term -> symbol -> term -> term


(** {3 Declarations and Theories} *)

type kind = SortDecl | OpDecl

(** A common type for sort and function declarations of SMT-LIB. *)
type decl =
  { kind : kind
  ; smb : symbol            (** Declared symbol *)
  ; pars : symbol list      (** For operators *)
  ; rank : sort list * sort (** For sorts, the length of the [sort list] is the arity *)
  ; iscore : bool           (** [true] for implicit core declarations *)
  }

(** A type for assertions *)
type assrt =
  { name : string
  ; form : term
  }

module Sm = Util.Coll.Sm

(** A [theory] represents a SMT-LIB problem. The purpose of the translation
    is to build a value of this type.
*)
type theory =
  { decls   : decl Sm.t       (** All declarations *)
  ; sorts   : symbol Deque.dq (** Declared sort symbols *)
  ; ops     : symbol Deque.dq (** Declared operator symbols *)
  ; assrts  : assrt Sm.t      (** Asserted expressions *)
  }
(** Invariants:
    * For any symbol in [sorts], there is a binding in [decls] with [kind = SortDecl];
    * For any symbol in [ops], there is a binding in [decls] with [kind = OpDecl];
    * All keys of [decls] are in [sorts] and [ops];
    * There are no duplicates in [sorts @@ ops];
    * For bindings of [assrts], the field [name] is either the key or ""
*)


(** {4 Constructor Utilities for Declarations and Assertions} *)

val mk_sort_decl  : ?iscore:bool -> symbol -> int -> decl
val mk_op_decl    : ?iscore:bool -> symbol -> ?pars:symbol list -> (sort list * sort) -> decl

val mk_cst_decl : ?iscore:bool -> symbol -> ?pars:symbol list -> sort -> decl
val mk_una_decl : ?iscore:bool -> symbol -> ?pars:symbol list -> sort -> sort -> decl
val mk_bin_decl : ?iscore:bool -> symbol -> ?pars:symbol list -> sort -> sort -> sort -> decl
val mk_ter_decl : ?iscore:bool -> symbol -> ?pars:symbol list -> sort -> sort -> sort -> sort -> decl

val mk_assrt  : ?name:string -> term -> assrt

val empty_theory : theory

val combine : theory -> theory -> theory

(** {4 Theory Management} *)

(** Return [true] if the symbol is declared (either as sort or op) *)
val mem         : theory -> symbol -> bool

(** Return the declaration of a symbol.
    @raise Not_found if the symbol is undeclared.
*)
val find        : theory -> symbol -> decl

(** Lile {!find}, but instead of raising [Not_found], return [None],
    otherwise [Some dcl] where [dcl] is the declaration.
*)
val find_opt    : theory -> symbol -> decl option

(** Return the theory with additional declaration.
    @raise Double_declaration if a declaration of the same symbol
    is present.
*)
val add_decl    : theory -> decl -> theory

(** Like {!add_decl}, but instead of raising [Double_declaration],
    return the theory unchanged.
*)
val maybe_decl  : theory -> decl -> theory

(** Return the theory with additional assertion. *)
val add_assrt   : theory -> assrt -> theory

