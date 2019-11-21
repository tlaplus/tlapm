(*
 * Copyright (C) 2011  INRIA and Microsoft Corporation
 *)

(** Packaging Module for SMT-LIB Encoding *)

module T : sig
  type symbol = string
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

  type kind = SortDecl | OpDecl
  type decl =
    { kind : kind
    ; smb : symbol
    ; pars : symbol list
    ; rank : sort list * sort
    ; iscore : bool
    }
  type assrt =
    { name : string
    ; form : term
    }
  module Sm = Util.Coll.Sm
  type theory =
    { decls   : decl Sm.t
    ; sorts   : symbol Deque.dq
    ; ops     : symbol Deque.dq
    ; assrts  : assrt Sm.t
    }

  val mem         : theory -> symbol -> bool
  val find        : theory -> symbol -> decl
  val add_decl    : theory -> decl -> theory
  val maybe_decl  : theory -> decl -> theory
  val add_assrt   : theory -> assrt -> theory
end

module Symbs : sig
  open T

  val core_theory : theory
end

module Axioms : sig
end

module Direct : sig
  open Expr.T
  open T

  val encode_direct : sequent -> theory
end

module Fmt : sig
  open T

  val pp_print_symbol         : Format.formatter -> symbol -> unit
  val pp_print_term           : Format.formatter -> term -> unit
  val pp_print_lit            : Format.formatter -> lit -> unit
  val pp_print_qual_ident     : Format.formatter -> qual_ident -> unit
  val pp_print_var_bind       : Format.formatter -> var_bind -> unit
  val pp_print_sorted_bind    : Format.formatter -> sorted_bind -> unit
  val pp_print_match_case     : Format.formatter -> match_case -> unit
  val pp_print_sort           : Format.formatter -> sort -> unit
  val pp_print_pattern        : Format.formatter -> pattern -> unit
  val pp_print_attribute      : Format.formatter -> attribute -> unit
  val pp_print_attribute_val  : Format.formatter -> attribute_val -> unit
end

