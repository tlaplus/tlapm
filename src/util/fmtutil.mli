(*
 * fmtutil.mli --- format utilities
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

(** Formatting utilities *)

open Format

val join: string -> string list -> string
val comma: string list -> string

(** [pp_print_commasp ff ()] is equivalent to [pp_print_string ff "," ; pp_print_space ff ()]  *)
val pp_print_commasp : formatter -> unit -> unit

(** [pp_print_delimited ~sep fmt ff [a1 ; ... ; an]] is equivalent to {[
    fmt ff a1 ;
    sep ff () ;
    ...
    sep ff () ;
    fmt ff an ; ]} The default [sep] is {!pp_print_commasp}. *)
val pp_print_delimited :
  ?sep:(formatter -> unit -> unit) ->
  (formatter -> 'a -> unit) ->
  formatter -> 'a list -> unit

(** [pp_print_delimited_fold ~sep fmt v ff [a1 ; a2 ; ... ; an]] is equivalent to {[
    let v = fmt v ff a1 in
      sep ff () ;
      let v = fmt v ff a2 in
        sep ff ()
           ...
           sep ff () ;
           fmt v ff an ]}
    The default [sep] is {!pp_print_commasp}. *)
val pp_print_delimited_fold :
  ?sep:(formatter -> unit -> unit) ->
  ('v -> formatter -> 'a -> 'v) ->
  'v -> formatter -> 'a list -> 'v

(** [pp_print_with_parens fmt ff a] is equivalent to {[
    pp_print_char ff '(' ;
    fmt ff a ;
    pp_print_char ff ')' ; ]} *)
val pp_print_with_parens : (formatter -> 'a -> unit) -> formatter -> 'a -> unit

(** This module implements minimal parenthesization *)
module type Minimal_sig = sig

  module Prec : Pars.Intf.Prec  (* The functor's argument: precedences *)

  (** Associativity *)
  type assoc = Left | Non | Right

  (** Operators are an abstract representation of the operator
      component of a minimally parenthesized expression *)
  type op =
    | Infix of assoc * exp * exp
    | Prefix of exp
    | Postfix of exp

  (** The expression "view" contains enough information to produce a
      minimal parenthesization. Both [Big] and [Atm] are "atoms", but
      [Big] atoms are always parenthesized when they are operands of
      an operator. *)
  and exp =
    | Atm of fmt
    | Big of fmt
    | Op of string * fmt * Prec.prec * op

  and fmt = formatter -> unit

  (** Parenthesize the given [exp] on the given [formatter]. *)
  val pp_print_minimal : formatter -> exp -> unit
end

module Minimal (Prec: Pars.Intf.Prec):
    Minimal_sig with module Prec = Prec
