(*
 * smtlib/fmt.ml -- pretty-printing
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

open S_t

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

