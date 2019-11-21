(*
 * smtlib/axioms.mli -- axioms for untyped encoding
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

(** Repertory of axioms used in {!Smtlib.Direct}. Separated for clearer
    presentation, since they take a lot of lines.

    It is assumed the symbols used in individual axioms are declared first
    in the theory being built.

    Names ending in 'def' correspond to axioms that define a particular
    symbols. 'car' is for set constructs defined by extentionality. 'inj'
    is to declare some function injective. 'hom' is for operators defined
    by a homomorphic relation (typically with a builtin operator).
*)

open S_t

(** [no_intersect (sort1, cast1) (sort2, cast2)] states that all elements
    of the first sort are distinct of every element of the second sort.
*)
val no_intersect    : symbol * symbol -> symbol * symbol -> term

val set_ext         : term  (* Ignore? *)
val subset_def      : term
val enum_set_car    : int -> term
val power_set_car   : term
val union_set_car   : term
val inter_car       : term
val union_car       : term
val diff_car        : term

val empty_ext       : term

val bool_set_car    : term
val bool_cast_inj   : term

val string_set_car  : term
val string_distinct : string -> string -> term
val string_cast_inj : term

val int_set_car     : term
val nat_set_car     : term
val int_cast_inj    : term
val int_plus_hom    : term
val int_minus_hom   : term
val int_mult_hom    : term
val int_div_hom     : term
val int_mod_hom     : term
val int_le_hom      : term
val range_car       : term

val fun_ext         : term  (* Ignore? *)
val fun_set_car     : term
val fun_except_dom  : term
val fun_except_val  : term

val prod_set_car    : int -> term
val tuple_ext       : int -> term
val tuple_def       : int -> int -> term
val tuple_dom       : int -> term

val rec_set_car     : int -> term
val record_def      : int -> term
val record_dom      : int -> term

