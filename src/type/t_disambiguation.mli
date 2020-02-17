(*
 * type/disambiguation.mli --- sort expressions
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

(** This module implements a disambiguation on sequents, which is close to
    type reconstruction but for basic sorts only.  In the result sequent, every
    bound variable has a sort annotation; every declared operator has a kind
    annotation (see {!Type.T}).  Moreover, for overloaded operators, a
    particular version is decided.

    This algorithm is intended to be called before any encoding to a multi-
    sorted language, like SMT-LIB.

    Sorts:
        Can be [U] (the "universal" or "unknown" sort---its domain is the
        universe of sets), [bool] (formulas), and primitive sorts [int],
        [real], [string].

        Casts from any sort [s] to [U] may be inserted where necessary.  When
        an operator is overloaded (e.g. "+" can be for integers, reals, or
        sets), a particular version is selected.  When a boolean is expected,
        the formula is arranged.

    Kinds:
        May be constant, first-order, or second-order.

    Operators:
        All arithmetic operators are either specialized on int or real (when
        possible), or kept as is.  If an arithmetic operator is not changed,
        then it is to be interpreted as an operator defined in [U].
*)


(* {3 Symbols} *)

val cast_nm : T_t.ty_atom -> T_t.ty_atom -> string

val z_plus      : string
val z_minus     : string
val z_uminus    : string
val z_times     : string
val z_quotient  : string
val z_remainder : string
val z_exp       : string
val z_lteq      : string
val z_lt        : string
val z_gteq      : string
val z_gt        : string
val z_range     : string

val r_plus      : string
val r_minus     : string
val r_uminus    : string
val r_times     : string
val r_ratio     : string
val r_quotient  : string
val r_remainder : string
val r_exp       : string
val r_lteq      : string
val r_lt        : string
val r_gteq      : string
val r_gt        : string
val r_range     : string

val u_any : string
val z_any : string
val r_any : string
val s_any : string


(* {3 Main} *)

val min_reconstruct : Expr.T.sequent -> Expr.T.sequent

