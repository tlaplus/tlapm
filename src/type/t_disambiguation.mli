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
val any_nm : T_t.ty_atom -> string

val int_special_prop : unit Property.pfuncs
val real_special_prop : unit Property.pfuncs
val cast_special_prop : (T_t.ty_atom * T_t.ty_atom) Property.pfuncs
val any_special_prop : T_t.ty_atom Property.pfuncs


(* {3 Main} *)

val min_reconstruct : Expr.T.sequent -> Expr.T.sequent

