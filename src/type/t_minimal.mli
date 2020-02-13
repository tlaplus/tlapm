(*
 * type/minimal.mli --- minimal typing
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

(** This module implements a disambiguation on sequents, which is close to
    type reconstruction but for basic sorts only.  In the result sequent, every
    bound variable has a sort annotation; every declared operator has a kind
    annotation (see {!Type.T}).

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
*)

(** Opaque casts *)
val u_cast : T_t.ty_atom -> string

val min_reconstruct : Expr.T.sequent -> Expr.T.sequent

