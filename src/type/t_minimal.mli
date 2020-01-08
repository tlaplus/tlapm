(*
 * type/minimal.mli --- minimal typing
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

(** This module implements a "minimal typing" reconstruction on POs.
    Minimal typing assigns to each expression one of the following basic sorts:
      - [bool] for formulas;
      - [set] for most non-formulas expressions;
      - [int] for unambiguous integer expressions like integer literals;
      - [string] for string literals;
      - a few other "basic" sorts.

    Even for encodings that do not require sophisticated type reconstruction,
    these basic types may be useful, even necessary. The algorithm works by
    inserting type coercions (or "casts") where necessary. One important case
    is coercions from/to the [bool] type:
      - Coercions from [bool] to [set] are sound because TRUE and FALSE are
        also values in the universe of set theory;
      - Coercions from [set] to [bool] are sound, they are the source of the
        so-called liberal interpretation of TLA+.

    Allowed coercions are (here "T1 <: T2" means that casting from T1 to T2
    is allowed):
      - T <: set      for all T
      - T <: bool     for all T
    Coercions are inserted as opaques operators.
*)

val min_reconstruct : Expr.T.sequent -> Expr.T.sequent

