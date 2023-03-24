(*
 * encode/standardize.mli
 *
 *
 * Copyright (C) 2022  INRIA and Microsoft Corporation
 *)

open Expr.T
open Type.T

(** This module removes all builtins and other TLA+ primitives from
    expressions.  All primitives are replaced by constants or operators
    with special annotations on them.

    For instance, the arithmetic expression:
      [m + n]
    put in standard form becomes:
      [plus(m, n)]

    The new constants are opaque expressions with {!Smb.smb_prop} annotations
    on them.  Type annotations are interpreted to disambiguate expressions.
    For instance, the [plus] operator will be addition on [int] only if a [int]
    annotation was attached to [+].  If not, it will be uninterpreted addition.
    This module is intended to be used after {!Type.Reconstruct}.

    Using second-order applications, all primitives can be put in standard
    form.  For instance, set comprehension:
      [{ x \in s : p }]
    becomes:
      [setst(s, LAMBDA x : p)]

    The primitives that are ignored by this module are: all boolean primitives
    (in the liberal interpretation, they will always be interpreted in the
    traditional way); temporal logic operators; builtins Unprimable and
    Irregular.
*)


(* {3 Main} *)

val main : sequent -> sequent

