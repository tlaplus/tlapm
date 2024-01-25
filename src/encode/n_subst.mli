(*
 * encode/subst.ml --- substitutions
 *
 *
 * Copyright (C) 2022  INRIA and Microsoft Corporation
 *)

open Expr.T
open Expr.Subst

(** A modified version of substitution for the {!Encode} package *)
val subst : map
(** Substitutions are applied to SMT patterns.
    Applications to 0 arguments are normalized in such a way that annotations
    are no longer discarded.
    *)
