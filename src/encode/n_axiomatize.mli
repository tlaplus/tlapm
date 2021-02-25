(*
 * encode/axiomatize.mli --- add axioms in a sequent
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

open Property
open Expr.T

open N_smb

(** This module implements Axiomatization, the process by which every
    `Opaque s` with a {!smb} attached is replaced by a reference (De Bruijn
    variable) to a NEW constant declaration.
    NOTE Opaques without a {!smb} are not affected.

    Additionally, if a {!smb} has dependencies and axioms implemented by
    {!smbtable}, they are added in the context.

    The layout of the new sequent follows this convention:
      NEW declarations, NEW axioms, original hyps |- original goal
*)

(* {3 Extended context} *)

(** Extended context; used to store symbols and axioms data in an
    intermediary form *)
type etx


(* {3 Main} *)

(** Collect relevant symbols and axioms *)
val collect : sequent -> etx

(** Assemble a sequent with an extended context; set {!decl_ptr_prop} *)
val assemble : etx -> sequent -> sequent

(** Combine collect and assemble *)
val main : sequent -> sequent

