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
    {!N_data.get_deps}, they are added in the context.

    The layout of the new sequent follows this convention:
      NEW declarations, NEW axioms, original hyps' |- original goal'
*)

(* {3 Extended context} *)

(** Extended context; used to store symbols and axioms data in an
    intermediary form *)
type ecx

(** The initial context may contain some mandatory new declarations *)
val init_ecx : ecx


(* {3 Main} *)

(** Collect relevant symbols and axioms *)
val collect : solver:string -> ecx -> sequent -> ecx

(** Assemble a sequent with an extended context *)
val assemble : solver:string -> ecx -> sequent -> sequent

(** Combine collect and assemble
    @param solver the target backend.
*)
val main : solver:string -> sequent -> sequent
(** If a backend is given, the operators of TLA+ that correspond to builtins
    of that backend are untouched.
    Available backends:
      - SMT
*)

