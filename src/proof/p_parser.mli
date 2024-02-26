(*
 * concept.mli --- conceptualizing
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

type supp = Emit | Suppress

val qed_loc_prop : Loc.locus Property.pfuncs
(** Represents the location of the QED step, excluding its proof. *)

val usebody : P_t.usable Tla_parser.lprs
val proof : P_t.proof Tla_parser.lprs
val suppress : supp Tla_parser.lprs
