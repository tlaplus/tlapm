(*
 * proof/subst.mli --- substitution in proofs
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

open Expr.Subst

open P_t

val app_proof : sub -> proof -> proof
val app_step : sub -> step -> sub * step
val app_inits : sub -> step list -> sub * step list
val app_usable : sub -> usable -> usable
