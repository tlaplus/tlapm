(* Utilities for performing substitutions in module syntax graphs. *)
open Expr.Subst

open M_t


val app_modunits: sub -> modunit list -> sub * modunit list
val app_modunit: sub -> modunit -> sub * modunit
val app_mule: sub -> mule -> mule
