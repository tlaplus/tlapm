(* Copyright (C) 2011-2012  INRIA and Microsoft Corporation *)
open Expr.T


val cg:
    sequent -> sequent * Typ_e.t * Typ_c.t
(*
val cg:
    Typ_c.cg_mode -> Typ_e.t ->
    Typ_t.t -> hyp list -> expr ->
        expr * Typ_c.t
*)
