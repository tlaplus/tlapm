(*
 * Copyright (C) 2011-2012  INRIA and Microsoft Corporation
 *)
open Expr.T

(****************************************************************************)
open Typ_t
open Typ_e
open Typ_c

(* val boolify: expr -> expr *)

(*
val cg:
    hyp list -> expr ->
        (Typ_e.t * Typ_c.t)
*)
(*
val solve:
    hyp list -> expr list ->
        expr list
*)

val type_construct: sequent -> sequent
