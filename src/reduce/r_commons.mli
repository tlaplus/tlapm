(*
 * reduce/commons.mli --- reduce utilities
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

open Expr.T
open Type.T


(** Add hypothesis at the top.  If the field @opq is filled, every [Opaque ops]
    in the sequent will be replaced by a variable bound to the new hypothesis.
*)
val add_hyp : hyp -> ?opq:string -> sequent -> sequent
