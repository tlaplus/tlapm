(*
 * Copyright (C) 2011  INRIA and Microsoft Corporation
 *)

(* Packaging module for the modules that implement PO transformations *)

module Commons : sig
  open Expr.T
  val add_hyp : hyp -> ?opq:string -> sequent -> sequent
end

