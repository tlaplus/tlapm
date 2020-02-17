(*
 * Copyright (C) 2011  INRIA and Microsoft Corporation
 *)

(* Packaging module for the modules that implement PO transformations *)

module Commons : sig
  open Expr.T
  val add_hyp : hyp -> ?opq:string -> sequent -> sequent
end

module NtTable : sig
  open Expr.T
  open Util.Coll
  type nt_node =
    | NT_U
    | NT_Mem
    | NT_Empty
    | NT_Enum of int
    | NT_SetSt of int * string
    (* TODO *)
  val nt_base : nt_node Sm.t
  val nt_get_id : nt_node -> string
  val nt_get_deps : nt_node -> nt_node Sm.t
  val nt_axiomatize : nt_node Sm.t -> sequent -> sequent
end

module NtCollect : sig
  open Expr.T
  open Util.Coll
  val collect : sequent -> NtTable.nt_node Sm.t
end
