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
  open Type.T
  open Util.Coll
  open Commons
  type nt_node =
    (* Set Theory *)
    | NT_U
    | NT_UAny
    | NT_Mem
    | NT_Subseteq
    | NT_Enum of int
    | NT_Union
    | NT_Power
    | NT_Cup
    | NT_Cap
    | NT_Setminus
    | NT_SetSt of string * ty_kind
    (*| NT_SetOf of string * ty_kind*)  (* TODO *)
    | NT_Boolean
    | NT_BoolToU
    | NT_String
    | NT_StringToU
    | NT_StringLit of string
  val add : nt_node -> nt_node Sm.t -> nt_node Sm.t
  val union : nt_node Sm.t -> nt_node Sm.t -> nt_node Sm.t
  val from_list : nt_node list -> nt_node Sm.t
  val nt_base : nt_node Sm.t
  val nt_get_id : nt_node -> string
  val nt_get_deps : nt_node -> nt_node Sm.t
  val nt_get_hyps : nt_node -> hyp Deque.dq
  val nt_axiomatize : nt_node Sm.t -> hyp Deque.dq -> hyp Deque.dq
end

module NtCollect : sig
  open Expr.T
  open Util.Coll
  val collect : sequent -> NtTable.nt_node Sm.t
end
