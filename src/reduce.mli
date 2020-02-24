(*
 * Copyright (C) 2011  INRIA and Microsoft Corporation
 *)

(* Packaging module for the modules that implement PO transformations *)

module Commons : sig
  open Expr.T
  val add_hyp : hyp -> ?opq:string -> sequent -> sequent
end

module NtAxioms : sig
  open Expr.T
  open Type.T

  val usort_nm : string
  val stringsort_nm : string
  val uany_nm : string
  val stringany_nm : string
  val mem_nm : string
  val subseteq_nm : string
  val empty_nm : string
  val enum_nm : int -> string
  val union_nm : string
  val power_nm : string
  val cup_nm : string
  val cap_nm : string
  val setminus_nm : string
  val setst_nm : string -> ty_kind -> string
  (*val setof_nm : string -> ty_kind -> string*)
  val boolean_nm : string
  val booltou_nm : string
  val string_nm : string
  val stringtou_nm : string
  val stringlit_nm : string -> string
  val arrow_nm : string
  val fcn_nm : string -> ty_kind -> string
  val domain_nm : string
  val fcnapp_nm : string
  val fcnexcept_nm : string
  val zset_nm : string
  val nset_nm : string
  val rset_nm : string
  val plus_nm : string
  val uminus_nm : string
  val minus_nm : string
  val times_nm : string
  val ratio_nm : string
  val quotient_nm : string
  val remainder_nm : string
  val exp_nm : string
  val infinity_nm : string
  val lteq_nm : string
  val lt_nm : string
  val gteq_nm : string
  val gt_nm : string
  val range_nm : string

  val uany_decl : hyp
  val stringany_decl : hyp
  val mem_decl : hyp
  val subseteq_decl : hyp
  val empty_decl : hyp
  val enum_decl : int -> hyp
  val union_decl : hyp
  val power_decl : hyp
  val cup_decl : hyp
  val cap_decl : hyp
  val setminus_decl : hyp
  val setst_decl : string -> ty_kind -> hyp
  (*val setof_decl : string -> ty_kind -> hyp*)
  val boolean_decl : hyp
  val booltou_decl : hyp
  val string_decl : hyp
  val stringtou_decl : hyp
  val stringlit_decl : string -> hyp
end

module NtTable : sig
  open Expr.T
  open Type.T
  open Util.Coll
  open Commons
  type nt_node =
    (* Set Theory *)
    | NT_U
    | NT_Str
    | NT_UAny
    | NT_StringAny
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

module NtCook : sig
  open Expr.T
  open Type.T
  open Property
  val setst_nm : string -> string
  val setst_prop : ty_kind pfuncs
  val cook : sequent -> sequent
end

module NtCollect : sig
  open Expr.T
  open Util.Coll
  val collect : sequent -> NtTable.nt_node Sm.t
end
