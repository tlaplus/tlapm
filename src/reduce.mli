(*
 * Copyright (C) 2011  INRIA and Microsoft Corporation
 *)

(* Packaging module for the modules that implement PO transformations *)

module NtAxioms : sig
  open Expr.T
  open Type.T

  (* {3 Logic} *)

  val choose_nm : string -> ty_kind -> string
  val choose_decl : string -> ty_kind -> hyp
  val critical_fact : string -> ty_kind -> expr -> hyp

  (* Set Theory *)
  val usort_nm : string
  val uany_nm : string
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
  val setof_nm : string -> int -> ty_kind -> string

  val uany_decl : hyp
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
  val setof_decl : string -> int -> ty_kind -> hyp

  val subseteq_fact : hyp
  val enum_fact : int -> hyp
  val union_fact : hyp
  val power_fact : hyp
  val cup_fact : hyp
  val cap_fact : hyp
  val setminus_fact : hyp
  val setst_fact : string -> ty_kind -> expr -> hyp
  val setof_fact : string -> int -> ty_kind -> expr -> hyp

  (* Booleans *)
  val boolean_nm : string
  val booltou_nm : string

  val boolean_decl : hyp
  val booltou_decl : hyp

  val boolean_fact : hyp

  (* Strings *)
  val stringsort_nm : string
  val stringany_nm : string
  val stringtou_nm : string
  val string_nm : string
  val stringlit_nm : string -> string

  val stringany_decl : hyp
  val stringtou_decl : hyp
  val string_decl : hyp
  val stringlit_decl : string -> hyp

  val string_fact : hyp
  val stringcast_fact : hyp
  val stringlit_distinct_fact : string -> string -> hyp

  (* Functions *)
  val arrow_nm : string
  val fcn_nm : string -> int -> ty_kind -> string
  val domain_nm : string
  val fcnapp_nm : string
  val fcnexcept_nm : string

  val arrow_decl : hyp
  val fcn_decl : string -> int -> ty_kind -> hyp
  val domain_decl : hyp
  val fcnapp_decl : hyp
  val fcnexcept_decl : hyp

  val funext_fact : hyp
  val arrow_fact : hyp
  val fcndom_fact : string -> int -> ty_kind -> hyp
  val fcnapp_fact : string -> int -> ty_kind -> expr -> hyp
  val excdom_fact : hyp
  val excapp_fact : hyp

  (* Arithmetic *)
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

  (* Tuples *)
  (* TODO *)

  (* Sequences *)
  (* TODO *)
end

module NtCook : sig
  open Expr.T
  open Type.T
  open Property
  type hyp_nm = string
  val choose_nm : ty_kind -> expr -> string
  val setst_nm : ty_kind -> expr -> string
  val setof_nm : int -> ty_kind -> expr -> string
  val fcn_nm : int -> ty_kind -> expr -> string
  val choose_special_prop : (hyp_nm option * ty_kind * expr) pfuncs
  val setst_special_prop : (hyp_nm option * ty_kind * expr) pfuncs
  val setof_special_prop : (hyp_nm option * int * ty_kind * expr) pfuncs
  val fcn_special_prop : (hyp_nm option * int * ty_kind * expr) pfuncs
  val cook : sequent -> sequent
end

module NtTable : sig
  open Expr.T
  open Type.T
  open Util.Coll
  type nt_node =
    (* Logic *)
    | NT_Choose of NtCook.hyp_nm option * string * ty_kind * expr
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
    | NT_SetSt of NtCook.hyp_nm option * string * ty_kind * expr
    | NT_SetOf of NtCook.hyp_nm option * string * int * ty_kind * expr
    (* Booleans *)
    | NT_BoolToU
    | NT_Boolean
    (* Strings *)
    | NT_Str
    | NT_StringAny
    | NT_StringToU
    | NT_String
    | NT_StringLit of string
    (* Functions *)
    | NT_Arrow
    | NT_Domain
    | NT_Fcnapp
    | NT_Fcn of NtCook.hyp_nm option * string * int * ty_kind * expr
    | NT_Except
  val add : nt_node -> nt_node Sm.t -> nt_node Sm.t
  val union : nt_node Sm.t -> nt_node Sm.t -> nt_node Sm.t
  val from_list : nt_node list -> nt_node Sm.t
  val nt_base : nt_node Sm.t
  val nt_get_id : nt_node -> string
  val nt_get_deps : nt_node -> nt_node Sm.t
  type state
  val nt_get_hyps : state -> nt_node -> state * hyp Deque.dq
  val nt_axiomatize : nt_node Sm.t -> sequent -> sequent
end

module NtCollect : sig
  open Expr.T
  open Util.Coll
  val collect : sequent -> NtTable.nt_node Sm.t
end
