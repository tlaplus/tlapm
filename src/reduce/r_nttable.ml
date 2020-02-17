(*
 * reduce/nttable.ml --- notypes encoding table
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

open Expr.T
open Type.T
open Ext
open Deps
open Util.Coll


type nt_node =
  | NT_U
  (* Set Theory *)
  | NT_Mem
  | NT_Empty
  | NT_Enum of int
  | NT_SetSt of int * string
  (* TODO *)

let nt_get_id node =
  match node with
  | NT_U -> "nt_u"
  | NT_Mem -> "nt_mem"
  | NT_Empty -> "nt_empty"
  | NT_Enum n -> "nt_enum_" ^ string_of_int n
  | NT_SetSt (n, f) -> "nt_setst_" ^ string_of_int n ^ "_" ^ f

let nt_base = Sm.empty

let nt_get_deps_l node =
  match node with
  | NT_Empty | NT_Enum _ | NT_SetSt _ -> [ NT_Mem ]
  | _ -> []

let nt_get_deps node =
  List.fold_left begin fun sm node ->
    Sm.add (nt_get_id node) node sm
  end Sm.empty (nt_get_deps_l node)


module NT_Graph : Graph
  with type node = nt_node
   and type s = sequent = struct

  type node = nt_node
  type s = sequent

  let base = nt_base
  let get_id = nt_get_id
  let get_deps = nt_get_deps

  let get_ac _ sq = sq (* TODO *)
end

module NT_Axiomatize = Closure (NT_Graph)

let nt_axiomatize ns sq = NT_Axiomatize.ac_deps ns sq
