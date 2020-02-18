(*
 * reduce/nt_table.ml --- notypes encoding table
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

open Ext
open Expr.T
open Type.T
open Deps
open Util.Coll
open Property

open R_commons


(* {3 General} *)

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
  (* TODO functions, arith, tuples, sequences, etc. *)

let nt_get_id node =
  match node with
  | NT_U -> "nt_u"
  | NT_UAny -> "nt_uany"
  | NT_Mem -> "nt_mem"
  | NT_Subseteq -> "nt_subseteq"
  | NT_Enum n -> "nt_enum_" ^ string_of_int n
  | NT_Union -> "nt_union"
  | NT_Power -> "nt_power"
  | NT_Cup -> "nt_cup"
  | NT_Cap -> "nt_cap"
  | NT_Setminus -> "nt_setminus"
  | NT_SetSt (s, _) -> "nt_setst_" ^ s
  | NT_Boolean -> "nt_boolean"
  | NT_BoolToU -> "nt_booltou"
  | NT_String -> "nt_string"
  | NT_StringToU -> "nt_stringtou"
  | NT_StringLit s -> "nt_stringlit_" ^ s

(* FIXME compile with >= 4.06.0 *)
let update id upd_f ns =
  if Sm.mem id ns then
    let n = Sm.find id ns in
    match upd_f (Some n) with
    | None -> Sm.remove id ns
    | Some n' -> Sm.add id n' ns
  else
    match upd_f None with
    | None -> Sm.remove id ns
    | Some n -> Sm.add id n ns

let add_update n = function
  | None -> Some n
  | Some n' when n = n' -> Some n'
  | Some n' -> invalid_arg ("Reduce.NtTable.add_update: \
                            duplicate node '" ^ (nt_get_id n) ^ "'")

let add n ns = update (nt_get_id n) (add_update n) ns

let union ns1 ns2 =
  Sm.merge begin fun id n1 n2 ->
    match n1, n2 with
    | None, None -> None
    | Some n, None | None, Some n -> Some n
    | Some n1, Some n2 ->
        if n1 = n2 then Some n1
        else invalid_arg ("Reduce.NtTable.union: \
                          duplicate nodes '" ^ id ^ "'")
  end ns1 ns2

let from_list ns =
  List.fold_right add ns Sm.empty


(* {3 NT Specification} *)

let nt_base = from_list [ NT_U ; NT_UAny ; NT_Mem ]

let nt_get_deps_l node =
  match node with
  | NT_U -> []
  | NT_UAny -> [ NT_U ]
  | NT_Mem -> [ NT_U ]
  | NT_Subseteq -> [ NT_U ; NT_Mem ]
  | NT_Enum _ -> [ NT_U ; NT_Mem ]
  | NT_Union -> [ NT_U ; NT_Mem ]
  | NT_Power -> [ NT_U ; NT_Mem ]
  | NT_Cup -> [ NT_U ; NT_Mem ]
  | NT_Cap -> [ NT_U ; NT_Mem ]
  | NT_Setminus -> [ NT_U ; NT_Mem ]
  | NT_SetSt _ -> [ NT_U ; NT_Mem ]
  | NT_BoolToU -> [ NT_U ; NT_Mem ]
  | NT_Boolean -> [ NT_U ; NT_Mem ; NT_BoolToU ]
  | NT_StringToU -> [ NT_U ; NT_Mem ]
  | NT_String -> [ NT_U ; NT_Mem ; NT_StringToU ]
  | NT_StringLit s -> [ NT_U ; NT_Mem ; NT_StringToU ; NT_String ]

let nt_get_deps node =
  List.fold_left begin fun sm node ->
    Sm.add (nt_get_id node) node sm
  end Sm.empty (nt_get_deps_l node)

let nt_get_hyps node =
  let hs =
    match node with
    | NT_U -> []
    | _ -> [] (* TODO *)
  in
  Deque.of_list hs


(* {3 Make Utilities} *)

module NT_Graph : Graph
  with type node = nt_node
   and type s = hyp Deque.dq =
struct
  type node = nt_node
  type s = hyp Deque.dq

  let base = nt_base
  let get_id = nt_get_id
  let get_deps = nt_get_deps

  let get_ac ns top =
    Deque.append (nt_get_hyps ns) top
end

module NT_Axiomatize = Closure (NT_Graph)

let nt_axiomatize ns top = NT_Axiomatize.ac_deps ns top
