(*
 * reduce/nt_table.mli --- notypes encoding table
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

open Expr.T
open Type.T
open Util.Coll
open Deps

open R_commons

(** To modify the declarations and axioms of the 'No Types' (NT) encoding,
    you should add/remove constructors in the {!nt_node} datatype, specify
    names in the {!nt_get_id} function and dependencies in the {!nt_get_deps}
    function.  The set {!nt_base} specifies what declarations/axioms will
    always be treated.

    The function {!nt_axiomatize} relies on a generic implementation; it is
    synthesized from the data we just described.  See {!Util.Deps}.
*)


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
  (* Booleans *)
  | NT_BoolToU
  | NT_Boolean
  (* Strings *)
  | NT_Str
  | NT_StringAny
  | NT_StringToU
  | NT_String
  | NT_StringLit of string

(** Safe add: @raise Invalid_argument if already present *)
val add : nt_node -> nt_node Sm.t -> nt_node Sm.t
val union : nt_node Sm.t -> nt_node Sm.t -> nt_node Sm.t
val from_list : nt_node list -> nt_node Sm.t

val nt_base : nt_node Sm.t
val nt_get_id : nt_node -> string
val nt_get_deps : nt_node -> nt_node Sm.t

(** Each node corresponds to one or several hypotheses to add to a context.
    Usually it's one declaration and a few axioms.
*)
val nt_get_hyps : nt_node -> hyp Deque.dq

(** [nt_axiomatize ns hs] adds to [hs] all hypotheses required by nodes [ns],
    accouting for depending nodes.  [hs] represents a generic top context.
*)
val nt_axiomatize : nt_node Sm.t -> hyp Deque.dq -> hyp Deque.dq
