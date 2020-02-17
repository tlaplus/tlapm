(*
 * reduce/nttable.mli --- notypes encoding table
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

open Expr.T
open Util.Coll
open Deps


(** A node represents one or more declarations/axioms.  They are representated
    abstractly here so that their dependencies are treated by a generic
    algorithm.  See {!Util.Deps}.
*)
type nt_node =
  | NT_U
  (* Set Theory *)
  | NT_Mem
  | NT_Empty
  | NT_Enum of int
  | NT_SetSt of int * string
  (* TODO *)

val nt_base : nt_node Sm.t
val nt_get_id : nt_node -> string
val nt_get_deps : nt_node -> nt_node Sm.t

(** [nt_axiomatize ns sq] adds all declarations and facts (axioms) required by
    [ns] in the context of [sq].
*)
val nt_axiomatize : nt_node Sm.t -> sequent -> sequent
