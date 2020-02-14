(*
 * deps.mli --- Dependency graphs with actions
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

open Util.Coll

(** This module type can represent a dependency graph.  Each node has a label
    and contains an action.  The arrows represent dependencies.  The action of
    a node can only be performed after all the actions of the depending nodes
    are performed.

    When giving an implementation of a graph, make sure [get_id] gives a unique
    label to each node, that in the result map of [get_deps] the key of each
    node is equal to its label, and that there are no circular dependencies.
*)
module type Graph = sig
  type node   (* Abstract type of a node *)
  type s      (* Abstract type to act on *)

  val base : node Sm.t  (* Nodes automatically treated *)

  val get_id   : node -> string     (* Every node has a name *)
  val get_deps : node -> node Sm.t  (* Dependencies *)

  val get_ac   : node -> s -> s     (* Action of a node *)
end

(** The function [ac_deps ns s] will perform on [s] all the actions attached to
    the nodes [ns], and the nodes they depend on.  If a node [s1] depends on a
    node [s2], the action of [s2] is performed first.  An action will not be
    performed twice, even between different calls.  Nodes of the set [base] are
    necessarily treated at the first call to [ac_deps], as if every other node
    had an arrow to them.

    Watch out for circular dependencies, they will make [ac_deps] run forever!
*)
module Closure (G : Graph) : sig
  val ac_deps : G.node Sm.t -> G.s -> G.s
end
