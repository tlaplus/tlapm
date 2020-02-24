(*
 * deps.ml --- Dependency graphs with actions
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

open Util.Coll

module type Graph = sig
  type node   (* Abstract type of a node *)
  type s      (* Abstract type to act on *)

  val base : node Sm.t  (* Nodes automatically treated *)

  val get_id   : node -> string     (* Every node has a name *)
  val get_deps : node -> node Sm.t  (* Dependencies *)

  val get_ac   : node -> s -> s     (* Action of a node *)
end

module Closure (G : Graph) = struct

  (* No node treated twice *)
  let treated = ref Ss.empty

  type action = G.s -> G.s

  let get_untreated ns =
    snd (Sm.partition begin fun id _ ->
      Ss.mem id !treated
    end ns)

  (* FIXME in standard library for >= 4.03.0 *)
  let union m1 m2 =
    Sm.merge begin fun id n1 n2 ->
      match n1, n2 with
      | None, None -> None
      | Some n, None | None, Some n -> Some n
      | Some n1, Some n2 ->
          if n1 = n2 then Some n2
          else
            invalid_arg ("Util.Deps.Closure.union: \
                          non unique label '" ^ id ^ "'")
    end m1 m2

  (* Explore graph recursively;
   * Don't traverse already treated nodes;
   * Stack actions, do all in the end. *)
  let rec ac_deps_aux (stack : action Deque.dq) ns s =
    try
      let id, n = Sm.choose ns in
      let deps = G.get_deps n in
      let more = get_untreated deps in
      let ns = union (Sm.remove id ns) more in
      let stack = Deque.snoc stack (G.get_ac n) in
      treated := Ss.add id !treated;
      ac_deps_aux stack ns s
    with Not_found ->
      Deque.fold_right (@@) stack s

  let ac_deps ns s =
    let ns = union ns G.base in
    let _, ns = Sm.partition begin fun id _ ->
      Ss.mem id !treated
    end ns in
    ac_deps_aux Deque.empty ns s

end
