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
  let seen = ref Ss.empty
  let init () = seen := Ss.empty

  type action = G.s -> G.s

  let remove_seen ns =
    snd (Sm.partition begin fun id _ ->
      Ss.mem id !seen
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

  (* Return double-ended queue of actions.
   * Pre-condition: no loops in the graph
   * Post-condition:
   *   if n1 -> .. -> n2 in the graph, then
   *   (front) :: .. :: n1 :: .. :: n2 :: .. :: (rear) in the deque.
   *)
  let rec ac_deps_aux (dq: action Deque.dq) ns =
    try
      let id, n = Sm.choose ns in
      seen := Ss.add id !seen;  (* Prevent circularity *)
      let deps = remove_seen (G.get_deps n) in
      (* Necessary rec. call: dependencies must be resolved first *)
      let dq = ac_deps_aux dq deps in
      let dq = Deque.cons (G.get_ac n) dq in
      ac_deps_aux dq (remove_seen ns)
    with Not_found ->
      dq

  let ac_deps ns s =
    let ns = union ns G.base in
    let dq = ac_deps_aux Deque.empty (remove_seen ns) in
    Deque.fold_right (@@) dq s

end
