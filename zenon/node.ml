(*  Copyright 2004 INRIA  *)

open Expr;;
open Printf;;

type priority =
  | Prop
  | Arity
  | Arity_eq
  | Inst of expr
;;

type node = {
  nconc : expr list;
  nrule : Mlproof.rule;
  nprio : priority;
  ngoal : goalness;
  nbranches : expr list array;
};;

type node_item =
  | Node of node
  | Stop
;;

let rec xrelevant cur l accu =
  match cur, l with
  | [], h :: t -> xrelevant h t accu
  | (Node n :: t1), t -> xrelevant t1 t (n :: accu)
  | (Stop :: _), _ -> (List.rev accu, true)
  | [], [] -> (List.rev accu, false)
;;

let relevant l = xrelevant [] l [];;


(* first draft: use stacks for finite nodes, and a pseudo-FIFO
   for the instantiation nodes
   TODO: efficient FIFO
*)

type queue = {
  prop1 : node list;
  prop2 : node list;
  unary : node list;
  binary : node list;
  nary : node list;
  eq_front : node list;
  eq_back : node list;
  eq_count : int;
  inst_state : int;
  inst_size : (int * node Heap.t) list;
  inst_front : node list;
  inst_back : node list;
};;

let k_meta_mul = 5;;
let k_tau_div = 8;;

let use_goalness = true;;
let ist_small = 16;;         (* ist_small must be even *)
let ist_old = 2;;
let ist_max = ist_small + ist_old;;
let num_eq = 10;;

let compare_nodes n1 n2 =
  let get_size n =
    match n.nrule with
    | Mlproof.All (_, e) | Mlproof.NotEx (_, e) ->
        size e + count_metas e * k_meta_mul + get_taus e / k_tau_div
    | _ -> assert false
  in
  get_size n1 - get_size n2
;;

let empty = {
  prop1 = [];
  prop2 = [];
  unary = [];
  binary = [];
  nary = [];
  eq_front = [];
  eq_back = [];
  eq_count = num_eq;
  inst_state = 0;
  inst_size = [];
  inst_front = [];
  inst_back = [];
};;

let insert_by_goalness l n =
  let gness = if use_goalness then n.ngoal else 0 in
  let h = try List.assoc gness l with Not_found -> Heap.empty compare_nodes in
  let nh = Heap.insert h n in
  let rec list_insert i e l =
    match l with
    | [] -> [(i, e)]
    | (j, _) :: t when j = i -> (i, e) :: t
    | (j, _) :: _ when j > i -> (i, e) :: l
    | h::t -> h :: (list_insert i e t)
  in
  list_insert gness nh l
;;

let rec can_instantiate m e =
  match e with
  | Evar _ -> true
  | Emeta (m1, _) -> not (List.exists (Expr.equal m) (get_metas m1))
  | Eapp (s, es, _) -> List.for_all (can_instantiate m) es
  | Enot (e1, _) -> can_instantiate m e1
  | Eand (e1, e2, _) | Eor (e1, e2, _) | Eimply (e1, e2, _)
  | Eequiv (e1, e2, _)
    -> can_instantiate m e1 && can_instantiate m e2
  | Etrue | Efalse -> true
  | Eall (v, t, e1, _) | Eex (v, t, e1, _) | Etau (v, t, e1, _)
  | Elam (v, t, e1, _)
    -> can_instantiate m e1
;;

let insert q n =
  match n.nprio with
  | Prop ->
     if Array.length n.nbranches < 2
     then {q with prop1 = n :: q.prop1}
     else {q with prop2 = n :: q.prop2}
  | Arity ->
      begin match Array.length n.nbranches with
      | 0 -> {q with prop1 = n::q.prop1}
      | 1 -> {q with unary = n::q.unary}
      | 2 -> {q with binary = n::q.binary}
      | _ -> {q with nary = n::q.nary}
      end
  | Arity_eq -> {q with eq_back = n::q.eq_back}
  | Inst _ ->
      begin match n.nrule with
      | Mlproof.All (m, e)
      | Mlproof.NotEx (Enot (m, _), e)
      when can_instantiate m e ->
       { q with
         inst_back = n::q.inst_back;
         inst_size = insert_by_goalness q.inst_size n;
       }
      | _ -> {q with inst_back = n::q.inst_back}
      end
;;

let remove_by_goalness ist l =
  let rec remove_at i l =
    match l with
    | [] -> None
    | (j, h) :: t when j < i ->
        begin match remove_at i t with
        | None -> None
        | Some (x, nl) -> Some (x, (j,h)::nl)
        end
    | (j, h) :: t ->
        begin match Heap.remove h with
        | None -> remove_at i t
        | Some (x, nh) -> Some (x, (j,nh)::t)
        end
  in
  if ist mod 2 = 0 then begin
    remove_at 0 l
  end else begin
    let better r1 r2 =
      match r1, r2 with
      | None, _ -> false
      | _, None -> true
      | Some n1, Some n2 -> compare_nodes n1 n2 < 0
    in
    let rec find_best i hd l =
      match l with
      | [] -> i
      | (j, h) :: t ->
          let hd2 = Heap.head h in
          if better hd2 hd
          then find_best j hd2 t
          else find_best i hd t
    in
    remove_at (find_best 0 None l) l
  end
;;

let rec is_empty l =
  match l with
  | [] -> true
  | (i, h) :: t -> Heap.is_empty h && is_empty t
;;

let rec remove_eq q =
  match q with
  | { eq_front = h :: t } -> Some (h, { q with eq_front = t })
  | { eq_back = _ :: _ } ->
     remove_eq { q with eq_front = List.rev q.eq_back; eq_back = [] }
  | _ -> None
;;

let rec remove_inst q =
  match q with
  | { inst_state = ist; inst_size = hpl } when ist < ist_small ->
      begin match remove_by_goalness ist hpl with
      | Some (x, l) ->
         Some (x, {q with inst_state = ist + 1; inst_size = l})
      | None -> remove_inst {q with inst_state = ist_small}
      end
  | { inst_state = ist; inst_front = h::t } ->
      Some (h, {q with inst_front = t; inst_state = (ist + 1) mod ist_max})
  | { inst_back = []; inst_size = hpl } ->
      if is_empty hpl then None
      else remove_inst {q with inst_state = 0}
  | { inst_back = l } ->
     remove_inst {q with inst_front = List.rev l; inst_back = []}
;;

let chain r1 r2 q =
  match r1 q with
  | None -> r2 q
  | x -> x
;;

let rec remove q =
  match q with
  | { prop1 = h::t } -> Some (h, {q with prop1 = t})
  | { prop2 = h::t } -> Some (h, {q with prop2 = t})
  | { unary = h::t } -> Some (h, {q with unary = t})
  | { binary = h::t } -> Some (h, {q with binary = t})
  | { nary = h::t } -> Some (h, {q with nary = t})
  | { eq_count = count } when count > 0 ->
     chain remove_eq remove_inst { q with eq_count = count - 1 }
  | _ -> chain remove_inst remove_eq { q with eq_count = num_eq }
;;

let rec last x l =
  match l with
  | [] -> x
  | h::t -> last h t
;;

let head q =
  match q with
  | { prop1 = h::t } -> Some h
  | { prop2 = h::t } -> Some h
  | { unary = h::t } -> Some h
  | { binary = h::t } -> Some h
  | { nary = h::t } -> Some h
  | { eq_front = h::t } -> Some h
  | { eq_back = h::t } -> Some (last h t)
  | { inst_front = h::t} -> Some h
  | { inst_back = h::t} -> Some (last h t)
  | _ -> None
;;

let size q =
  sprintf "p1:%d p2:%d a1:%d a2:%d an:%d eq:%d-%d inst:%d-%d"
          (List.length q.prop1) (List.length q.prop2)
          (List.length q.unary) (List.length q.binary)
          (List.length q.nary) (List.length q.eq_front) (List.length q.eq_back)
          (List.length q.inst_front)
          (List.length q.inst_back)
;;
