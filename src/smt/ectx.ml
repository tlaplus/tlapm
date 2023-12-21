(* Extended context.

Authors: Hernán Vanzetto <hernan.vanzetto@inria.fr>

Copyright (C) 2014-2014  INRIA and Microsoft Corporation
*)
open Ext
open Property
open Expr.T

module Dq = Deque
module T = Typ_t

(** Type [t] as seen in [Expr.Fmt].
  ['a Expr.Visit.scx] = ['a * Deque.dq] is used by the visitors [Expr.Visit.map] and [Expr.Visit.iter].
  [int Ctx.ctx] is the context where the proper identifiers are kept.
*)
type t = hyp Deque.dq * int Ctx.ctx

let dot = Dq.empty, Ctx.dot

let length (dx,cx) =
  let l1 = Dq.size dx in
  let l2 = Ctx.length cx in
  assert (l1 = l2) ;
  l1

(** [bump] is used to add a [Fact] (meaning no identifier) to the context *)
let bump (dx,cx) =
  (* let dx = Expr.Visit.adj dx (Fresh ("dummy" %% [], Shape_expr, Constant, Unbounded) %% []) in *)
  let dx = Dq.snoc dx (Fresh ("dummy" %% [], Shape_expr, Constant, Unbounded) %% []) in
  (* let dx = Dq.snoc dx ("",false,None) in *)
  let cx = Ctx.bump cx in
  (dx,cx)

let update_defn_name id defn =
  match defn.core with
  | Recursive (h,s) -> Recursive (id @@ h,s) @@ defn
  | Operator (h,ex) -> Operator (id @@ h,ex) @@ defn
  | Instance (h,i) -> Instance (id @@ h,i) @@ defn
  | Bpragma (h,ex,ls) -> Bpragma (id @@ h,ex,ls) @@ defn

let update_hyp_name id h =
  match h.core with
  | Fresh (nm, s, k, hdom) -> Fresh (id @@ nm, s, k, hdom) @@ h
  | Flex nm -> Flex (id @@ nm) @@ h
  | Defn (def, w, v, e) ->
      Defn (update_defn_name id def,w,v,e) @@ h
  | Fact _ ->
      (* Errors.bug "Backend.SMT.Ectx.adj: Fact not expected" *)
      h

let adj (dx,cx) h =
  let id = hyp_name h in
  let cx = Ctx.push cx id in
  let id = Tla_parser.pickle (Ctx.string_of_ident (fst (Ctx.top cx))) in      (** From [Isabelle]. Identifier "x" comes as "x_1", "x_2" if needed. *)
  let h = update_hyp_name id h in
  let dx = Dq.snoc dx h in
  ((dx,cx), (id,h))

let rec adjs ecx = function
  | [] -> (ecx, [])
  | h :: hs ->
      let ecx,vh = adj ecx h in
      let ecx,vhs = adjs ecx hs in
      (ecx, vh :: vhs)

(* Hack to recognize bounded vars by [Shape_op 0] in [is_bounded].
Normally it is [Shape_expr].
*)
let hack_bs hs = List.map begin fun h ->
  match h.core with
  | Fresh (v, s, k, d) -> Fresh (v, Shape_op 0, k, d) @@ h
  | _ -> h
  end hs

let is_bounded_hyp = function
  | Some {core = Fresh (_, Shape_op 0, _, Unbounded)} -> true
    (* Hack introduced by [hack_bs] *)
  | _ -> false

let is_bounded dx n =
  let h = Dq.nth ~backwards:true dx (n - 1) in
  is_bounded_hyp h

(** [adj_bs] is used for two different functions.
    [vss]
    [hs]
    *)
let adj_bs ecx bs =
  let hs = Expr.Visit.hyps_of_bounds_unditto bs |> hack_bs in
  let (dx,cx),vhs = adjs ecx hs in
  let vs,hs = List.split vhs in
  let vs = List.map (Smtcommons.turn_first_char true) vs in
  let ss = List.map begin fun h ->
    match Typ_t.optype h with
    | Some T.Int -> Axioms.SInt
    | Some (T.Ref (_,T.Int,_)) -> Axioms.SInt
    | Some T.Str -> Axioms.SStr
    | Some (T.Ref (_,T.Str,_)) -> Axioms.SStr
    | _ -> Axioms.U
    end hs in
  let vss = List.combine vs ss in
  (dx,cx), vss, hs

let tla_id (dx,cx) n =
  assert (n > 0 && n <= length (dx,cx)) ;
  Ctx.string_of_ident (fst (Ctx.index cx n))

let smt_id (dx,cx) n =
  let id = tla_id (dx,cx) n in
  Smtcommons.smt_pickle (is_bounded dx n) id

(** Reconstructs a [Ectx.t] context from scratch using hypotheses [hs].
    Add list of hyps [hs : hyp Dq.dq] to [cx : int Ctx.ctx] *)
let rec from_hyps (ecx:t) (hs:hyp Deque.dq) : t =
  match Dq.front hs with
  | None -> ecx
  | Some (h, hs) ->
      begin match h.core with
      | Fresh (nm, _, _, _)
      | Flex nm
      | Defn ({core = Operator (nm, _)
                    | Instance (nm, _)
                    | Bpragma (nm,_,_)
                    | Recursive (nm, _)}, _, _, _) ->
          let ecx,_ = adj ecx h in
          from_hyps ecx hs
      | Fact _ ->
          from_hyps (bump ecx) hs
      end
