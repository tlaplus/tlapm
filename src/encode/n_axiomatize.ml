(*
 * encode/axiomatize.ml --- add axioms in a sequent
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

open Ext
open Property
open Expr.T

open N_table

module Sm = Util.Coll.Sm


(* {3 Helpers} *)

let error ?at mssg =
  Errors.bug ?at ("Encode.Axiomatize: " ^ mssg)


(* {3 Contexts} *)

(** Extended context type
    Set of new symbols with axioms attached.  The index of a symbol is always
    its name (obtained by {!get_name}).
    Axioms are expressions in standard form that may only reference the
    operators in the [etx] object, using opaque expressions.
*)
type etx = data Sm.t
and data = smb * expr list

let init_etx = Sm.empty

let mem s etx = Sm.mem s etx

let get_smb s etx = fst (Sm.find s etx)

let get_axms s etx = snd (Sm.find s etx)

let map_etx f etx =
  Sm.map begin fun (smb, es) ->
    let es = List.map (fun e -> f smb e) es in
    (smb, es)
  end etx

(* NOTE Important function! *)
(* Add symbol to extended context, along with all depending symbols and axioms
 * NOTE If a symbol is encountered, but a different symbol with the same name
 * was already treated, the new one will be ignored. *)
let add_smb smb etx =
  let rec spin (acc : etx) (ws : smb Sm.t) =
    if Sm.is_empty ws then
      (* Done *)
      acc
    else
      let k, smb = Sm.choose ws in
      if Sm.mem k acc then
        (* Smb already treated; skip *)
        let ws = Sm.remove k ws in
        spin acc ws
      else
        (* New smb; add it to acc with axioms;
         * add symbol dependencies to ws; continue *)
        let deps, axms =
          match get_defn smb with
          | None -> (Sm.empty, [])
          | Some df -> begin
            match smbtable df with
            | None -> (Sm.empty, [])
            | Some (deps, axms) ->
                let deps =
                  List.fold_left begin fun deps smb ->
                    let smb = std_smb smb in
                    Sm.add (get_name smb) smb deps
                  end Sm.empty deps
                in
                (deps, axms)
          end
        in
        let ws =
          Sm.union (fun _ _ smb -> Some smb) deps ws |>
          Sm.remove k (* redundant with skip phase *)
        in
        let acc =
          Sm.add k (smb, axms) acc
        in
        spin acc ws
  in

  let init = Sm.singleton (get_name smb) smb in
  spin etx init


(* {3 Collection} *)

let collect_visitor = object (self : 'self)
  inherit [unit, etx] Expr.Visit.fold as super

  method expr scx etx oe =
    match oe.core with
    | Opaque _ when has_smb oe ->
        let smb = get oe smb_prop in
        add_smb smb etx

    | _ -> super#expr scx etx oe

  method hyp scx etx h =
    match h.core with
    | Defn (_, _, Hidden, _)
    | Fact (_, Hidden, _) ->
        let scx = Expr.Visit.adj scx h in
        (scx, etx)
    | _ ->
        super#hyp scx etx h
end

let collect sq =
  let scx = ((), Deque.empty) in
  let etx = init_etx in
  snd (collect_visitor#sequent scx etx sq)


(* {3 Assembly} *)

let axm_ptrs_prop = make "Encode.Axiomatization.axm_ptrs_prop"

let mk_decl smb =
  let v = get_name smb %% [] in
  let sch = get_sch smb in
  let v = assign v Type.T.Props.tsch_prop sch in
  let shp = Shape_op 0 in (* special *)
  Fresh (v, shp, Constant, Unbounded) %% []

let mk_fact e =
  Fact (e, Visible, NotSet) %% []

(* FIXME remove *)
let is_arith_smb smb =
  match get_defn smb with
  | Some ( Plus | Uminus | Minus | Times | Lteq ) -> true
  | _ -> false

let is_arith_op e =
  match query e smb_prop with
  | Some smb -> is_arith_smb smb
  | None -> false

let assemble_visitor = object (self : 'self)
  inherit [unit] Expr.Visit.map as super

  method expr ((), hx as scx) oe =
    match oe.core with
    | Opaque _ when has_smb oe && not (is_arith_op oe) ->
        let smb = get oe smb_prop in
        let s = get_name smb in
        let is_fresh_s = fun h ->
          hyp_name h = s
        in
        begin try
        let n =
          match Deque.find ~backwards:true hx is_fresh_s with
          | Some (n, _) -> n
          | None ->
              let mssg = "cannot find symbol '"
                        ^ s ^ "' in context" in
              error ~at:oe mssg
        in
        let ix = 1 + n in
        remove (Ix ix @@ oe) smb_prop
        with _ -> oe end

        (* FIXME remove *)
    | Opaque _ when has_smb oe && is_arith_op oe ->
        let smb = get oe smb_prop in
        let tsch = get_sch smb in
        assign oe Type.T.Props.tsch_prop tsch

    | _ -> super#expr scx oe

  method hyp scx h =
    match h.core with
    | Defn (_, _, Hidden, _)
    | Fact (_, Hidden, _) ->
        let scx = Expr.Visit.adj scx h in
        (scx, h)
    | _ ->
        super#hyp scx h
end

let assemble etx sq =
  let top_hx =
    (* For each declaration, we want to attach pointers to the relevant axioms
     * that come next.  The trick is to build the context in two opposite
     * directions, one for declarations and the other for axioms:
     *
     *    .. <-- NEW declarations, NEW axioms --> ..
     *
     * That way, we don't insert new hypothesis in the middle of the already-
     * built context, and the process is accumulative. *)
    let new_decls, new_axms =
      Sm.fold begin fun _ (smb, axms) (new_decls, new_axms) ->
        if is_arith_smb smb then (* FIXME remove *)
          (new_decls, new_axms)
        else
          let decl = mk_decl smb in
          let ptrs = List.init (List.length axms) (fun i -> 1 + i + Deque.size new_decls + Deque.size new_axms) in
          let decl = assign decl axm_ptrs_prop ptrs in
          let new_decls = Deque.cons decl new_decls in
          let axms = List.map mk_fact axms in
          let new_axms = Deque.append_list new_axms axms in
          (new_decls, new_axms)
      end etx (Deque.empty, Deque.empty)
    in
    Deque.append new_decls new_axms
  in

  let sq = { sq with context = Deque.append top_hx sq.context } in
  let scx = ((), Deque.empty) in
  let _, sq = assemble_visitor#sequent scx sq in
  sq


(* {3 Main} *)

let main sq =
  let etx = collect sq in
  let enc e = N_direct.expr Ctx.dot e |> fst in (* FIXME encode sooner *)
  let etx = map_etx (fun _ -> enc) etx in
  let sq = assemble etx sq in
  sq

