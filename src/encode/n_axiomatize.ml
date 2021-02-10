(*
 * encode/axiomatize.ml --- add axioms in a sequent
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

open Ext
open Property
open Expr.T

open N_smb
open N_data


(* {3 Contexts} *)

type etx = s * SmbSet.t * expr Deque.dq

let init_etx = (init, SmbSet.empty, Deque.empty)


(* {3 Helpers} *)

let error ?at mssg =
  let mssg = "Encode.Axiomatize: " ^ mssg in
  Errors.bug ?at mssg


(* {3 Collection} *)

(* NOTE Important function
 * Add symbol to extended context, along with all depending
 * symbols and axioms *)
let add_smb smb (s, smbs, facts) =
  let rec more s acc_smbs acc_facts work_smbs =
    try
      let smb = SmbSet.choose work_smbs in
      if SmbSet.mem smb acc_smbs then
        let work_smbs = SmbSet.remove smb work_smbs in
        more s acc_smbs acc_facts work_smbs
      else
        let s, data = get_data s (get_defn smb) in
        let s, deps = List.fold_left begin fun (s, deps) tla_smb ->
          let s, smb = mk_smb s tla_smb in
          (s, smb :: deps)
        end (s, []) data.dat_deps in
        let axms = List.map get_axm data.dat_axms in
        let acc_smbs = SmbSet.add smb acc_smbs in
        let acc_facts = List.fold_left Deque.snoc acc_facts axms in
        let work_smbs = SmbSet.remove smb work_smbs in
        let work_smbs = List.fold_right SmbSet.add deps work_smbs in
        more s acc_smbs acc_facts work_smbs
    with Not_found ->
      (s, acc_smbs, acc_facts)
  in
  more s smbs facts (SmbSet.singleton smb)

let collect_visitor = object (self : 'self)
  inherit [unit, etx] Expr.Visit.fold as super

  method expr scx ecx oe =
    match oe.core with
    | Opaque _ when has oe smb_prop ->
        let smb = get oe smb_prop in
        add_smb smb ecx

    | _ -> super#expr scx ecx oe

  method hyp scx ecx h =
    match h.core with
    | Defn (_, _, Hidden, _)
    | Fact (_, Hidden, _) ->
        let scx = Expr.Visit.adj scx h in
        (scx, ecx)
    | _ ->
        super#hyp scx ecx h
end

let collect sq =
  let scx = ((), Deque.empty) in
  let ecx = init_etx in
  snd (collect_visitor#sequent scx ecx sq)


(* {3 Assembly} *)

let mk_decl smb =
  let v = get_name smb %% [] in
  let ty2 = get_ty2 smb in
  let v = assign v Type.T.Props.ty2_prop ty2 in
  let shp = Shape_op 0 in (* special *)
  Fresh (v, shp, Constant, Unbounded) %% []

let mk_fact e =
  Fact (e, Visible, NotSet) %% []

let assemble_visitor decls = object (self : 'self)
  inherit [unit] Expr.Visit.map as super

  method expr ((), hx as scx) oe =
    match oe.core with
    | Opaque _ when has oe smb_prop ->
        let smb = get oe smb_prop in
        let n =
          match Deque.find ~backwards:true decls (equal_smb smb) with
          | Some (n, _) -> n
          | None ->
              let mssg = "cannot find symbol '"
                        ^ get_name smb ^ "' in context" in
              error ~at:oe mssg
        in
        let ix = 1 + Deque.size hx + n in
        remove (Ix ix @@ oe) smb_prop

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

let assemble (_, decls, axms) sq =
  let decls =
    SmbSet.elements decls
    |> Deque.of_list
  in
  let scx = ((), Deque.empty) in
  let sq = { sq with context =
    Deque.append (Deque.map (fun _ -> mk_fact) axms) sq.context
  } in
  let _, sq = (assemble_visitor decls)#sequent scx sq in
  { sq with context =
      Deque.append (Deque.map (fun _ -> mk_decl) decls) sq.context
  }


(* {3 Main} *)

let main sq =
  let ecx = collect sq in
  let sq = assemble ecx sq in
  sq

