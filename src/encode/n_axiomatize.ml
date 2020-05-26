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
open N_canon


(* {3 Contexts} *)

type etx = SmbSet.t * expr Deque.dq

let init_etx = (SmbSet.empty, Deque.empty)


(* {3 Helpers} *)

let error ?at mssg =
  Errors.bug ?at ("Encode.Axiomatize: " ^ mssg)


(* {3 Collection} *)

let axioms smb = [] (* TODO *)

let add_smb smb (smbs, facts as ecx) =
  if SmbSet.mem smb smbs then
    ecx
  else
    let smbs =
      SmbSet.add smb smbs
    in
    let facts =
      List.fold_left Deque.snoc facts (axioms smb)
    in
    (smbs, facts)

let collect_visitor = object (self : 'self)
  inherit [unit, etx] Expr.Visit.fold as super

  method expr scx ecx oe =
    match oe.core with
    | Opaque _ when has_smb oe ->
        let smb = get_smb oe in
        add_smb smb ecx

    | _ -> super#expr scx ecx oe
end

let collect sq =
  let scx = ((), Deque.empty) in
  let ecx = init_etx in
  snd (collect_visitor#sequent scx ecx sq)


(* {3 Assembly} *)

let mk_decl smb =
  let nm = Type.T.annot_kind (get_name smb %% []) (get_kind smb) in
  let shp = Shape_expr in (* NOTE shape should be irrelevant! *)
  Fresh (nm, shp, Constant, Unbounded) %% []

let mk_fact e =
  Fact (e, Visible, NotSet) %% []

let assemble_visitor decls laxms = object (self : 'self)
  inherit [unit] Expr.Visit.map as super

  method expr ((), hx as scx) oe =
    match oe.core with
    | Opaque _ when has_smb oe ->
        let smb = get_smb oe in
        let n =
          match Deque.find ~backwards:true decls ((=) smb) with
          | Some (n, _) -> n
          | None ->
              let mssg = "cannot find symbol '"
                        ^ get_name smb ^ "' in context" in
              error mssg
        in
        let ix = 1 + Deque.size hx + laxms + n in
        remove (Ix ix @@ oe) smb_prop

    | _ -> super#expr scx oe
end

let assemble (decls, axms) sq =
  let decls =
    SmbSet.elements decls
    |> Deque.of_list
  in
  let laxms = Deque.size axms in
  let scx = ((), Deque.empty) in
  let _, sq = (assemble_visitor decls laxms)#sequent scx sq in
  { sq with context =
      sq.context
      |> Deque.append (Deque.map (fun _ -> mk_fact) axms)
      |> Deque.append (Deque.map (fun _ -> mk_decl) decls)
  }


(* {3 Main} *)

let main sq =
  let ex = collect sq in
  let sq = assemble ex sq in
  sq

