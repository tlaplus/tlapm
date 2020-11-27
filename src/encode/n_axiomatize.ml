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


(* {3 Contexts} *)

type etx = SmbSet.t * expr Deque.dq

let init_etx = (SmbSet.empty, Deque.empty)


(* {3 Helpers} *)

let error ?at mssg =
  Errors.bug ?at ("Encode.Axiomatize: " ^ mssg)


(* {3 Collection} *)

(* NOTE Important function
 * Add symbol to extended context, along with all depending
 * symbols and axioms
 * NOTE Axioms left unencoded because all declarations must
 * be collected beforehand *)
let add_smb smb (smbs, facts) =
  let rec more acc_smbs acc_facts work_smbs =
    try
      let smb = SmbSet.choose work_smbs in
      if SmbSet.mem smb acc_smbs then
        let work_smbs = SmbSet.remove smb work_smbs in
        more acc_smbs acc_facts work_smbs
      else
        let deps, axms =
          match get_defn smb with
          | None -> ([], [])
          | Some defn -> begin
            match smbtable defn with
            | None -> ([], [])
            | Some (tla_smbs, axms) ->
                (List.map std_smb tla_smbs, axms)
          end
        in
        let acc_smbs = SmbSet.add smb acc_smbs in
        let acc_facts = List.fold_left Deque.snoc acc_facts axms in
        let work_smbs = SmbSet.remove smb work_smbs in
        let work_smbs = List.fold_right SmbSet.add deps work_smbs in
        more acc_smbs acc_facts work_smbs
    with Not_found ->
      (acc_smbs, acc_facts)
  in
  more smbs facts (SmbSet.singleton smb)

let collect_visitor = object (self : 'self)
  inherit [unit, etx] Expr.Visit.fold as super

  method expr scx ecx oe =
    match oe.core with
    | Opaque _ when has_smb oe ->
        let smb = get_smb oe in
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
  let nm = get_name smb %% [] in
  let sch = get_sch smb in
  let nm = assign nm Type.T.Props.tsch_prop sch in
  let shp = Shape_op 0 in (* special *)
  Fresh (nm, shp, Constant, Unbounded) %% []

let mk_fact e =
  Fact (e, Visible, NotSet) %% []

(* FIXME HACK *)
let is_arith_smb smb =
  match get_defn smb with
  | Some ( Plus | Uminus | Minus | Times | Lteq ) -> true
  | _ -> false

let is_arith_op e =
  match query e smb_prop with
  | Some smb -> is_arith_smb smb
  | None -> false

let assemble_visitor decls = object (self : 'self)
  inherit [unit] Expr.Visit.map as super

  method expr ((), hx as scx) oe =
    match oe.core with
    | Opaque _ when has_smb oe && not (is_arith_op oe) ->
        let smb = get_smb oe in
        let n =
          match Deque.find ~backwards:true decls ((=) smb) with
          | Some (n, _) -> n
          | None ->
              let mssg = "cannot find symbol '"
                        ^ get_name smb ^ "' in context" in
              error ~at:oe mssg
        in
        let ix = 1 + Deque.size hx + n in
        remove (Ix ix @@ oe) smb_prop

    | Opaque _ when has_smb oe && is_arith_op oe ->
        let smb = get_smb oe in
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

let assemble (decls, axms) sq =
  let decls =
    SmbSet.elements decls
    |> List.filter (fun smb -> not (is_arith_smb smb)) (* FIXME HACK *)
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
  let decls, axms = collect sq in
  let enc e = N_direct.expr Ctx.dot e |> fst in
  let axms = Deque.map (fun _ -> enc) axms in
  let sq = assemble (decls, axms) sq in
  sq

