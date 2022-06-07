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
open N_axioms
open N_table


(* {3 Contexts} *)

module TlaAxmSet = Set.Make (struct
  type t = tla_axm
  let compare = Pervasives.compare
end)

type ecx = s * SmbSet.t * TlaAxmSet.t

let pre_init_ecx =
  let init_smbs =
    [] |>
    List.map mk_smb |>
    SmbSet.of_list
  in
  (init, init_smbs, TlaAxmSet.empty)


(* {3 Helpers} *)

let error ?at mssg =
  let mssg = "Encode.Axiomatize: " ^ mssg in
  (*Errors.bug ?at mssg*)
  failwith mssg

(* Native symbols do not lead to a declaration, they are translated
 * as builtins of the backends *)
let is_native ~solver smb =
  begin match solver with
  | "SMT" | "Z3" | "CVC4" | "veriT" ->
      begin match get_defn smb with
      | TIntLit _
      | TIntPlus
      | TIntUminus
      | TIntMinus
      | TIntTimes
      | TIntQuotient
      | TIntRemainder
      | TIntLteq
      | TIntLt
      | TIntGteq
      | TIntGt
      | TFSCard _
      | TFSMem _
      | TFSSubseteq _
      | TFSEmpty _
      | TFSSingleton _
      | TFSAdd _
      | TFSSetEnum _
      | TFSCup _
      | TFSCap _
      | TFSSetminus _ -> true
      | _ -> false
      end
  | _ -> false
  end


(* {3 Collection} *)

(* NOTE Important function
 * Add symbol to extended context, along with all depending
 * symbols and axioms *)
let add_smb ~solver smb ecx =
  let rec spin (s, acc_smbs, acc_facts as ecx) work_smbs =
    try
      let smb = SmbSet.choose work_smbs in
      if SmbSet.mem smb acc_smbs then
        let work_smbs = SmbSet.remove smb work_smbs in
        spin ecx work_smbs
      else
        let s, deps = get_deps ~solver (get_defn smb) s in
        let smb_deps = List.fold_left begin fun smbs tla_smb ->
          let smb = mk_smb tla_smb in
          smb :: smbs
        end [] deps.dat_deps in
        let acc_smbs = SmbSet.add smb acc_smbs in
        let acc_facts = List.fold_right TlaAxmSet.add deps.dat_axms acc_facts in
        let work_smbs = SmbSet.remove smb work_smbs in
        let work_smbs = List.fold_right SmbSet.add smb_deps work_smbs in
        spin (s, acc_smbs, acc_facts) work_smbs
    with Not_found ->
      ecx
  in
  spin ecx (SmbSet.singleton smb)

let init_ecx ~solver =
  begin
    if solver = "CVC4" && Params.debugging "fs" then
      (*[ TFSCard (TAtm TAIdv)
      ; TFSMem (TAtm TAIdv)
      ; TFSSubseteq (TAtm TAIdv)
      ; TFSEmpty (TAtm TAIdv)
      ; TFSSingleton (TAtm TAIdv)
      ; TFSAdd (TAtm TAIdv)
      ; TFSCup (TAtm TAIdv)
      ; TFSCap (TAtm TAIdv)
      ; TFSSetminus (TAtm TAIdv)
      ]*)
      []
    else if Params.debugging "ext" then
      [ SetEnum 0 ]
    else []
  end |>
  List.map mk_smb |>
  List.fold_left (fun ecx smb -> add_smb ~solver smb ecx) pre_init_ecx

let collect_visitor = object (self : 'self)
  inherit [string, ecx] Expr.Visit.fold as super

  method expr (solver, cx as scx) ecx oe =
    begin match oe.core with
    | Opaque _ when has oe smb_prop ->
        let smb = get oe smb_prop in
        add_smb ~solver smb ecx

    | _ -> super#expr scx ecx oe

    end |>
    fold_pats (fun es ecx -> List.fold_left (self#expr scx) ecx es) oe


  method hyp scx ecx h =
    match h.core with
    | Defn (_, _, Hidden, _)
    | Fact (_, Hidden, _) ->
        let scx = Expr.Visit.adj scx h in
        (scx, ecx)
    | _ ->
        super#hyp scx ecx h
end

let collect ~solver ecx sq =
  let scx = (solver, Deque.empty) in
  snd (collect_visitor#sequent scx ecx sq)


(* {3 Assembly} *)

let mk_decl smb =
  let v = get_name smb %% [] in
  let ty2 = get_ty2 smb in
  let v = assign v Type.T.Props.ty2_prop ty2 in
  let shp = Shape_op 0 in (* special *)
  let h = Fresh (v, shp, Constant, Unbounded) %% [] in
  assign h smb_prop smb

let mk_fact ~solver tla_axm =
  let e = get_axm ~solver tla_axm in
  let meta = { hkind = Axiom ; name = axm_desc tla_axm } in
  let e = assign e meta_prop meta in
  let h = Fact (e, Visible, NotSet) %% [] in
  (* The optional smb_prop annotation is used in Flattening
   * for detecting axiom instances *)
  let h = Option.fold (fun h -> assign h smb_prop) h (query e smb_prop) in
  h

let assemble_visitor = object (self : 'self)
  inherit [string] Expr.Visit.map as super

  method expr (solver, hx as scx) oe =
    begin match oe.core with
    | Opaque _ when has oe smb_prop && not (is_native solver (get oe smb_prop)) ->
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

    | _ -> super#expr scx oe

    end |>
    map_pats (List.map (self#expr scx))

  method hyp scx h =
    match h.core with
    | Defn (_, _, Hidden, _)
    | Fact (_, Hidden, _) ->
        let scx = Expr.Visit.adj scx h in
        (scx, h)
    | _ ->
        super#hyp scx h
end

let assemble ~solver (_, decls, axms) sq =
  let decls = SmbSet.filter (fun smb -> not (is_native ~solver smb)) decls in
  let decls = Deque.map (fun _ -> mk_decl) (SmbSet.elements decls |> Deque.of_list) in
  let axms = TlaAxmSet.fold (fun tla_axm dq -> Deque.snoc dq (mk_fact ~solver tla_axm)) axms Deque.empty in
  let top_hx = Deque.append decls axms in

  let sq = { sq with context = Deque.append top_hx sq.context } in
  let scx = (solver, Deque.empty) in
  let _, sq = assemble_visitor#sequent scx sq in
  sq


(* {3 Main} *)

let main ~solver sq =
  let ecx = init_ecx ~solver in
  let ecx = collect ~solver ecx sq in
  let sq = assemble ~solver ecx sq in
  sq

