(* cSpell:words printexc recursives submod anoninst *)

(* Max number of unprocessed/pending versions to keep. *)
let keep_vsn_count = 50

module OblRef = struct
  type t = int * int

  let compare (p_ref_a, obl_id_a) (p_ref_b, obl_id_b) =
    let p_ref_cmp = Stdlib.compare p_ref_a p_ref_b in
    if p_ref_cmp = 0 then Stdlib.compare obl_id_a obl_id_b else p_ref_cmp
end

module DocMap = Map.Make (Lsp.Types.DocumentUri)
module OblMap = Map.Make (OblRef)
open Tlapm_lsp_prover
open Tlapm_lsp_prover.ToolboxProtocol

(** Versions that are collected after the last prover launch or client
    asks for diagnostics. We store some limited number of versions here,
    just to cope with async events from the client. *)
module TV = struct
  type t = {
    text : string; (* Contents if the file at the specific version. *)
    version : int;
  }

  let make txt vsn = { text = txt; version = vsn }
end

(** Actual state of the document. *)
module TA = struct
  type t = {
    doc_vsn : TV.t;
    p_ref : int;
    mule : (Tlapm_lib.Module.T.mule, exn) result option;
    nts : tlapm_notif list;
    obs : tlapm_obligation OblMap.t;
  }

  let make tv =
    { doc_vsn = tv; p_ref = 0; mule = None; obs = OblMap.empty; nts = [] }
end

(** Represents a document identified by its uri. It can contain multiple versions and all the related info. *)
module TD = struct
  type t = {
    pending : TV.t list; (* All the received but not yet processed versions. *)
    actual : TA.t option; (* Already processed version. *)
    last_p_ref : int; (* Counter for the proof runs. *)
  }

  let make tv = { pending = [ tv ]; actual = None; last_p_ref = 0 }
end

type tk = Lsp.Types.DocumentUri.t
type t = TD.t DocMap.t
type proof_res = int * tlapm_obligation list * tlapm_notif list

let empty = DocMap.empty

(* Just record the text. It will be processed later, when a prover
   command or diagnostics query is issued by the client. *)
let add docs uri vsn txt =
  let rev = TV.make txt vsn in
  let drop_unused =
    List.filter (fun (pv : TV.t) -> pv.version < vsn - keep_vsn_count)
  in
  let upd = function
    | None -> Some (TD.make rev)
    | Some (d : TD.t) -> Some { d with pending = rev :: drop_unused d.pending }
  in
  DocMap.update uri upd docs

let rem docs uri = DocMap.remove uri docs

let latest_vsn docs uri =
  match DocMap.find_opt uri docs with
  | None -> None
  | Some TD.{ actual; pending = []; _ } -> (
      match actual with
      | Some { doc_vsn; _ } -> Some doc_vsn.version
      | None -> None)
  | Some TD.{ pending = dv :: _; _ } -> Some dv.version

let with_actual doc uri docs f act pending =
  let doc = TD.{ doc with pending; actual = Some act } in
  let doc, act, res = f doc act in
  let doc = TD.{ doc with actual = Some act } in
  let docs = DocMap.add uri doc docs in
  (docs, res)

(* Here we merge pending versions with the actual and then run
   the supplied function on the prepared doc info. *)
let with_doc_vsn docs uri vsn f =
  match DocMap.find_opt uri docs with
  | None -> (docs, None)
  | Some (TD.{ pending; actual; _ } as doc) -> (
      let fresh_active v = TA.make v in
      let merge_into (v : TV.t) (a : TA.t) =
        let diff_pos = TlapmRange.first_diff_pos a.doc_vsn.text v.text in
        let before_change loc = not (TlapmRange.before diff_pos loc) in
        let obs =
          OblMap.filter
            (fun _ (o : tlapm_obligation) -> before_change o.loc)
            a.obs
        in
        let nts =
          List.filter (fun (n : tlapm_notif) -> before_change n.loc) a.nts
        in
        { a with doc_vsn = v; obs; nts }
      in
      let rec drop_after_vsn = function
        | [] -> (None, [])
        | (pv : TV.t) :: pvs ->
            if pv.version = vsn then (Some pv, [])
            else
              let res, pvs = drop_after_vsn pvs in
              (res, pv :: pvs)
      in
      match actual with
      | Some ({ doc_vsn = adv; _ } as actual) when adv.version = vsn ->
          with_actual doc uri docs f actual pending
      | _ -> (
          let selected, pending = drop_after_vsn pending in
          match selected with
          | None -> (docs, None)
          | Some selected ->
              let act =
                match actual with
                | None -> fresh_active selected
                | Some act -> merge_into selected act
              in
              let act = { act with mule = None } in
              with_actual doc uri docs f act pending))

let analyze_mule (mule : Tlapm_lib.Module.T.mule) =
  let open Tlapm_lib in
  let mule_ = Property.unwrap mule in
  let _ =
    List.fold_left
      (fun acc u ->
        let open Tlapm_lib.Module.T in
        match Property.unwrap u with
        | Constants _ -> acc
        | Recursives _ -> acc
        | Variables _ -> acc
        | Definition _ -> acc
        | Axiom _ -> acc
        | Theorem (name, _b, _c, _d, _e, _f) ->
            (match name with
            | None -> Eio.traceln "-----------> TH.name=None"
            | Some n ->
                Eio.traceln "-----------> TH.name=%s" (Property.unwrap n));
            acc
        | Submod _ -> acc
        | Mutate _ -> acc
        | Anoninst _ -> acc)
      () mule_.body
  in
  ()

let try_parse_anyway uri (act : TA.t) =
  let v = act.doc_vsn in
  match
    (* TODO: Call the parser under a mutex. *)
    Tlapm_lib.module_of_string v.text (Lsp.Types.DocumentUri.to_path uri)
  with
  | mule ->
      Eio.traceln "-----------> Document parsed";
      analyze_mule mule;
      (* TODO: Fix it. *)
      { act with mule = Some (Ok mule) }
  | exception e ->
      (* TODO: Get the errors. *)
      Eio.traceln "-----------> Document parsing failed: %s"
        (Printexc.to_string e);
      { act with mule = Some (Error e) }

let try_parse uri (act : TA.t) =
  match act with
  | { mule = None; _ } -> try_parse_anyway uri act
  | { mule = Some _; _ } -> act

let proof_res (act : TA.t) =
  let obs_list = List.map snd (OblMap.to_list act.obs) in
  (act.p_ref, obs_list, act.nts)

(* Push specific version to the actual, increase the proof_rec and clear the notifications. *)
let prepare_proof docs uri vsn : t * (int * string * proof_res) option =
  with_doc_vsn docs uri vsn @@ fun (doc : TD.t) (act : TA.t) ->
  let act = try_parse uri act in
  match act.mule with
  | None | Some (Error _) -> (doc, act, None)
  | Some (Ok _) ->
      let next_p_ref = doc.last_p_ref + 1 in
      let doc = { doc with last_p_ref = next_p_ref } in
      let act = { act with p_ref = next_p_ref; nts = [] } in
      (doc, act, Some (next_p_ref, act.doc_vsn.text, proof_res act))

let add_obl docs uri vsn p_ref (obl : tlapm_obligation) =
  with_doc_vsn docs uri vsn @@ fun (doc : TD.t) (act : TA.t) ->
  if act.p_ref = p_ref then
    let drop_older_intersecting (o_pr, _o_id) (o : tlapm_obligation) =
      o_pr = p_ref || not (TlapmRange.intersects obl.loc o.loc)
    in
    let obs = OblMap.add (p_ref, obl.id) obl act.obs in
    let obs = OblMap.filter drop_older_intersecting obs in
    let act = { act with obs } in
    (doc, act, Some (proof_res act))
  else (doc, act, None)

let add_notif docs uri vsn p_ref notif =
  with_doc_vsn docs uri vsn @@ fun (doc : TD.t) (act : TA.t) ->
  if act.p_ref = p_ref then
    let nts = notif :: act.nts in
    let act = { act with nts; obs = OblMap.empty } in
    (doc, act, Some (proof_res act))
  else (doc, act, None)

let get_proof_res docs uri vsn =
  with_doc_vsn docs uri vsn @@ fun doc act ->
  let act = try_parse uri act in
  (doc, act, Some (proof_res act))

let get_proof_res_latest docs uri =
  match latest_vsn docs uri with
  | None -> (docs, None, None)
  | Some latest_vsn ->
      let docs, res = get_proof_res docs uri latest_vsn in
      (docs, Some latest_vsn, res)
