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

(* Versions that are collected after the last prover launch or client
   asks for diagnostics. We store some limited number of versions here,
   just to cope with async events from the client. *)
type tv =
  | TV of {
      text : string; (* Contents if the file at the specific version. *)
      version : int;
    }

(* Actual state of the document. *)
type ta =
  | TA of {
      doc_vsn : tv;
      p_ref : int;
      nts : tlapm_notif list;
      obs : tlapm_obligation OblMap.t;
    }

type td =
  | TD of {
      pending : tv list; (* All the received but not yet processed versions. *)
      actual : ta option; (* Already processed version. *)
      last_p_ref : int; (* Counter for the proof runs. *)
    }

type tk = Lsp.Types.DocumentUri.t
type t = td DocMap.t
type proof_res = int * tlapm_obligation list * tlapm_notif list

let empty = DocMap.empty

(* Just record the text. It will be processed later, when a prover
   command or diagnostics query is issued by the client. *)
let add docs uri vsn txt =
  let rev = TV { text = txt; version = vsn } in
  let drop_unused =
    List.filter (fun (TV pv) -> pv.version < vsn - keep_vsn_count)
  in
  let upd = function
    | None -> Some (TD { pending = [ rev ]; actual = None; last_p_ref = 0 })
    | Some (TD d) -> Some (TD { d with pending = rev :: drop_unused d.pending })
  in
  DocMap.update uri upd docs

let rem docs uri = DocMap.remove uri docs

let latest_vsn docs uri =
  match DocMap.find_opt uri docs with
  | None -> None
  | Some (TD { actual; pending = []; _ }) -> (
      match actual with
      | Some (TA { doc_vsn; _ }) ->
          let (TV doc_vsn) = doc_vsn in
          Some doc_vsn.version
      | None -> None)
  | Some (TD { pending = TV dv :: _; _ }) -> Some dv.version

let with_actual (TD doc) uri docs f act pending =
  let doc = TD { doc with pending; actual = Some act } in
  let TD doc, act, res = f doc act in
  let doc = TD { doc with actual = Some act } in
  let docs = DocMap.add uri doc docs in
  (docs, res)

(* Here we merge pending versions with the actual and then run
   the supplied function on the prepared doc info. *)
let with_doc_vsn docs uri vsn f =
  match DocMap.find_opt uri docs with
  | None -> (docs, None)
  | Some (TD ({ pending; actual; _ } as doc)) -> (
      let fresh_active (TV v) =
        TA { doc_vsn = TV v; p_ref = 0; obs = OblMap.empty; nts = [] }
      in
      let merge_into (TV v) (TA a) =
        let (TV a_doc_vsn) = a.doc_vsn in
        let diff_pos = TlapmRange.first_diff_pos a_doc_vsn.text v.text in
        let before_change loc = not (TlapmRange.before diff_pos loc) in
        let obs =
          OblMap.filter
            (fun _ (o : tlapm_obligation) -> before_change o.loc)
            a.obs
        in
        let nts =
          List.filter (fun (n : tlapm_notif) -> before_change n.loc) a.nts
        in
        TA { a with doc_vsn = TV v; obs; nts }
      in
      let rec drop_after_vsn = function
        | [] -> (None, [])
        | TV pv :: pvs ->
            if pv.version = vsn then (Some (TV pv), [])
            else
              let res, pvs = drop_after_vsn pvs in
              (res, TV pv :: pvs)
      in
      match actual with
      | Some (TA ({ doc_vsn = TV adv; _ } as actual)) when adv.version = vsn ->
          with_actual (TD doc) uri docs f (TA actual) pending
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
              with_actual (TD doc) uri docs f act pending))

let proof_res (TA a) =
  let obs_list = List.map snd (OblMap.to_list a.obs) in
  (a.p_ref, obs_list, a.nts)

(* Push specific version to the actual, increase the proof_rec and clear the notifications. *)
let prepare_proof docs uri vsn : t * (int * string * proof_res) option =
  with_doc_vsn docs uri vsn @@ fun (TD doc') (TA act') ->
  let next_p_ref = doc'.last_p_ref + 1 in
  let doc = TD { doc' with last_p_ref = next_p_ref } in
  let act = TA { act' with p_ref = next_p_ref; nts = [] } in
  let (TV doc_vsn') = act'.doc_vsn in
  (doc, act, Some (next_p_ref, doc_vsn'.text, proof_res act))

let add_obl docs uri vsn p_ref (obl : tlapm_obligation) =
  with_doc_vsn docs uri vsn @@ fun (TD doc') (TA act') ->
  if act'.p_ref = p_ref then
    let drop_older_intersecting (o_pr, _o_id) (o : tlapm_obligation) =
      o_pr = p_ref || not (TlapmRange.intersects obl.loc o.loc)
    in
    let obs = OblMap.add (p_ref, obl.id) obl act'.obs in
    let obs = OblMap.filter drop_older_intersecting obs in
    let act = TA { act' with obs } in
    (TD doc', act, Some (proof_res act))
  else (TD doc', TA act', None)

let add_notif docs uri vsn p_ref notif =
  with_doc_vsn docs uri vsn @@ fun (TD doc') (TA act') ->
  if act'.p_ref = p_ref then
    let nts = notif :: act'.nts in
    let act = TA { act' with nts; obs = OblMap.empty } in
    (TD doc', act, Some (proof_res act))
  else (TD doc', TA act', None)

let get_proof_res docs uri vsn =
  with_doc_vsn docs uri vsn @@ fun doc act -> (doc, act, Some (proof_res act))

let get_proof_res_latest docs uri =
  match latest_vsn docs uri with
  | None -> (docs, None, None)
  | Some latest_vsn ->
      let docs, res = get_proof_res docs uri latest_vsn in
      (docs, Some latest_vsn, res)
