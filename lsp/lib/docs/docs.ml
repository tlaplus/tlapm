open Util
open Prover.ToolboxProtocol
open Prover
module Proof_step = Proof_step
module Proof_status = Proof_status
module Doc_proof_res = Doc_proof_res

type tk = LspT.DocumentUri.t
type t = Doc.t DocMap.t

let empty = DocMap.empty

(* Just record the text. It will be processed later, when a prover
   command or diagnostics query is issued by the client. *)
let add docs uri vsn txt =
  let tv = Doc_vsn.make txt vsn in
  let upd = function
    | None -> Some (Doc.make uri tv)
    | Some (doc : Doc.t) -> Some (Doc.add doc tv)
  in
  DocMap.update uri upd docs

let rem docs uri = DocMap.remove uri docs

let latest_vsn docs uri =
  match DocMap.find_opt uri docs with
  | None -> None
  | Some doc -> Some (Doc.latest_vsn doc)

(* Here we merge pending versions with the actual and then run
   the supplied function on the prepared doc info. *)
let with_doc_vsn docs uri vsn f =
  match DocMap.find_opt uri docs with
  | None -> (docs, None)
  | Some doc -> (
      match Doc.set_actual_vsn doc vsn with
      | None -> (docs, None)
      | Some doc ->
          let doc, res = Doc.with_actual doc f in
          let docs = DocMap.add uri doc docs in
          (docs, res))

(* Push specific version to the actual, increase the proof_rec and clear the notifications. *)
let prepare_proof docs uri vsn range :
    t * (int * string * TlapmRange.t * Doc_proof_res.t) option =
  with_doc_vsn docs uri vsn @@ fun (doc : Doc.t) (act : Doc_actual.t) ->
  let next_doc, next_p_ref = Doc.next_p_ref doc in
  match Doc_actual.prepare_proof act next_p_ref with
  | None -> (doc, act, None)
  | Some act ->
      let p_range = Doc_actual.locate_proof_range act range in
      let res =
        (next_p_ref, Doc_actual.text act, p_range, Doc_actual.proof_res act)
      in
      (next_doc, act, Some res)

(* Calculate proof range by user selection. *)
let suggest_proof_range docs uri range : t * (int * TlapmRange.t) option =
  match latest_vsn docs uri with
  | None -> (docs, None)
  | Some vsn ->
      with_doc_vsn docs uri vsn @@ fun (doc : Doc.t) (act : Doc_actual.t) ->
      let p_range = Doc_actual.locate_proof_range act range in
      (doc, act, Some (vsn, p_range))

let add_obl docs uri vsn p_ref (obl : tlapm_obligation) =
  with_doc_vsn docs uri vsn @@ fun (doc : Doc.t) (act : Doc_actual.t) ->
  match Doc_actual.add_obl act p_ref obl with
  | None -> (doc, act, None)
  | Some act -> (doc, act, Some (Doc_actual.proof_res act))

let add_notif docs uri vsn p_ref notif =
  with_doc_vsn docs uri vsn @@ fun (doc : Doc.t) (act : Doc_actual.t) ->
  match Doc_actual.add_notif act p_ref notif with
  | None -> (doc, act, None)
  | Some act -> (doc, act, Some (Doc_actual.proof_res act))

let terminated docs uri vsn p_ref =
  with_doc_vsn docs uri vsn @@ fun (doc : Doc.t) (act : Doc_actual.t) ->
  match Doc_actual.terminated act p_ref with
  | None -> (doc, act, None)
  | Some act -> (doc, act, Some (Doc_actual.proof_res act))

let get_proof_res docs uri vsn =
  with_doc_vsn docs uri vsn @@ fun doc act ->
  (doc, act, Some (Doc_actual.proof_res act))

let get_proof_res_latest docs uri =
  match latest_vsn docs uri with
  | None -> (docs, None, None)
  | Some latest_vsn ->
      let docs, res = get_proof_res docs uri latest_vsn in
      (docs, Some latest_vsn, res)

let get_obligation_state docs uri vsn range =
  with_doc_vsn docs uri vsn @@ fun doc act ->
  let res =
    match Doc_actual.get_obligation_state act range with
    | None -> None
    | Some ps -> Some (Proof_step.as_lsp_tlaps_proof_step_details uri ps)
  in
  (doc, act, res)

let get_obligation_state_latest docs uri range =
  match latest_vsn docs uri with
  | None -> (docs, None)
  | Some latest_vsn ->
      let docs, res = get_obligation_state docs uri latest_vsn range in
      (docs, res)
