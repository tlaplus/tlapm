open Util
open Prover
module Proof_step = Proof_step
module Proof_status = Proof_status
module Doc_proof_res = Doc_proof_res

type parser_fun = Util.parser_fun
type tk = LspT.DocumentUri.t
type t = { parser : Util.parser_fun; by_uri : Doc.t DocMap.t }

let empty parser = { parser; by_uri = DocMap.empty }

let with_parser docs parser =
  let by_uri = DocMap.map (fun d -> Doc.with_parser d parser) docs.by_uri in
  { parser; by_uri }

(* Just record the text. It will be processed later, when a prover
   command or diagnostics query is issued by the client. *)
let add docs uri vsn txt =
  let tv = Doc_vsn.make txt vsn in
  let upd = function
    | None -> Some (Doc.make uri tv docs.parser)
    | Some (doc : Doc.t) -> Some (Doc.add doc tv)
  in
  { docs with by_uri = DocMap.update uri upd docs.by_uri }

let rem docs uri = { docs with by_uri = DocMap.remove uri docs.by_uri }

let latest_vsn docs uri =
  match DocMap.find_opt uri docs.by_uri with
  | None -> None
  | Some doc -> Some (Doc.latest_vsn doc)

(* Here we merge pending versions with the actual and then run
   the supplied function on the prepared doc info. *)
let with_doc_vsn docs uri vsn f =
  match DocMap.find_opt uri docs.by_uri with
  | None -> (docs, None)
  | Some doc -> (
      match Doc.set_actual_vsn doc vsn with
      | None -> (docs, None)
      | Some doc ->
          let doc, res = Doc.with_actual doc f in
          let by_uri = DocMap.add uri doc docs.by_uri in
          ({ docs with by_uri }, res))

(* Calculate proof range by user selection. *)
let suggest_proof_range docs uri range : t * (int * Range.t) option =
  match latest_vsn docs uri with
  | None -> (docs, None)
  | Some vsn ->
      with_doc_vsn docs uri vsn @@ fun (doc : Doc.t) (act : Doc_actual.t) ->
      let p_range = Doc_actual.locate_proof_range act range in
      (doc, act, Some (vsn, p_range))

(* Push specific version to the actual, increase the proof_rec and clear the notifications. *)
let prover_prepare docs uri vsn range ~p_ref :
    t * (string * Range.t * Doc_proof_res.t) option =
  with_doc_vsn docs uri vsn @@ fun (doc : Doc.t) (act : Doc_actual.t) ->
  match Doc_actual.prover_prepare act p_ref with
  | None -> (doc, act, None)
  | Some act ->
      let p_range = Doc_actual.locate_proof_range act range in
      let res = (Doc_actual.text act, p_range, Doc_actual.proof_res act) in
      (doc, act, Some res)

let prover_add_obl_provers docs uri vsn p_ref obl_id provers =
  with_doc_vsn docs uri vsn @@ fun (doc : Doc.t) (act : Doc_actual.t) ->
  match Doc_actual.prover_add_obl_provers act p_ref obl_id provers with
  | None -> (doc, act, None)
  | Some act -> (doc, act, Doc_actual.is_obl_final act p_ref obl_id)

let prover_add_obl docs uri vsn p_ref (obl : Toolbox.Obligation.t) =
  with_doc_vsn docs uri vsn @@ fun (doc : Doc.t) (act : Doc_actual.t) ->
  match Doc_actual.prover_add_obl act p_ref obl with
  | None -> (doc, act, None)
  | Some act -> (doc, act, Doc_actual.is_obl_final act p_ref obl.id)

let prover_add_notif docs uri vsn p_ref notif =
  with_doc_vsn docs uri vsn @@ fun (doc : Doc.t) (act : Doc_actual.t) ->
  match Doc_actual.prover_add_notif act p_ref notif with
  | None -> (doc, act, None)
  | Some act -> (doc, act, Some (Doc_actual.proof_res act))

let prover_terminated docs uri vsn p_ref =
  with_doc_vsn docs uri vsn @@ fun (doc : Doc.t) (act : Doc_actual.t) ->
  match Doc_actual.prover_terminated act p_ref with
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

let get_proof_step_details docs uri vsn range =
  with_doc_vsn docs uri vsn @@ fun doc act ->
  let res =
    match Doc_actual.get_proof_step_details act range with
    | None -> None
    | Some ps -> Some (Proof_step.as_lsp_tlaps_proof_step_details uri ps)
  in
  (doc, act, res)

let get_proof_step_details_latest docs uri range =
  match latest_vsn docs uri with
  | None -> (docs, None)
  | Some latest_vsn ->
      let docs, res = get_proof_step_details docs uri latest_vsn range in
      (docs, res)

let on_parsed_mule docs uri vsn f =
  with_doc_vsn docs uri vsn @@ fun doc act ->
  let res = Doc_actual.on_parsed_mule act f in
  (doc, act, res)

let on_parsed_mule_latest docs uri f =
  match latest_vsn docs uri with
  | None -> (docs, None)
  | Some latest_vsn -> on_parsed_mule docs uri latest_vsn (f latest_vsn)
