open Util
open Prover

let prover_mutex = Eio.Mutex.create ()

(* Separated form the type [t] to have the value lazily evaluated. *)
module Parsed = struct
  type t = {
    nts : Toolbox.tlapm_notif list;
    ps : Proof_step.t option;
        (** Parsed document structure, a tree of proof steps.
          It is obtained by parsing the document and then updated
          when obligation proof states are received from the prover. *)
  }

  let make ~uri ~(doc_vsn : Doc_vsn.t) ~(ps_prev : Proof_step.t option) =
    match
      Eio.Mutex.use_rw ~protect:true prover_mutex @@ fun () ->
      Parser.module_of_string (Doc_vsn.text doc_vsn)
        (LspT.DocumentUri.to_path uri)
    with
    | Ok mule ->
        let ps = Proof_step.of_module mule ps_prev in
        { nts = []; ps }
    | Error (loc_opt, msg) ->
        let nts = [ Toolbox.notif_of_loc_msg loc_opt msg ] in
        { nts; ps = None }

  let ps_if_ready (p : t Lazy.t) =
    match Lazy.is_val p with false -> None | true -> (Lazy.force p).ps
end

type t = {
  doc_vsn : Doc_vsn.t;
  p_ref : int;
  ps_prev : Proof_step.t option;
      (** Proof steps from the previous version, if there was any.*)
  parsed : Parsed.t Lazy.t;
      (** Parsed document and information derived from it. *)
}

(** Create new actual document based on the document version [doc_vsn]
    and port the current state from the previous actual document
    [prev_act], if provided. *)
let make uri doc_vsn prev_act =
  match prev_act with
  | None ->
      (* There is no previous active document, we will not try
         to move the proof state from there. *)
      let parsed = lazy (Parsed.make ~uri ~doc_vsn ~ps_prev:None) in
      { doc_vsn; p_ref = 0; ps_prev = None; parsed }
  | Some prev_act ->
      (* We have the previous actual document, thus either use its
         parsed data, or the data it got from its previous. *)
      let ps_prev =
        match Parsed.ps_if_ready prev_act.parsed with
        | None -> prev_act.ps_prev
        | some -> some
      in
      let parsed = lazy (Parsed.make ~uri ~doc_vsn ~ps_prev) in
      { doc_vsn; p_ref = prev_act.p_ref; ps_prev; parsed }

let vsn act = Doc_vsn.version act.doc_vsn
let text act = Doc_vsn.text act.doc_vsn

let proof_res (act : t) : Doc_proof_res.t =
  let parsed = Lazy.force act.parsed in
  Doc_proof_res.make parsed.nts parsed.ps

let prepare_proof (act : t) next_p_ref =
  (* Force it to be parsed, then prepare for the next proof session. *)
  match (Lazy.force act.parsed).ps with
  | None -> None
  | Some _ -> Some { act with p_ref = next_p_ref }

let locate_proof_range (act : t) range =
  let parsed = Lazy.force act.parsed in
  Proof_step.locate_proof_range parsed.ps range

let get_obligation_state act range =
  let parsed = Lazy.force act.parsed in
  Proof_step.locate_proof_step parsed.ps range

let add_obl (act : t) (p_ref : int) (obl : Toolbox.Obligation.t) =
  if act.p_ref = p_ref then
    let parsed = Lazy.force act.parsed in
    let ps = Proof_step.with_prover_result parsed.ps p_ref obl in
    let parsed = Lazy.from_val { parsed with ps } in
    Some { act with parsed }
  else None

let add_notif (act : t) p_ref notif =
  if act.p_ref = p_ref then
    let parsed = Lazy.force act.parsed in
    let nts = notif :: parsed.nts in
    let parsed = Lazy.from_val { parsed with nts } in
    Some { act with parsed }
  else None

let terminated (act : t) p_ref =
  if act.p_ref = p_ref then
    let parsed = Lazy.force act.parsed in
    let ps = Proof_step.with_prover_terminated parsed.ps p_ref in
    let parsed = Lazy.from_val { parsed with ps } in
    Some { act with parsed }
  else None
