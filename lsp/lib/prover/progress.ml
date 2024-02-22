module LspT = Lsp.Types
module OblIdSet = Set.Make (Int)

type t = {
  p_ref : int;
  token : LspT.ProgressToken.t;
  started : bool;
  ended : bool;
  obl_count : int option; (* Total number of proof obligations. *)
  obl_done : OblIdSet.t; (* Number of obligations already checked. *)
}

let title = "Checking TLA+ proofs"

let message pr =
  match pr.obl_count with
  | None -> "Obligation count unknown."
  | Some total ->
      Format.sprintf "%d of %d obligations checked"
        (OblIdSet.cardinal pr.obl_done)
        total

let percentage pr =
  match pr.obl_count with
  | None -> 0
  | Some 0 -> 100
  | Some obl_count -> OblIdSet.cardinal pr.obl_done * 100 / obl_count

let make_token p_ref = `String (Format.sprintf "tlapm_lsp-p_ref-%d" p_ref)

let reset p_ref ended =
  {
    p_ref;
    token = make_token p_ref;
    started = ended;
    ended;
    obl_count = None;
    obl_done = OblIdSet.empty;
  }

(* --------------- Functions creating LSP packets. --------------- *)

let make_lsp_req_create pr =
  Lsp.Server_request.WorkDoneProgressCreate
    (LspT.WorkDoneProgressCreateParams.create ~token:pr.token)

let make_lsp_notif_begin pr =
  let message = message pr in
  let percentage = percentage pr in
  let value =
    Lsp.Progress.Begin
      (LspT.WorkDoneProgressBegin.create ~cancellable:true ~message ~percentage
         ~title ())
  in
  Lsp.Server_notification.WorkDoneProgress
    (LspT.ProgressParams.create ~token:pr.token ~value)

let make_lsp_notif_report pr =
  let message = message pr in
  let percentage = percentage pr in
  let value =
    Lsp.Progress.Report
      (LspT.WorkDoneProgressReport.create ~cancellable:true ~message ~percentage
         ())
  in
  Lsp.Server_notification.WorkDoneProgress
    (LspT.ProgressParams.create ~token:pr.token ~value)

let make_lsp_notif_end pr =
  let message = message pr in
  let value = Lsp.Progress.End (LspT.WorkDoneProgressEnd.create ~message ()) in
  Lsp.Server_notification.WorkDoneProgress
    (LspT.ProgressParams.create ~token:pr.token ~value)

(* These should be provided by the session to interact with the environment. *)

module type Callbacks = sig
  type p := t
  type t

  val next_req_id : t -> Jsonrpc.Id.t * t
  val lsp_send : t -> Jsonrpc.Packet.t -> t
  val with_progress : t -> (t -> p -> t * p) -> t
end

module Make (CB : Callbacks) = struct
  let send_notif cb_state lsp_notif =
    let rpc_notif = Lsp.Server_notification.to_jsonrpc lsp_notif in
    let rpc_packet = Jsonrpc.Packet.Notification rpc_notif in
    CB.lsp_send cb_state rpc_packet

  let send_req cb_state lsp_req =
    let req_id, cb_state = CB.next_req_id cb_state in
    let rpc_req = Lsp.Server_request.to_jsonrpc_request lsp_req ~id:req_id in
    let rpc_packet = Jsonrpc.Packet.Request rpc_req in
    CB.lsp_send cb_state rpc_packet

  (* --------------- The main functionality. --------------- *)

  let make () = reset 0 true
  let is_latest pr token = make_token pr.p_ref = token

  (* End the previous progress bar, if not ended yet, and create a new one. *)
  let proof_started ~p_ref cb_state =
    CB.with_progress cb_state @@ fun cb_state pr ->
    if pr.p_ref < p_ref then
      let cb_state =
        match pr.ended with
        | true -> cb_state
        | false -> send_notif cb_state (make_lsp_notif_end pr)
      in
      let pr = reset p_ref false in
      let cb_state = send_req cb_state (make_lsp_req_create pr) in
      (cb_state, pr)
    else (cb_state, pr)

  let obl_count ~p_ref ~obl_count cb_state =
    CB.with_progress cb_state @@ fun cb_state pr ->
    if p_ref = pr.p_ref then
      let was_started = pr.started in
      let pr = { pr with obl_count = Some obl_count; started = true } in
      let cb_state =
        match was_started with
        | true -> send_notif cb_state (make_lsp_notif_report pr)
        | false -> send_notif cb_state (make_lsp_notif_begin pr)
      in
      (cb_state, pr)
    else (cb_state, pr)

  let obligation ~p_ref ~(obl : Toolbox.Obligation.t) cb_state =
    CB.with_progress cb_state @@ fun cb_state pr ->
    if
      p_ref = pr.p_ref && pr.started && (not pr.ended)
      && (not (OblIdSet.mem obl.id pr.obl_done))
      && Toolbox.Obligation.is_final obl
    then
      let pr = { pr with obl_done = OblIdSet.add obl.id pr.obl_done } in
      let cb_state = send_notif cb_state (make_lsp_notif_report pr) in
      (cb_state, pr)
    else (cb_state, pr)

  let proof_ended ~p_ref cb_state =
    CB.with_progress cb_state @@ fun cb_state pr ->
    if p_ref = pr.p_ref && pr.ended = false then
      let pr = { pr with ended = true } in
      let cb_state = send_notif cb_state (make_lsp_notif_end pr) in
      (cb_state, pr)
    else (cb_state, pr)
end

let%test_module "progress reporting tests" =
  (module struct
    type tst_t = { req_id : int; sent : Jsonrpc.Packet.t list; progress : t }

    module TestCB = struct
      type t = tst_t

      let next_req_id cb =
        let next = cb.req_id + 1 in
        (`Int next, { cb with req_id = next })

      let lsp_send cb pkt = { cb with sent = pkt :: cb.sent }

      let with_progress st f =
        let st, progress = f st st.progress in
        { st with progress }
    end

    module TestPr = Make (TestCB)

    let fresh = { req_id = 0; sent = []; progress = TestPr.make () }

    let%test_unit "basic" =
      let open Toolbox in
      let fake_obl = Obligation.Test.with_id_status in
      let cb = fresh in
      let p_ref = 1 in
      let cb = TestPr.proof_started ~p_ref cb in
      let cb = TestPr.obl_count ~p_ref ~obl_count:10 cb in
      let cb = TestPr.obligation ~p_ref ~obl:(fake_obl 2 Proved) cb in
      let cb = TestPr.obligation ~p_ref ~obl:(fake_obl 3 ToBeProved) cb in
      let cb = TestPr.obligation ~p_ref ~obl:(fake_obl 5 Proved) cb in
      let cb = TestPr.proof_ended ~p_ref cb in
      match List.length cb.sent with
      | 5 -> ()
      | x -> failwith (Format.sprintf "got unexpected message count: %d" x)
  end)
