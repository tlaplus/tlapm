module LspT = Lsp.Types

type t = {
  p_ref : int;
  token : LspT.ProgressToken.t;
  started : bool;
  ended : bool;
  obl_count : int option; (* Total number of proof obligations. *)
  obl_done : int; (* Number of obligations already checked. *)
}

let title = "Checking TLA+ proofs"

let message pr =
  match pr.obl_count with
  | None -> "Obligation count unknown."
  | Some total ->
      Format.sprintf "%d of %d obligations checked" pr.obl_done total

let percentage pr =
  match pr.obl_count with
  | None -> 0
  | Some 0 -> 100
  | Some obl_count -> pr.obl_done * 100 / obl_count

let token p_ref = `String (Format.sprintf "tlapm_lsp-p_ref-%d" p_ref)

let reset p_ref ended =
  {
    p_ref;
    token = token p_ref;
    started = ended;
    ended;
    obl_count = None;
    obl_done = 0;
  }

let make () = reset 0 true

module type Callbacks = sig
  type t

  val next_req_id : t -> Jsonrpc.Id.t * t
  val lsp_send : t -> Jsonrpc.Packet.t -> t
end

module Make (CB : Callbacks) = struct
  (* --------------- Functions creating LSP packets. --------------- *)

  let lsp_req_create pr =
    Lsp.Server_request.WorkDoneProgressCreate
      (LspT.WorkDoneProgressCreateParams.create ~token:pr.token)

  let lsp_notif_begin pr =
    let message = message pr in
    let percentage = percentage pr in
    let value =
      Lsp.Progress.Begin
        (LspT.WorkDoneProgressBegin.create ~cancellable:true ~message
           ~percentage ~title ())
    in
    Lsp.Server_notification.WorkDoneProgress
      (LspT.ProgressParams.create ~token:pr.token ~value)

  let lsp_notif_report pr =
    let message = message pr in
    let percentage = percentage pr in
    let value =
      Lsp.Progress.Report
        (LspT.WorkDoneProgressReport.create ~cancellable:true ~message
           ~percentage ())
    in
    Lsp.Server_notification.WorkDoneProgress
      (LspT.ProgressParams.create ~token:pr.token ~value)

  let lsp_notif_end pr =
    let message = message pr in
    let value =
      Lsp.Progress.End (LspT.WorkDoneProgressEnd.create ~message ())
    in
    Lsp.Server_notification.WorkDoneProgress
      (LspT.ProgressParams.create ~token:pr.token ~value)

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

  (* End the previous progress bar, if not ended yet, and create a new one. *)
  let proof_started pr p_ref cb_state =
    if pr.p_ref < p_ref then
      let cb_state =
        match pr.ended with
        | true -> cb_state
        | false -> send_notif cb_state (lsp_notif_end pr)
      in
      let pr = reset p_ref false in
      let cb_state = send_req cb_state (lsp_req_create pr) in
      (pr, cb_state)
    else (pr, cb_state)

  let obl_num pr p_ref obl_count cb_state =
    if p_ref = pr.p_ref then
      let was_started = pr.started in
      let pr = { pr with obl_count = Some obl_count; started = true } in
      let cb_state =
        match was_started with
        | true -> send_notif cb_state (lsp_notif_report pr)
        | false -> send_notif cb_state (lsp_notif_begin pr)
      in
      (pr, cb_state)
    else (pr, cb_state)

  let obl_changed pr p_ref obl_done cb_state =
    if
      p_ref = pr.p_ref && pr.started && (not pr.ended)
      && obl_done <> pr.obl_done
    then
      let pr = { pr with obl_done } in
      let cb_state = send_notif cb_state (lsp_notif_report pr) in
      (pr, cb_state)
    else (pr, cb_state)

  let proof_ended pr p_ref cb_state =
    if p_ref = pr.p_ref && pr.ended = false then
      let pr = { pr with ended = true } in
      let cb_state = send_notif cb_state (lsp_notif_end pr) in
      (pr, cb_state)
    else (pr, cb_state)
end

let%test_module "progress reporting tests" =
  (module struct
    module TestCB = struct
      type t = { req_id : int; sent : Jsonrpc.Packet.t list }

      let fresh = { req_id = 0; sent = [] }

      let next_req_id cb =
        let next = cb.req_id + 1 in
        (`Int next, { cb with req_id = next })

      let lsp_send cb pkt = { cb with sent = pkt :: cb.sent }
    end

    module TestPr = Make (TestCB)

    let%test_unit "basic" =
      let cb = TestCB.fresh in
      let pr = make () in
      let p_ref = 1 in
      let pr, cb = TestPr.proof_started pr p_ref cb in
      let pr, cb = TestPr.obl_num pr p_ref 10 cb in
      let pr, cb = TestPr.obl_changed pr p_ref 5 cb in
      let pr, cb = TestPr.obl_changed pr p_ref 10 cb in
      let _pr, cb = TestPr.proof_ended pr p_ref cb in
      match List.length cb.sent with
      | 5 -> ()
      | x -> failwith (Format.sprintf "got unexpected message count: %d" x)
  end)
