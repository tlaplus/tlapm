let diagnostic_source = "TLAPM"

module Docs = Tlapm_lsp_docs
module Prover = Tlapm_lsp_prover
module LspT = Lsp.Types

(* A reference to a doc_uri * version * prover launch counter. *)
type doc_ref = Lsp.Types.DocumentUri.t * int * int

type events =
  | LspEOF
  | LspPacket of Jsonrpc.Packet.t
  | TlapmEvent of doc_ref * Tlapm_lsp_prover.ToolboxProtocol.tlapm_msg

type mode = Initializing | Ready | Shutdown

type t = {
  event_taker : unit -> events;
  event_adder : events -> unit;
  output_adder : Jsonrpc.Packet.t option -> unit;
  last_req_id : int;
  progress : Tlapm_lsp_progress.t;
  mode : mode;
  docs : Docs.t;
  prov : Prover.t;
}

let with_docs' st f =
  match st.mode with
  | Initializing -> Error "initializing"
  | Ready ->
      let st', docs' = f (st, st.docs) in
      Ok { st' with docs = docs' }
  | Shutdown -> Error "going to shutdown"

let with_docs st f =
  match with_docs' st f with
  | Ok st' -> st'
  | Error err ->
      Eio.traceln "Ignoring request: %s" err;
      st

(* For callbacks. *)
let lsp_send st p =
  st.output_adder (Some p);
  st

(* For callbacks. *)
type t' = t

module Progress = Tlapm_lsp_progress.Make (struct
  type t = t'

  let lsp_send = lsp_send

  let next_req_id st =
    let next = st.last_req_id + 1 in
    (`Int next, { st with last_req_id = next })
end)

let progress_proof_started st p_ref =
  let progress, st = Progress.proof_started st.progress p_ref st in
  { st with progress }

let progress_obl_num st p_ref obl_num =
  let progress, st = Progress.obl_num st.progress p_ref obl_num st in
  { st with progress }

let progress_obl_changed st p_ref obl_done =
  let progress, st = Progress.obl_changed st.progress p_ref obl_done st in
  { st with progress }

let progress_proof_ended st p_ref =
  let progress, st = Progress.proof_ended st.progress p_ref st in
  { st with progress }

(* TODO: {"jsonrpc":"2.0","method":"window/workDoneProgress/cancel","params":{"token":"tlapm_lsp-p_ref-1"}} *)

let make_diagnostics os ns =
  let open Prover.ToolboxProtocol in
  let open Lsp.Types in
  let diagnostics_o =
    List.filter_map
      (fun (o : tlapm_obligation) ->
        let message =
          "Obligation: "
          ^ Prover.ToolboxProtocol.tlapm_obl_state_to_string o.status
        in
        let message =
          match o.obl with None -> message | Some obl -> message ^ "\n" ^ obl
        in
        let severity =
          match o.status with
          | ToBeProved -> None
          | BeingProved -> None
          | Normalized -> None
          | Proved -> None
          | Failed -> Some Lsp.Types.DiagnosticSeverity.Error
          | Interrupted -> Some Lsp.Types.DiagnosticSeverity.Error
          | Trivial -> None
          | Unknown _ -> Some Lsp.Types.DiagnosticSeverity.Error
        in
        match severity with
        | None -> None
        | Some severity ->
            let range = Prover.TlapmRange.as_lsp_range o.loc in
            let source = diagnostic_source in
            Some (Diagnostic.create ~message ~range ~severity ~source ()))
      os
  in
  let diagnostics_n =
    List.map
      (fun (n : tlapm_notif) ->
        let severity =
          match n.sev with
          | TlapmNotifError -> Lsp.Types.DiagnosticSeverity.Error
          | TlapmNotifWarning -> Lsp.Types.DiagnosticSeverity.Warning
        in
        Diagnostic.create ~message:n.msg
          ~range:(Prover.TlapmRange.as_lsp_range n.loc)
          ~severity ~source:diagnostic_source ())
      ns
  in
  List.concat [ diagnostics_o; diagnostics_n ]

let send_diagnostics st uri vsn os ns =
  let open Lsp.Types in
  let diagnostics = make_diagnostics os ns in
  let d_par =
    PublishDiagnosticsParams.create ~diagnostics ~uri ~version:vsn ()
  in
  let d_ntf = Lsp.Server_notification.PublishDiagnostics d_par in
  let d_pkg =
    Jsonrpc.Packet.Notification (Lsp.Server_notification.to_jsonrpc d_ntf)
  in
  st.output_adder (Some d_pkg)

let send_proof_state_markers st uri pss =
  let jsonrpc_notif =
    Jsonrpc.Notification.create
      ~params:
        (`List
          [
            LspT.DocumentUri.yojson_of_t uri;
            `List
              (List.filter_map
                 (fun ps -> ps)
                 (List.map Docs.PS.yojson_of_t pss));
          ])
      ~method_:"tlaplus/tlaps/proofStates" ()
  in
  let lsp_notif = Lsp.Server_notification.UnknownNotification jsonrpc_notif in
  let lsp_packet =
    Jsonrpc.Packet.Notification (Lsp.Server_notification.to_jsonrpc lsp_notif)
  in
  st.output_adder (Some lsp_packet)

let send_proof_info st uri vsn res =
  match res with
  | Some (Docs.ProofRes.{ p_ref; obs; nts; pss } as proof_res) ->
      let st =
        progress_obl_changed st p_ref (Docs.ProofRes.obs_done proof_res)
      in
      send_diagnostics st uri vsn obs nts;
      send_proof_state_markers st uri pss
  | None -> ()

module Handlers = Tlapm_lsp_handlers.Make (struct
  module LspT = Lsp.Types

  type t = t'

  let ready st =
    match st.mode with
    | Initializing -> { st with mode = Ready }
    | Ready -> st
    | Shutdown -> st

  let shutdown st =
    match st.mode with
    | Initializing -> { st with mode = Shutdown }
    | Ready -> { st with mode = Shutdown }
    | Shutdown -> st

  let lsp_send = lsp_send
  let with_docs = with_docs

  let prove_step st (uri : LspT.DocumentUri.t) (vsn : int)
      (range : LspT.Range.t) =
    Eio.traceln "PROVE_STEP: %s#%d lines %d--%d"
      (LspT.DocumentUri.to_string uri)
      vsn range.start.line range.end_.line;
    let docs, next_p_ref_opt =
      Docs.prepare_proof st.docs uri vsn (Prover.TlapmRange.of_lsp_range range)
    in
    let st = { st with docs } in
    match next_p_ref_opt with
    | Some (p_ref, doc_text, p_range, proof_res) -> (
        let st = progress_proof_started st p_ref in
        send_proof_info st uri vsn (Some proof_res);
        let prov_events e =
          st.event_adder (TlapmEvent ((uri, vsn, p_ref), e))
        in
        match
          Prover.start_async st.prov uri vsn doc_text p_range prov_events ()
        with
        | Ok prov' -> { st with prov = prov' }
        | Error msg ->
            Eio.traceln "failed to launch prover: %s" msg;
            st)
    | None ->
        Eio.traceln "cannot find doc/vsn";
        st

  let suggest_proof_range st uri range =
    let range = Prover.TlapmRange.of_lsp_range range in
    let docs, res = Docs.suggest_proof_range st.docs uri range in
    let st = { st with docs } in
    match res with
    | None -> (st, None)
    | Some (vsn, p_range) ->
        (st, Some (vsn, Prover.TlapmRange.as_lsp_range p_range))

  let latest_diagnostics st uri =
    Eio.traceln "PULL_DIAGS: %s" (LspT.DocumentUri.to_string uri);
    let docs, vsn_opt, proof_res_opt = Docs.get_proof_res_latest st.docs uri in
    let st = { st with docs } in
    (match (vsn_opt, proof_res_opt) with
    | None, _ -> send_proof_info st uri 0 (Some Docs.ProofRes.empty)
    | Some vsn, None -> send_proof_info st uri vsn (Some Docs.ProofRes.empty)
    | Some vsn, Some p_res -> send_proof_info st uri vsn (Some p_res));
    (st, (0, []))

  let diagnostic_source = diagnostic_source

  let%test_unit "basics" =
    Eio_main.run @@ fun env ->
    Eio.Switch.run @@ fun sw ->
    let fs = Eio.Stdenv.fs env in
    let proc_mgr = Eio.Stdenv.process_mgr env in
    let st =
      {
        mode = Initializing;
        event_taker = (fun () -> LspEOF);
        event_adder = (fun _ -> ());
        output_adder = (fun _ -> ());
        last_req_id = 0;
        progress = Tlapm_lsp_progress.make ();
        docs = Docs.empty;
        prov = Prover.create sw fs proc_mgr;
      }
    in
    let () =
      match with_docs' st (fun docs -> docs) with
      | Ok _ -> failwith "should fail"
      | Error _ -> ()
    in
    let st = ready st in
    let st =
      match with_docs' st (fun docs -> docs) with
      | Ok st -> st
      | Error e -> failwith e
    in
    let st = shutdown st in
    let () =
      match with_docs' st (fun docs -> docs) with
      | Ok _ -> failwith "should fail"
      | Error _ -> ()
    in
    ()
end)

let handle_lsp_packet p st = Some (Handlers.handle_jsonrpc_packet p st)

let handle_tlapm_msg ((uri, vsn, p_ref) : doc_ref) msg st =
  let open Prover.ToolboxProtocol in
  let open Lsp.Types in
  Eio.traceln "handle_tlapm_msg: uri=%s, vsn=%d, p_ref=%d"
    (DocumentUri.to_string uri)
    vsn p_ref;
  match msg with
  | TlapmNotif notif ->
      Eio.traceln "---> TlapmNotif: %s" notif.msg;
      let docs, res = Docs.add_notif st.docs uri vsn p_ref notif in
      send_proof_info st uri vsn res;
      Some { st with docs }
  | TlapmObligationsNumber obl_num ->
      Eio.traceln "---> TlapmObligationsNumber";
      let st =
        try progress_obl_num st p_ref obl_num
        with e ->
          Eio.traceln "EXCEPTION %s" (Printexc.to_string e);
          st
      in
      Eio.traceln "---> TlapmObligationsNumber -- done";
      (* TODO: Cleanup. *)
      Some st
  | TlapmObligation obl ->
      Eio.traceln "---> TlapmObligation, id=%d" obl.id;
      let docs, res = Docs.add_obl st.docs uri vsn p_ref obl in
      send_proof_info st uri vsn res;
      Some { st with docs }
  | TlapmTerminated ->
      Eio.traceln "---> TlapmTerminated";
      let st = progress_proof_ended st p_ref in
      let docs, res = Docs.terminated st.docs uri vsn p_ref in
      send_proof_info st uri vsn res;
      Some { st with docs }

let handle_event e st =
  match e with
  | LspEOF -> None
  | LspPacket p -> handle_lsp_packet p st
  | TlapmEvent (ref, msg) -> handle_tlapm_msg ref msg st

(* The main event processing loop.
   At the exit we send EOF to the output thread. *)
let rec loop st =
  match handle_event (st.event_taker ()) st with
  | Some st' -> loop st'
  | None -> st.output_adder None

(** Entry point to run the session as a fiber. *)
let run event_taker event_adder output_adder sw fs proc_mgr =
  let st =
    {
      mode = Initializing;
      event_taker;
      event_adder;
      output_adder;
      last_req_id = 0;
      progress = Tlapm_lsp_progress.make ();
      docs = Docs.empty;
      prov = Prover.create sw fs proc_mgr;
    }
  in
  loop st
