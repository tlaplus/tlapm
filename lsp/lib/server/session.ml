open Prover
module LspT = Lsp.Types
module DocUriSet = Set.Make (LspT.DocumentUri)

(* A reference to a doc_uri * version * prover launch counter. *)
type doc_ref = LspT.DocumentUri.t * int * int

type events =
  | LspEOF
  | LspPacket of Jsonrpc.Packet.t
  | TlapmEvent of doc_ref * Toolbox.Msg.t
  | TimerTick

type mode = Initializing | Ready | Shutdown

type t = {
  event_taker : unit -> events;
  event_adder : events -> unit;
  output_adder : Jsonrpc.Packet.t option -> unit;
  last_req_id : int;
  next_p_ref : int;
  paths : string list;  (** Additional paths to look for TLA+ modules. *)
  progress : Prover.Progress.t;
  mode : mode;
  docs : Docs.t;
  prov : Prover.t;
      (** Prover that is currently running.
          We are always running not more than 1 prover to
          avoid their interference via fingerprints, etc. *)
  delayed : DocUriSet.t;
      (** Docs which have delayed proof info updates.
          We use this to buffer the updates to the UI.*)
  current_ps : LspT.Location.t option;
      (** The proof step that is currently selected.
          We will send state updates for it. *)
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

module ProverProgress = Prover.Progress.Make (struct
  type nonrec t = t

  let lsp_send = lsp_send

  let next_req_id st =
    let next = st.last_req_id + 1 in
    (`Int next, { st with last_req_id = next })

  let with_progress st f =
    let st, progress = f st st.progress in
    { st with progress }
end)

let send_diagnostics diagnostics st uri vsn =
  let open LspT in
  let d_par =
    PublishDiagnosticsParams.create ~diagnostics ~uri ~version:vsn ()
  in
  let d_ntf = Lsp.Server_notification.PublishDiagnostics d_par in
  let d_pkg =
    Jsonrpc.Packet.Notification (Lsp.Server_notification.to_jsonrpc d_ntf)
  in
  st.output_adder (Some d_pkg)

let send_proof_state_markers marks st uri =
  let open Structs in
  let jsonrpc_notif =
    Jsonrpc.Notification.create
      ~params:
        (`List
          [
            LspT.DocumentUri.yojson_of_t uri;
            `List (List.map TlapsProofStepMarker.yojson_of_t marks);
          ])
      ~method_:"tlaplus/tlaps/proofStepMarkers" ()
  in
  let lsp_notif = Lsp.Server_notification.UnknownNotification jsonrpc_notif in
  let lsp_packet =
    Jsonrpc.Packet.Notification (Lsp.Server_notification.to_jsonrpc lsp_notif)
  in
  st.output_adder (Some lsp_packet)

let send_obligation_proof_state st =
  let open Structs in
  let maybe_st =
    with_docs' st @@ fun (st, docs) ->
    let docs, notif_data =
      match st.current_ps with
      | None -> (docs, None)
      | Some loc ->
          let tlapm_range = Range.of_lsp_range loc.range in
          let position = Range.from tlapm_range in
          Docs.get_proof_step_details_latest docs loc.uri position
    in
    let notif_packet = TlapsProofStepDetails.to_jsonrpc_packet notif_data in
    st.output_adder (Some notif_packet);
    (st, docs)
  in
  match maybe_st with Ok st -> st | Error _ -> st

let send_proof_info st uri vsn res =
  match res with
  | Some res ->
      (* Send the current proof step info, if it is in the [uri] file. *)
      let st =
        match st.current_ps with
        | Some current_ps when current_ps.uri = uri -> (
            match DocUriSet.mem current_ps.uri st.delayed with
            | true -> send_obligation_proof_state st
            | false -> st)
        | Some _other -> st
        | None -> st
      in
      (* And then the diagnostics and markers. *)
      let diags, marks = Docs.Doc_proof_res.as_lsp res in
      send_diagnostics diags st uri vsn;
      send_proof_state_markers marks st uri;
      let delayed = DocUriSet.remove uri st.delayed in
      { st with delayed }
  | None -> st

let send_latest_proof_info st uri =
  let docs, vsn_opt, proof_res_opt = Docs.get_proof_res_latest st.docs uri in
  let st = { st with docs } in
  match (vsn_opt, proof_res_opt) with
  | None, _ -> send_proof_info st uri 0 (Some Docs.Doc_proof_res.empty)
  | Some vsn, None -> send_proof_info st uri vsn (Some Docs.Doc_proof_res.empty)
  | Some vsn, Some p_res -> send_proof_info st uri vsn (Some p_res)

let delay_proof_info st uri =
  let delayed = DocUriSet.add uri st.delayed in
  { st with delayed }

let parser_fun loader_paths =
  let parser ~content ~filename =
    Parser.module_of_string ~content ~filename ~loader_paths
  in
  parser

module SessionHandlers = Handlers.Make (struct
  module LspT = LspT

  type nonrec t = t

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

  let use_paths st paths =
    Eio.traceln "Will use paths: %s" (String.concat ":" paths);
    let docs = Docs.with_parser st.docs (parser_fun paths) in
    { st with paths; docs }

  let prove_step st (uri : LspT.DocumentUri.t) (vsn : int)
      (range : LspT.Range.t) =
    Eio.traceln "PROVE_STEP: %s#%d lines %d--%d"
      (LspT.DocumentUri.to_string uri)
      vsn range.start.line range.end_.line;
    let p_ref = st.next_p_ref in
    let st = { st with next_p_ref = st.next_p_ref + 1 } in
    let docs, proof_opt =
      Docs.prover_prepare st.docs uri vsn (Range.of_lsp_range range) ~p_ref
    in
    let st = { st with docs } in
    match proof_opt with
    | Some (doc_text, p_range, proof_res) -> (
        let st = ProverProgress.proof_started ~p_ref st in
        let st = send_proof_info st uri vsn (Some proof_res) in
        let prov_events e =
          st.event_adder (TlapmEvent ((uri, vsn, p_ref), e))
        in
        match
          Prover.start_async st.prov uri doc_text p_range st.paths prov_events
            ()
        with
        | Ok prov' -> { st with prov = prov' }
        | Error msg ->
            Eio.traceln "failed to launch prover: %s" msg;
            st)
    | None ->
        Eio.traceln "cannot find doc/vsn";
        st

  let cancel st (progress_token : LspT.ProgressToken.t) =
    match ProverProgress.is_latest st.progress progress_token with
    | true ->
        let prov = Prover.cancel_all st.prov in
        { st with prov }
    | false -> st

  let suggest_proof_range st uri range =
    let range = Range.of_lsp_range range in
    let docs, res = Docs.suggest_proof_range st.docs uri range in
    let st = { st with docs } in
    match res with
    | None -> (st, None)
    | Some (vsn, p_range) -> (st, Some (vsn, Range.as_lsp_range p_range))

  let track_obligation_proof_state (st : t) uri range =
    let st = { st with current_ps = Some (LspT.Location.create ~uri ~range) } in
    let st = send_obligation_proof_state st in
    st

  let latest_diagnostics st uri =
    Eio.traceln "PULL_DIAGS: %s" (LspT.DocumentUri.to_string uri);
    let st = send_latest_proof_info st uri in
    (st, (0, []))

  let diagnostic_source = Const.diagnostic_source

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
        next_p_ref = 0;
        paths = [];
        progress = ProverProgress.make ();
        docs = Docs.empty (parser_fun []);
        prov = Prover.create sw fs proc_mgr;
        delayed = DocUriSet.empty;
        current_ps = None;
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

let handle_lsp_packet p st = Some (SessionHandlers.handle_jsonrpc_packet p st)

let handle_toolbox_msg ((uri, vsn, p_ref) : doc_ref) msg st =
  let open LspT in
  Eio.traceln "handle_Toolbox.Msg.t: uri=%s, vsn=%d, p_ref=%d"
    (DocumentUri.to_string uri)
    vsn p_ref;
  match msg with
  | Toolbox.Msg.TlapmNotif notif ->
      Eio.traceln "---> TlapmNotif: %s" notif.msg;
      let docs, _res = Docs.prover_add_notif st.docs uri vsn p_ref notif in
      let st = { st with docs } in
      let st = delay_proof_info st uri in
      Some st
  | Toolbox.Msg.TlapmObligationsNumber obl_count ->
      Eio.traceln "---> TlapmObligationsNumber";
      let st = ProverProgress.obl_count ~p_ref ~obl_count st in
      Some st
  | Toolbox.Msg.TlapmObligation obl ->
      Eio.traceln "---> TlapmObligation, id=%d" obl.id;
      let st = ProverProgress.obligation ~p_ref ~obl st in
      let docs, _res = Docs.prover_add_obl st.docs uri vsn p_ref obl in
      let st = { st with docs } in
      let st = delay_proof_info st uri in
      Some st
  | Toolbox.Msg.TlapmTerminated ->
      Eio.traceln "---> TlapmTerminated";
      let st = ProverProgress.proof_ended ~p_ref st in
      let docs, res = Docs.prover_terminated st.docs uri vsn p_ref in
      let st = { st with docs } in
      let st = send_proof_info st uri vsn res in
      Some st

let handle_timer_tick st =
  let send_for_doc uri stAcc =
    Eio.traceln "Sending delayed proof info for %s "
      (LspT.DocumentUri.to_string uri);
    send_latest_proof_info stAcc uri
  in
  let st = DocUriSet.fold send_for_doc st.delayed st in
  Some { st with delayed = DocUriSet.empty }

let handle_event e st =
  match e with
  | LspEOF -> None
  | LspPacket p -> handle_lsp_packet p st
  | TlapmEvent (ref, msg) -> handle_toolbox_msg ref msg st
  | TimerTick -> handle_timer_tick st

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
      next_p_ref = 0;
      paths = [];
      progress = ProverProgress.make ();
      docs = Docs.empty (parser_fun []);
      prov = Prover.create sw fs proc_mgr;
      delayed = DocUriSet.empty;
      current_ps = None;
    }
  in
  loop st
