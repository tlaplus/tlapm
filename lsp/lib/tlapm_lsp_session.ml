(* cSpell:words sprintf *)

(* TODO: Notes on the presentation.
   See DocumentHighlight -- <https://microsoft.github.io/language-server-protocol/specifications/lsp/3.17/specification/#documentHighlightOptions>
   Also:
     - executeCommandProvider
     - diagnosticProvider (why the diagnostics are not cleared?)
     - semanticTokens?
         <https://microsoft.github.io/language-server-protocol/specifications/lsp/3.17/specification/#semanticTokensClientCapabilities>
         <https://microsoft.github.io/language-server-protocol/specifications/lsp/3.17/specification/#textDocument_semanticTokens>
*)

let diagnostic_source = "TLAPM"

module Docs = Tlapm_lsp_docs
module Prover = Tlapm_lsp_prover

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

let make_diagnostics os ns =
  let open Prover.ToolboxProtocol in
  let open Lsp.Types in
  let diagnostics_o =
    List.map
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
          | ToBeProved -> Lsp.Types.DiagnosticSeverity.Hint
          | BeingProved -> Lsp.Types.DiagnosticSeverity.Hint
          | Normalized -> Lsp.Types.DiagnosticSeverity.Hint
          | Proved -> Lsp.Types.DiagnosticSeverity.Information
          | Failed -> Lsp.Types.DiagnosticSeverity.Error
          | Interrupted -> Lsp.Types.DiagnosticSeverity.Error
          | Trivial -> Lsp.Types.DiagnosticSeverity.Information
          | Unknown _ -> Lsp.Types.DiagnosticSeverity.Error
        in
        let range = Prover.TlapmRange.as_lsp_range o.loc in
        Diagnostic.create ~message ~range ~severity ~source:diagnostic_source ())
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

let send_diagnostics_if_changed st uri vsn res =
  match res with
  | Some (_id, os, ns) -> send_diagnostics st uri vsn os ns
  | None -> ()

module PacketsCB = struct
  module LT = Lsp.Types

  type cb_t = t

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

  let lsp_send st p =
    st.output_adder (Some p);
    st

  let with_docs = with_docs

  let prove_step st (uri : LT.DocumentUri.t) (vsn : int) (range : LT.Range.t) =
    Eio.traceln "PROVE_STEP: %s#%d lines %d--%d"
      (LT.DocumentUri.to_string uri)
      vsn range.start.line range.end_.line;
    let docs, next_p_ref_opt =
      Docs.prepare_proof st.docs uri vsn (Prover.TlapmRange.of_lsp_range range)
    in
    let st = { st with docs } in
    match next_p_ref_opt with
    | Some (p_ref, doc_text, p_range, proof_res) -> (
        send_diagnostics_if_changed st uri vsn (Some proof_res);
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

  let latest_diagnostics st uri =
    Eio.traceln "PULL_DIAGS: %s" (LT.DocumentUri.to_string uri);
    let docs, vsn_opt, proof_res_opt = Docs.get_proof_res_latest st.docs uri in
    let st = { st with docs } in
    (* Clear the the diagnostics sent by the server, otherwise
       they will be duplicated with the response to this one.
       TODO: That's probably wrong place for doing that.
       TODO: The diagnostics are still duplicated in some cases,
             e.g. when pull is done and then the same obl proved by command.
       TODO: Maybe we should reply here with an empty response, but resend
             the server-sent notification.
    *)
    (* send_diagnostics st uri 0 [] []; *)
    (match (vsn_opt, proof_res_opt) with
    | None, _ -> send_diagnostics st uri 0 [] []
    | Some vsn, None -> send_diagnostics st uri vsn [] []
    | Some vsn, Some (_p_ref, os, ns) -> send_diagnostics st uri vsn os ns);
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
end

module Packets = Tlapm_lsp_packets.Make (PacketsCB)

let handle_lsp_packet p st = Some (Packets.handle_jsonrpc_packet p st)

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
      send_diagnostics_if_changed st uri vsn res;
      Some { st with docs }
  | TlapmObligationsNumber _ ->
      (* TODO: Implement. *)
      Eio.traceln "---> TlapmObligationsNumber";
      Some st
  | TlapmObligation obl ->
      Eio.traceln "---> TlapmObligation, id=%d" obl.id;
      let docs, res = Docs.add_obl st.docs uri vsn p_ref obl in
      send_diagnostics_if_changed st uri vsn res;
      Some { st with docs }
  | TlapmTerminated ->
      (* TODO: Implement: mark revision unused? *)
      Eio.traceln "---> TlapmTerminated";
      Some st

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
      docs = Docs.empty;
      prov = Prover.create sw fs proc_mgr;
    }
  in
  loop st
