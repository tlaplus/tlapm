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

  let prove_step st (uri : LT.DocumentUri.t) (vsn : int) (range : LT.Range.t) =
    Eio.traceln "PROVE_STEP: %s#%d lines %d--%d"
      (LT.DocumentUri.to_string uri)
      vsn range.start.line range.end_.line;
    let docs, next_p_ref_opt = Docs.next_p_ref_opt st.docs uri vsn in
    let st = { st with docs } in
    match next_p_ref_opt with
    | Some (p_ref, doc_text) -> (
        (* TODO: Check if line numbers are 0/1 based. *)
        let prov_events e =
          st.event_adder (TlapmEvent ((uri, vsn, p_ref), e))
        in
        match
          Prover.start_async st.prov uri vsn doc_text range.start.line
            range.end_.line prov_events ()
        with
        | Ok prov' -> { st with prov = prov' }
        | Error msg ->
            Eio.traceln "failed to launch prover: %s" msg;
            st)
    | None ->
        Eio.traceln "cannot find doc/vsn";
        st

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
  | TlapmWarning { msg = tw_msg } ->
      (* TODO: Implement. *)
      Eio.traceln "---> TlapmWarning: %s" tw_msg;
      Some st
  | TlapmError { msg = te_msg; _ } ->
      (* TODO: Implement. *)
      Eio.traceln "---> TlapmError: %s" te_msg;
      Some st
  | TlapmObligationsNumber _ ->
      (* TODO: Implement. *)
      Eio.traceln "---> TlapmObligationsNumber";
      Some st
  | TlapmObligation _ ->
      (* TODO: Implement. *)
      Eio.traceln "---> TlapmObligation";
      Some st
  | TlapmTerminated ->
      (* TODO: Implement. *)
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
