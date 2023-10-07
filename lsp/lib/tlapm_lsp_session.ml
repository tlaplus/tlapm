module Docs = Tlapm_lsp_docs

type events =
  | LspEOF
  | LspPacket of Jsonrpc.Packet.t
  | TlapmEvent of int * Tlapm_lsp_prover.ToolboxProtocol.tlapm_msg

type mode = Initializing | Ready | Shutdown

type t = {
  events : unit -> events;
  output : Jsonrpc.Packet.t option -> unit;
  mode : mode;
  docs : Docs.t;
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
    st.output (Some p);
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
    (* TODO: Implement. *)
    st

  let%test_unit "basics" =
    let st =
      {
        mode = Initializing;
        output = (fun _ -> ());
        events = (fun () -> LspEOF);
        docs = Docs.empty;
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

let handle_tlapm_msg _ref _msg st =
  (* TODO: Implement. *)
  Some st

let handle_event e st =
  match e with
  | LspEOF -> None
  | LspPacket p -> handle_lsp_packet p st
  | TlapmEvent (ref, msg) -> handle_tlapm_msg ref msg st

(* The main event processing loop.
   At the exit we send EOF to the output thread. *)
let rec loop st =
  match handle_event (st.events ()) st with
  | Some st' -> loop st'
  | None -> st.output None

(** Entry point to run the session as a fiber. *)
let run event_taker output_adder =
  let st =
    {
      mode = Initializing;
      events = event_taker;
      output = output_adder;
      docs = Docs.empty;
    }
  in
  loop st
