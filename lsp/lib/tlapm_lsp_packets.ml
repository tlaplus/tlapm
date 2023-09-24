(** Dispatch notification packets. *)
let handle_jsonrpc_notif jsonrpc_notif _writer state =
  let open Lsp.Types in
  match Lsp.Client_notification.of_jsonrpc jsonrpc_notif with
  | Ok Initialized ->
      Eio.traceln "CONN: Initialized";
      Tlapm_lsp_state.ready state
  | Ok (TextDocumentDidOpen params) ->
      let uri = params.textDocument.uri in
      let vsn = params.textDocument.version in
      let text = params.textDocument.text in
      Eio.traceln "DOCUMENT[Open]: %s => %s" (DocumentUri.to_string uri) text;
      Tlapm_lsp_state.handle_if_ready_silent state (fun docs ->
          Tlapm_lsp_docs.add docs uri vsn text)
  | Ok (TextDocumentDidChange params) -> (
      let uri = params.textDocument.uri in
      let vsn = params.textDocument.version in
      match params.contentChanges with
      | [ { text; range = None; rangeLength = None } ] ->
          Eio.traceln "DOCUMENT[Change]: %s => %s"
            (DocumentUri.to_string uri)
            text;
          Tlapm_lsp_state.handle_if_ready_silent state (fun docs ->
              Tlapm_lsp_docs.add docs uri vsn text)
      | _ -> failwith "incremental changes not supported")
  | Ok (TextDocumentDidClose params) ->
      let uri = params.textDocument.uri in
      Tlapm_lsp_state.handle_if_ready_silent state (fun docs ->
          Tlapm_lsp_docs.rem docs uri)
  | Ok (DidSaveTextDocument params) ->
      let uri = params.textDocument.uri in
      Eio.traceln "DOCUMENT[Save]: %s" (DocumentUri.to_string uri);
      state
  | Ok (SetTrace params) ->
      let level =
        match params.value with
        | Compact -> "Compact"
        | Off -> "Off"
        | Messages -> "Messages"
        | Verbose -> "Verbose"
      in
      Eio.traceln "CONN: Set trace: %s -- ignored" level;
      state
  | Ok (UnknownNotification _params) ->
      Eio.traceln "Unknown notification: %s" jsonrpc_notif.method_;
      state
  | Ok _unsupported ->
      Eio.traceln "Unsupported notification: %s" jsonrpc_notif.method_;
      state
  | Error error ->
      Eio.traceln "Failed to decode notification: %s - %s" jsonrpc_notif.method_
        error;
      state

let handle_jsonrpc_req_initialize (jsonrpc_req : Jsonrpc.Request.t) params
    writer state =
  let open Lsp.Types in
  let print_ci (params : InitializeParams.t) =
    match params.clientInfo with
    | None -> ()
    | Some ci ->
        let ci_version = match ci.version with None -> "?" | Some v -> v in
        Eio.traceln "CONN: Client INFO, name=%s, version=%s" ci.name ci_version
  in
  print_ci params;
  let capabilities =
    ServerCapabilities.create
      ~textDocumentSync:(`TextDocumentSyncKind TextDocumentSyncKind.Full) ()
  in
  let server_version =
    match Build_info.V1.version () with
    | None -> "development"
    | Some v -> Build_info.V1.Version.to_string v
  in
  let serverInfo =
    InitializeResult.create_serverInfo ~name:"tlapm-lsp" ~version:server_version
      ()
  in
  let respInfo = InitializeResult.create ~capabilities ~serverInfo () in
  let response =
    Jsonrpc.Response.ok jsonrpc_req.id (InitializeResult.yojson_of_t respInfo)
  in
  let packet = Jsonrpc.Packet.Response response in
  let () = writer packet in
  state

let handle_jsonrpc_req_shutdown (_jsonrpc_req : Jsonrpc.Request.t) state =
  Eio.traceln "CONN: Shutdown";
  Tlapm_lsp_state.shutdown state

let handle_jsonrpc_req_unknown (jsonrpc_req : Jsonrpc.Request.t) writer state =
  Eio.traceln "Received unknown JsonRPC request, method=%s" jsonrpc_req.method_;
  let open Jsonrpc in
  let error =
    Response.Error.make ~code:Response.Error.Code.MethodNotFound
      ~message:"method not supported" ()
  in
  let response = Response.error jsonrpc_req.id error in
  let packet = Jsonrpc.Packet.Response response in
  let () = writer packet in
  state

(** Dispatch request packets. *)
let handle_jsonrpc_request (jsonrpc_req : Jsonrpc.Request.t) writer state =
  let open Lsp.Types in
  match Lsp.Client_request.of_jsonrpc jsonrpc_req with
  | Ok (E (Initialize (params : InitializeParams.t))) ->
      handle_jsonrpc_req_initialize jsonrpc_req params writer state
  | Ok (E Shutdown) -> handle_jsonrpc_req_shutdown jsonrpc_req state
  | _ -> handle_jsonrpc_req_unknown jsonrpc_req writer state

(* Dispatch client responses to our requests. *)
let handle_jsonrpc_response _jsonrpc_resp state = state

let handle_jsonrpc_packet (packet : Jsonrpc.Packet.t) writer state =
  match packet with
  | Notification notif -> handle_jsonrpc_notif notif writer state
  | Request req -> handle_jsonrpc_request req writer state
  | Response resp -> handle_jsonrpc_response resp state
  | Batch_call sub_packets ->
      let fold_fun state_acc sub_pkg =
        match sub_pkg with
        | `Notification notif -> handle_jsonrpc_notif notif writer state_acc
        | `Request req -> handle_jsonrpc_request req writer state_acc
      in
      List.fold_left fold_fun state sub_packets
  | Batch_response sub_responses ->
      let fold_fun state_acc sub_resp =
        handle_jsonrpc_response sub_resp state_acc
      in
      List.fold_left fold_fun state sub_responses
