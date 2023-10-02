(* cSpell:words sprintf *)

(** Helper to send responses to requests. *)
let reply_ok (jsonrpc_req : Jsonrpc.Request.t) writer payload =
  let open Jsonrpc in
  let response = Response.ok jsonrpc_req.id payload in
  let packet = Packet.Response response in
  writer packet

(** Helper to send responses to requests. *)
let reply_error (jsonrpc_req : Jsonrpc.Request.t) writer code message =
  let open Jsonrpc in
  let error = Response.Error.make ~code ~message () in
  let response = Response.error jsonrpc_req.id error in
  let packet = Jsonrpc.Packet.Response response in
  writer packet

(** Dispatch notification packets. *)
let handle_jsonrpc_notif jsonrpc_notif writer state =
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
      let send_diags () =
        let some =
          Diagnostic.create ~message:"Hey from prover!"
            ~range:
              (Range.create
                 ~start:(Position.create ~line:1 ~character:3)
                 ~end_:(Position.create ~line:1 ~character:7))
            ()
        in
        let d_par =
          PublishDiagnosticsParams.create ~diagnostics:[ some ] ~uri
            ~version:vsn ()
        in
        let diag = Lsp.Server_notification.PublishDiagnostics d_par in
        let d_pkg =
          Jsonrpc.Packet.Notification (Lsp.Server_notification.to_jsonrpc diag)
        in
        writer d_pkg
      in
      let with_docs docs =
        send_diags ();
        Tlapm_lsp_docs.add docs uri vsn text
      in
      Tlapm_lsp_state.handle_if_ready_silent state with_docs
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
  let supported_commands =
    [ "tlapm-lsp-test.prover-info"; "tlapm-lsp-test.prove-step.lsp" ]
  in
  let capabilities =
    ServerCapabilities.create
      ~textDocumentSync:(`TextDocumentSyncKind TextDocumentSyncKind.Full)
      ~executeCommandProvider:
        (ExecuteCommandOptions.create ~commands:supported_commands
           ~workDoneProgress:false ())
      ~diagnosticProvider:
        (`DiagnosticOptions
          (DiagnosticOptions.create ~identifier:"TLAPM"
             ~interFileDependencies:false ~workspaceDiagnostics:false
             ~workDoneProgress:false ()))
      ~codeActionProvider:
        (`CodeActionOptions
          (CodeActionOptions.create ~resolveProvider:true
             ~workDoneProgress:false
             ~codeActionKinds:[ CodeActionKind.Other "proof-state" ]
             ()))
      ()
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
  reply_ok jsonrpc_req writer (InitializeResult.yojson_of_t respInfo);
  state

let handle_jsonrpc_req_shutdown (_jsonrpc_req : Jsonrpc.Request.t) state =
  Eio.traceln "CONN: Shutdown";
  Tlapm_lsp_state.shutdown state

let handle_jsonrpc_req_unknown (jsonrpc_req : Jsonrpc.Request.t) message writer
    state =
  Eio.traceln "Received unknown JsonRPC request, method=%s, error=%s"
    jsonrpc_req.method_ message;
  let open Jsonrpc.Response.Error in
  reply_error jsonrpc_req writer Code.MethodNotFound message;
  state

(* {"jsonrpc":"2.0","id":1,"method":"workspace/executeCommand","params":{"command":"tlapm-lsp-test.prover-info","arguments":[]}} *)
let handle_jsonrpc_req_exec_cmd (jsonrpc_req : Jsonrpc.Request.t)
    (params : Lsp.Types.ExecuteCommandParams.t) writer state =
  match params.command with
  | "tlapm-lsp-test.prover-info" ->
      Eio.traceln "COMMAND: prover-info";
      reply_ok jsonrpc_req writer (`String "OK");
      state
  | "tlapm-lsp-test.prove-step.lsp" ->
      (* TODO: Args are passed from the codeAction. *)
      Eio.traceln "COMMAND: prove-step";
      reply_ok jsonrpc_req writer (`String "OK");
      state
  | unknown ->
      handle_jsonrpc_req_unknown jsonrpc_req
        (Printf.sprintf "command unknown: %s" unknown)
        writer state

(**
Provide code actions for a document.
  - Code actions can be used for proof decomposition, probably.
*)
let handle_jsonrpc_req_code_action (jsonrpc_req : Jsonrpc.Request.t)
    (_params : Lsp.Types.CodeActionParams.t) writer state =
  let open Lsp.Types in
  let someActionDiag =
    Diagnostic.create ~message:"Hey from prover as an action!"
      ~range:
        (Range.create
           ~start:(Position.create ~line:2 ~character:13)
           ~end_:(Position.create ~line:2 ~character:17))
      ()
  in
  let someAction =
    Lsp.Types.CodeAction.create ~title:"Prover code action"
      ~diagnostics:[ someActionDiag ]
      ~command:
        (Command.create ~command:"tlapm-lsp-test.prove-step.lsp"
           ~title:"Prove it as an action!"
           ~arguments:[ `String "important_arg" ]
           ())
      ()
  in
  let acts = Some [ `CodeAction someAction ] in
  reply_ok jsonrpc_req writer (Lsp.Types.CodeActionResult.yojson_of_t acts);
  state

let handle_jsonrpc_req_code_action_resolve (jsonrpc_req : Jsonrpc.Request.t)
    (_params : Lsp.Types.CodeAction.t) writer state =
  (* TODO: Actually resolve the code actions. *)
  reply_ok jsonrpc_req writer (`String "OK");
  state

(** Dispatch request packets. *)
let handle_jsonrpc_request (jsonrpc_req : Jsonrpc.Request.t) writer state =
  let open Lsp.Types in
  match Lsp.Client_request.of_jsonrpc jsonrpc_req with
  | Ok (E (Initialize (params : InitializeParams.t))) ->
      handle_jsonrpc_req_initialize jsonrpc_req params writer state
  | Ok (E (ExecuteCommand params)) ->
      handle_jsonrpc_req_exec_cmd jsonrpc_req params writer state
  | Ok (E (CodeAction params)) ->
      handle_jsonrpc_req_code_action jsonrpc_req params writer state
  | Ok (E (CodeActionResolve params)) ->
      handle_jsonrpc_req_code_action_resolve jsonrpc_req params writer state
  | Ok (E Shutdown) -> handle_jsonrpc_req_shutdown jsonrpc_req state
  | Ok (E (UnknownRequest unknown)) -> (
      match unknown.meth with
      | "textDocument/diagnostic" ->
          (* TODO: Handle the diagnostic pull. *)
          state
      | _ ->
          handle_jsonrpc_req_unknown jsonrpc_req "unknown method not supported"
            writer state)
  | Ok (E _unsupported) ->
      handle_jsonrpc_req_unknown jsonrpc_req "method not supported" writer state
  | Error reason ->
      let err_msg = Printf.sprintf "cannot decode method: %s" reason in
      handle_jsonrpc_req_unknown jsonrpc_req err_msg writer state

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
