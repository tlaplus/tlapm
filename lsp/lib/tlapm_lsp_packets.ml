(* cSpell:words sprintf tlaplus *)
module Docs = Tlapm_lsp_docs
module LT = Lsp.Types

module type Callbacks = sig
  type cb_t

  val ready : cb_t -> cb_t
  val shutdown : cb_t -> cb_t
  val lsp_send : cb_t -> Jsonrpc.Packet.t -> cb_t
  val with_docs : cb_t -> (cb_t * Docs.t -> cb_t * Docs.t) -> cb_t
  val prove_step : cb_t -> LT.DocumentUri.t -> int -> LT.Range.t -> cb_t

  val latest_diagnostics :
    cb_t -> LT.DocumentUri.t -> cb_t * (int * LT.Diagnostic.t list)

  val diagnostic_source : string
end

module Make (CB : Callbacks) = struct
  (** Helper to send responses to requests. *)
  let reply_ok (jsonrpc_req : Jsonrpc.Request.t) payload cb_state =
    let open Jsonrpc in
    let response = Response.ok jsonrpc_req.id payload in
    let packet = Packet.Response response in
    CB.lsp_send cb_state packet

  (** Helper to send responses to requests. *)
  let reply_error (jsonrpc_req : Jsonrpc.Request.t) code message cb_state =
    let open Jsonrpc in
    let error = Response.Error.make ~code ~message () in
    let response = Response.error jsonrpc_req.id error in
    let packet = Jsonrpc.Packet.Response response in
    CB.lsp_send cb_state packet

  (** Dispatch notification packets. *)
  let handle_jsonrpc_notif jsonrpc_notif cb_state =
    let open Lsp.Types in
    match Lsp.Client_notification.of_jsonrpc jsonrpc_notif with
    | Ok Initialized ->
        Eio.traceln "CONN: Initialized";
        CB.ready cb_state
    | Ok (TextDocumentDidOpen params) ->
        let uri = params.textDocument.uri in
        let vsn = params.textDocument.version in
        let text = params.textDocument.text in
        Eio.traceln "DOCUMENT[Open]: %s => %s" (DocumentUri.to_string uri) text;
        CB.with_docs cb_state @@ fun (cb_st, docs) ->
        let docs = Tlapm_lsp_docs.add docs uri vsn text in
        (cb_st, docs)
    | Ok (TextDocumentDidChange params) -> (
        let uri = params.textDocument.uri in
        let vsn = params.textDocument.version in
        match params.contentChanges with
        | [ { text; range = None; rangeLength = None } ] ->
            Eio.traceln "DOCUMENT[Change]: %s => %s"
              (DocumentUri.to_string uri)
              text;
            CB.with_docs cb_state @@ fun (cb_st, docs) ->
            (cb_st, Tlapm_lsp_docs.add docs uri vsn text)
        | _ -> failwith "incremental changes not supported")
    | Ok (TextDocumentDidClose params) ->
        let uri = params.textDocument.uri in
        CB.with_docs cb_state @@ fun (cb_st, docs) ->
        (cb_st, Tlapm_lsp_docs.rem docs uri)
    | Ok (DidSaveTextDocument params) ->
        let uri = params.textDocument.uri in
        Eio.traceln "DOCUMENT[Save]: %s" (DocumentUri.to_string uri);
        cb_state
    | Ok (SetTrace params) ->
        let level =
          match params.value with
          | Compact -> "Compact"
          | Off -> "Off"
          | Messages -> "Messages"
          | Verbose -> "Verbose"
        in
        Eio.traceln "CONN: Set trace: %s -- ignored" level;
        cb_state
    | Ok (UnknownNotification _params) ->
        Eio.traceln "Unknown notification: %s" jsonrpc_notif.method_;
        cb_state
    | Ok _unsupported ->
        Eio.traceln "Unsupported notification: %s" jsonrpc_notif.method_;
        cb_state
    | Error error ->
        Eio.traceln "Failed to decode notification: %s - %s"
          jsonrpc_notif.method_ error;
        cb_state

  let handle_jsonrpc_req_initialize (jsonrpc_req : Jsonrpc.Request.t) params
      cb_state =
    let open Lsp.Types in
    let print_ci (params : InitializeParams.t) =
      match params.clientInfo with
      | None -> ()
      | Some ci ->
          let ci_version = match ci.version with None -> "?" | Some v -> v in
          Eio.traceln "CONN: Client INFO, name=%s, version=%s" ci.name
            ci_version
    in
    print_ci params;
    let supported_commands =
      [ "tlapm-lsp-test.prover-info"; "tlaplus.tlaps.check-step.lsp" ]
    in
    let capabilities =
      ServerCapabilities.create
        ~textDocumentSync:(`TextDocumentSyncKind TextDocumentSyncKind.Full)
        ~executeCommandProvider:
          (ExecuteCommandOptions.create ~commands:supported_commands
             ~workDoneProgress:false ())
        ~diagnosticProvider:
          (`DiagnosticOptions
            (DiagnosticOptions.create ~identifier:CB.diagnostic_source
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
      InitializeResult.create_serverInfo ~name:"tlapm-lsp"
        ~version:server_version ()
    in
    let respInfo = InitializeResult.create ~capabilities ~serverInfo () in
    reply_ok jsonrpc_req (InitializeResult.yojson_of_t respInfo) cb_state

  let handle_jsonrpc_req_shutdown (_jsonrpc_req : Jsonrpc.Request.t) cb_state =
    Eio.traceln "CONN: Shutdown";
    CB.shutdown cb_state

  (* TODO: It looks like VSCode don't update the diagnostics. *)
  let handle_jsonrpc_req_diagnostics (jsonrpc_req : Jsonrpc.Request.t) uri
      cb_state =
    let cb_state, (p_ref, items) = CB.latest_diagnostics cb_state uri in
    let report =
      LT.FullDocumentDiagnosticReport.create ~items
        ~resultId:(string_of_int p_ref) ()
    in
    reply_ok jsonrpc_req
      (LT.FullDocumentDiagnosticReport.yojson_of_t report)
      cb_state

  let handle_jsonrpc_req_unknown (jsonrpc_req : Jsonrpc.Request.t) message
      cb_state =
    Eio.traceln "Received unknown JsonRPC request, method=%s, error=%s"
      jsonrpc_req.method_ message;
    let open Jsonrpc.Response.Error in
    reply_error jsonrpc_req Code.MethodNotFound message cb_state

  (* Example request:
     {"jsonrpc":"2.0","id":6,"method":"workspace/executeCommand","params":{
      "command":"tlaplus.tlaps.check-step.lsp",
      "arguments":[
        {"uri":"file:///home/.../aaa.tla","version":1},
        {"start":{"line":2,"character":15},"end":{"line":2,"character":15}} ]}}
  *)
  let handle_check_step (jsonrpc_req : Jsonrpc.Request.t)
      (params : LT.ExecuteCommandParams.t) cb_state =
    Eio.traceln "COMMAND: prove-step";
    match params.arguments with
    | Some [ uri_vsn_arg; range_arg ] ->
        let uri_vsn =
          LT.VersionedTextDocumentIdentifier.t_of_yojson uri_vsn_arg
        in
        let range = LT.Range.t_of_yojson range_arg in
        CB.prove_step cb_state uri_vsn.uri uri_vsn.version range
    | Some _ ->
        reply_error jsonrpc_req Jsonrpc.Response.Error.Code.InvalidParams
          "single argument object expected" cb_state
    | None ->
        reply_error jsonrpc_req Jsonrpc.Response.Error.Code.InvalidParams
          "arguments missing" cb_state

  (* {"jsonrpc":"2.0","id":1,"method":"workspace/executeCommand","params":{"command":"tlapm-lsp-test.prover-info","arguments":[]}} *)
  let handle_jsonrpc_req_exec_cmd (jsonrpc_req : Jsonrpc.Request.t)
      (params : Lsp.Types.ExecuteCommandParams.t) cb_state =
    match params.command with
    | "tlapm-lsp-test.prover-info" ->
        Eio.traceln "COMMAND: prover-info";
        reply_ok jsonrpc_req (`String "OK") cb_state
    | "tlaplus.tlaps.check-step.lsp" ->
        handle_check_step jsonrpc_req params cb_state
    | unknown ->
        handle_jsonrpc_req_unknown jsonrpc_req
          (Printf.sprintf "command unknown: %s" unknown)
          cb_state

  (**
    Provide code actions for a document.
    - Code actions can be used for proof decomposition, probably.
  *)
  let handle_jsonrpc_req_code_action (jsonrpc_req : Jsonrpc.Request.t)
      (_params : Lsp.Types.CodeActionParams.t) cb_state =
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
          (Command.create ~command:"tlaplus.tlaps.check-step.lsp"
             ~title:"Prove it as an action!"
             ~arguments:[ `String "important_arg" ]
             ())
        ()
    in
    let acts = Some [ `CodeAction someAction ] in
    reply_ok jsonrpc_req (Lsp.Types.CodeActionResult.yojson_of_t acts) cb_state

  let handle_jsonrpc_req_code_action_resolve (jsonrpc_req : Jsonrpc.Request.t)
      (_params : Lsp.Types.CodeAction.t) cb_state =
    (* TODO: Actually resolve the code actions. *)
    reply_ok jsonrpc_req (`String "OK") cb_state

  (* TODO: Thats experiment. *)
  let tmp_send_proof_state (cb_state : CB.cb_t) uri =
    let range =
      LT.Range.create
        ~start:(LT.Position.create ~line:1 ~character:3)
        ~end_:(LT.Position.create ~line:2 ~character:5)
    in
    let jrn =
      Jsonrpc.Notification.create
        ~params:
          (`List
            [
              LT.DocumentUri.yojson_of_t uri;
              `List
                [
                  `Assoc
                    [
                      ("range", LT.Range.yojson_of_t range);
                      ("state", `String "proved");
                      ("hover", `String "Congrats!");
                    ];
                ];
            ])
        ~method_:"tlaplus/tlaps/proofStates" ()
    in
    let ntf = Lsp.Server_notification.UnknownNotification jrn in
    let pkt =
      Jsonrpc.Packet.Notification (Lsp.Server_notification.to_jsonrpc ntf)
    in
    CB.lsp_send cb_state pkt

  (** Dispatch request packets. *)
  let handle_jsonrpc_request (jsonrpc_req : Jsonrpc.Request.t) cb_state =
    let open Lsp.Types in
    match Lsp.Client_request.of_jsonrpc jsonrpc_req with
    | Ok (E (Initialize (params : InitializeParams.t))) ->
        handle_jsonrpc_req_initialize jsonrpc_req params cb_state
    | Ok (E (ExecuteCommand params)) ->
        handle_jsonrpc_req_exec_cmd jsonrpc_req params cb_state
    | Ok (E (CodeAction params)) ->
        handle_jsonrpc_req_code_action jsonrpc_req params cb_state
    | Ok (E (CodeActionResolve params)) ->
        handle_jsonrpc_req_code_action_resolve jsonrpc_req params cb_state
    | Ok (E Shutdown) -> handle_jsonrpc_req_shutdown jsonrpc_req cb_state
    | Ok (E (UnknownRequest unknown)) -> (
        match unknown.meth with
        | "textDocument/diagnostic" -> (
            match unknown.params with
            | Some params -> (
                match params with
                | `Assoc xs ->
                    let text_doc_js = List.assoc "textDocument" xs in
                    let text_doc_id =
                      LT.TextDocumentIdentifier.t_of_yojson text_doc_js
                    in
                    let cb_state =
                      tmp_send_proof_state cb_state text_doc_id.uri
                    in
                    handle_jsonrpc_req_diagnostics jsonrpc_req text_doc_id.uri
                      cb_state
                | `List _xs ->
                    reply_error jsonrpc_req
                      Jsonrpc.Response.Error.Code.InvalidParams "params missing"
                      cb_state)
            | None ->
                reply_error jsonrpc_req
                  Jsonrpc.Response.Error.Code.InvalidParams "params missing"
                  cb_state)
        | _ ->
            handle_jsonrpc_req_unknown jsonrpc_req
              "unknown method not supported" cb_state)
    | Ok (E _unsupported) ->
        handle_jsonrpc_req_unknown jsonrpc_req "method not supported" cb_state
    | Error reason ->
        let err_msg = Printf.sprintf "cannot decode method: %s" reason in
        handle_jsonrpc_req_unknown jsonrpc_req err_msg cb_state

  (* Dispatch client responses to our requests. *)
  let handle_jsonrpc_response _jsonrpc_resp state = state

  let handle_jsonrpc_packet (packet : Jsonrpc.Packet.t) state =
    match packet with
    | Notification notif -> handle_jsonrpc_notif notif state
    | Request req -> handle_jsonrpc_request req state
    | Response resp -> handle_jsonrpc_response resp state
    | Batch_call sub_packets ->
        let fold_fun state_acc sub_pkg =
          match sub_pkg with
          | `Notification notif -> handle_jsonrpc_notif notif state_acc
          | `Request req -> handle_jsonrpc_request req state_acc
        in
        List.fold_left fold_fun state sub_packets
    | Batch_response sub_responses ->
        let fold_fun state_acc sub_resp =
          handle_jsonrpc_response sub_resp state_acc
        in
        List.fold_left fold_fun state sub_responses
end
