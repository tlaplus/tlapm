(* // TODO: curl -vvv -X POST -H 'Content-Type: application/vscode-jsonrpc; charset=utf-8' -d '{"jsonrpc": "2.0", "id": 1, "method": "textDocument/completion", "params": { }}' http://localhost:8080/ *)

let handle_jsonrpc_notif jsonrpc_notif _writer =
  match Lsp.Client_notification.of_jsonrpc jsonrpc_notif with
  (* TODO: Handle all the cases. *)
  | Ok Initialized -> ()
  | Ok (TextDocumentDidOpen params) ->
      let uri = params.textDocument.uri in
      let text = params.textDocument.text in
      Eio.traceln "DOCUMENT[OP]: %s => %s"
        (Lsp.Types.DocumentUri.to_string uri)
        text
  | Ok (TextDocumentDidChange params) ->
      let uri = params.textDocument.uri in
      let changes = params.contentChanges in
      let rec trec (items : Lsp.Types.TextDocumentContentChangeEvent.t list) =
        match items with
        | [] -> ()
        | doc :: tail ->
            let text = doc.text in
            Eio.traceln "DOCUMENT[CH]: %s => %s"
              (Lsp.Types.DocumentUri.to_string uri)
              text;
            trec tail
      in
      trec changes
  | Ok (TextDocumentDidClose _params) -> ()
  | Ok (UnknownNotification _params) ->
      ()
      (* writer packet *)
      (* // TODO: That's just echo. *)
  | _ -> ()

(* // TODO: Handle all the cases. *)
let handle_jsonrpc_request (jsonrpc_req : Jsonrpc.Request.t) writer : unit =
  let print_ci (params : Lsp.Types.InitializeParams.t) =
    match params.clientInfo with
    | None -> ()
    | Some ci ->
        let ci_version = match ci.version with None -> "?" | Some v -> v in
        Eio.traceln "Client INFO, name=%s, version=%s" ci.name ci_version
  in
  match Lsp.Client_request.of_jsonrpc jsonrpc_req with
  | Ok (E (Initialize (params : Lsp.Types.InitializeParams.t))) ->
      print_ci params;
      let open Lsp.Types in
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
        InitializeResult.create_serverInfo ~name:"tlapm-lsp"
          ~version:server_version ()
      in
      let respInfo = InitializeResult.create ~capabilities ~serverInfo () in
      let response =
        Jsonrpc.Response.ok jsonrpc_req.id
          (InitializeResult.yojson_of_t respInfo)
      in
      let packet = Jsonrpc.Packet.Response response in
      writer packet
  | _ -> ()

let handle_jsonrpc_packet (packet : Jsonrpc.Packet.t) writer =
  Eio.traceln "Got LSP Packet";
  match packet with
  | Notification jsonrpc_notif -> handle_jsonrpc_notif jsonrpc_notif writer
  | Request jsonrpc_req -> handle_jsonrpc_request jsonrpc_req writer
  | Response _ -> () (* // TODO: Handle it. *)
  | Batch_call _ -> () (* // TODO: Handle it. *)
  | Batch_response _ -> ()
