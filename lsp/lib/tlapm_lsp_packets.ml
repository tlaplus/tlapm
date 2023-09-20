(* // TODO: curl -vvv -X POST -H 'Content-Type: application/vscode-jsonrpc; charset=utf-8' -d '{"jsonrpc": "2.0", "id": 1, "method": "textDocument/completion", "params": { }}' http://localhost:8080/ *)

let handle_jsonrpc_notif jsonrpc_notif _writer =
  match Lsp.Client_notification.of_jsonrpc jsonrpc_notif with
  (* TODO: Handle all the cases. *)
  | Ok Initialized -> ()
  | Ok (TextDocumentDidOpen _params) -> ()
  | Ok (UnknownNotification _params) ->
      ()
      (* writer packet *)
      (* // TODO: That's just echo. *)
  | _ -> ()

let handle_jsonrpc_request jsonrpc_req _writer =
  match Lsp.Client_request.of_jsonrpc jsonrpc_req with
  | Ok (E (Initialize _params)) -> () (* TODO: Handle all the cases. *)
  | _ -> ()

let handle_jsonrpc_packet (packet : Jsonrpc.Packet.t) writer =
  Eio.traceln "Got LSP Packet";
  match packet with
  | Notification jsonrpc_notif -> handle_jsonrpc_notif jsonrpc_notif writer
  | Request jsonrpc_req -> handle_jsonrpc_request jsonrpc_req writer
  | Response _ -> () (* // TODO: Handle it. *)
  | Batch_call _ -> () (* // TODO: Handle it. *)
  | Batch_response _ -> ()
