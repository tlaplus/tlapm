module LspT = Lsp.Types

(** Corresponds to `import { Location } from 'vscode-languageclient/node';` *)
module Location = struct
  type t = { uri : LspT.DocumentUri.t; range : LspT.Range.t }

  let make ~uri ~range = { uri; range }

  let yojson_of_t (t : t) =
    `Assoc
      [
        ("uri", LspT.DocumentUri.yojson_of_t t.uri);
        ("range", LspT.Range.yojson_of_t t.range);
      ]
end

(** Corresponds to
  ```
  export interface TlapsProofObligationResult {
    prover: string;
    meth: string;
    status: string;
    reason: string | null;
    obligation: string | null; // Non-null, if prover failed.
  }
  ```
*)
module TlapsProofObligationResult = struct
  type t = {
    prover : string;
    meth : string;
    status : string;
    reason : string option;
    obligation : string option;
  }

  let make ~prover ~meth ~status ~reason ~obligation =
    { prover; meth; status; reason; obligation }

  let yojson_of_t (t : t) =
    let opt_str o = match o with None -> `Null | Some s -> `String s in
    `Assoc
      [
        ("prover", `String t.prover);
        ("meth", `String t.meth);
        ("status", `String t.status);
        ("reason", opt_str t.reason);
        ("obligation", opt_str t.obligation);
      ]
end

(** Corresponds to
  ```
  export interface TlapsProofObligationState {
    location: Location;
    obligation: string;
    results: TlapsProofObligationResult[];
  }
  ```
  *)
module TlapsProofObligationState = struct
  type t = {
    location : Location.t;
    obligation : string;
    results : TlapsProofObligationResult.t list;
  }

  let make ~location ~obligation ~results = { location; obligation; results }

  let yojson_of_t (t : t option) =
    match t with
    | None -> `Null
    | Some t ->
        `Assoc
          [
            ("location", Location.yojson_of_t t.location);
            ("obligation", `String t.obligation);
            ( "results",
              `List (List.map TlapsProofObligationResult.yojson_of_t t.results)
            );
          ]

  let to_jsonrpc_packet t =
    let notif =
      Jsonrpc.Notification.create
        ~params:(`List [ yojson_of_t t ])
        ~method_:"tlaplus/tlaps/currentProofObligation" ()
    in
    let notif_server = Lsp.Server_notification.UnknownNotification notif in
    Jsonrpc.Packet.Notification
      (Lsp.Server_notification.to_jsonrpc notif_server)
end
