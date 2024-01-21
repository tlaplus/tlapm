module LspT = Lsp.Types

let opt_str o = match o with None -> `Null | Some s -> `String s

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
    range: Range;
    normalized: string;
    results: TlapsProofObligationResult[];
  }
  ```
  *)
module TlapsProofObligationState = struct
  type t = {
    range : LspT.Range.t;
    normalized : string option;
    results : TlapsProofObligationResult.t list;
  }

  let make ~range ~normalized ~results = { range; normalized; results }

  let yojson_of_t (t : t) =
    `Assoc
      [
        ("range", LspT.Range.yojson_of_t t.range);
        ("normalized", opt_str t.normalized);
        ( "results",
          `List (List.map TlapsProofObligationResult.yojson_of_t t.results) );
      ]
end

(** Corresponds to
  ```
  export interface TlapsProofStepDetails {
    kind: string;
    location: Location;
    obligations: TlapsProofObligationState[];
  }
  ```
  TODO: Add sub-step counts by state.
  TODO: Add the derived state.
*)
module TlapsProofStepDetails = struct
  type t = {
    kind : string;
    location : LspT.Location.t;
    obligations : TlapsProofObligationState.t list;
  }

  let make ~kind ~location ~obligations = { kind; location; obligations }

  let yojson_of_t (t : t option) =
    match t with
    | None -> `Null
    | Some t ->
        `Assoc
          [
            ("kind", `String t.kind);
            ("location", LspT.Location.yojson_of_t t.location);
            ( "obligations",
              `List
                (List.map TlapsProofObligationState.yojson_of_t t.obligations)
            );
          ]

  let to_jsonrpc_packet t =
    let notif =
      Jsonrpc.Notification.create
        ~params:(`List [ yojson_of_t t ])
        ~method_:"tlaplus/tlaps/currentProofStep" ()
    in
    let notif_server = Lsp.Server_notification.UnknownNotification notif in
    Jsonrpc.Packet.Notification
      (Lsp.Server_notification.to_jsonrpc notif_server)
end

(** Corresponds to
   ```
   interface ProofStateMarker {
     range: vscode.Range;
     state: string;
     hover: string;
   }
   ```
*)
module TlapsProofStateMarker : sig
  type t

  val make : range:LspT.Range.t -> state:string -> hover:string -> t
  val yojson_of_t : t -> Yojson.Safe.t
end = struct
  type t = {
    range : LspT.Range.t;
    state : string; (* TODO: Rename to status. *)
    hover : string;
  }

  let make ~range ~state ~hover = { range; state; hover }

  let yojson_of_t (t : t) =
    `Assoc
      [
        ("range", LspT.Range.yojson_of_t t.range);
        ("state", `String t.state);
        ("hover", `String t.hover);
      ]
end
