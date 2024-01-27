module LspT = Lsp.Types

let opt_str o = match o with None -> `Null | Some s -> `String s

(** Corresponds to
    ```
    export interface CountByStepStatus {
      proved: number;
      failed: number;
      omitted: number;
      missing: number;
      pending: number;
      progress: number;
    }
    ```
*)
module CountByStepStatus = struct
  type t = {
    proved : int;
    failed : int;
    omitted : int;
    missing : int;
    pending : int;
    progress : int;
  }

  let make ~proved ~failed ~omitted ~missing ~pending ~progress =
    { proved; failed; omitted; missing; pending; progress }

  let yojson_of_t (t : t) =
    `Assoc
      [
        ("proved", `Int t.proved);
        ("failed", `Int t.failed);
        ("omitted", `Int t.omitted);
        ("missing", `Int t.missing);
        ("pending", `Int t.pending);
        ("progress", `Int t.progress);
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
    role : string;
    range : LspT.Range.t;
    normalized : string option;
    results : TlapsProofObligationResult.t list;
  }

  let make ~role ~range ~normalized ~results =
    { role; range; normalized; results }

  let yojson_of_t (t : t) =
    `Assoc
      [
        ("role", `String t.role);
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
    status: string;
    location: Location;
    obligations: TlapsProofObligationState[];
    sub_count: CountByStepStatus;
  }
  ```
*)
module TlapsProofStepDetails = struct
  type t = {
    kind : string;
    status : string;
    location : LspT.Location.t;
    obligations : TlapsProofObligationState.t list;
    sub_count : CountByStepStatus.t;
  }

  let make ~kind ~status ~location ~obligations ~sub_count =
    { kind; status; location; obligations; sub_count }

  let yojson_of_t (t : t option) =
    match t with
    | None -> `Null
    | Some t ->
        `Assoc
          [
            ("kind", `String t.kind);
            ("status", `String t.status);
            ("location", LspT.Location.yojson_of_t t.location);
            ( "obligations",
              `List
                (List.map TlapsProofObligationState.yojson_of_t t.obligations)
            );
            ("sub_count", CountByStepStatus.yojson_of_t t.sub_count);
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
   interface ProofStepMarker {
     status: string;
     range: vscode.Range;
     hover: string;
   }
   ```
*)
module TlapsProofStepMarker : sig
  type t

  val make : status:string -> range:LspT.Range.t -> hover:string -> t
  val yojson_of_t : t -> Yojson.Safe.t
end = struct
  type t = { status : string; range : LspT.Range.t; hover : string }

  let make ~status ~range ~hover = { status; range; hover }

  let yojson_of_t (t : t) =
    `Assoc
      [
        ("status", `String t.status);
        ("range", LspT.Range.yojson_of_t t.range);
        ("hover", `String t.hover);
      ]
end
