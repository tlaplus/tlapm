type t

val run : string -> t
val close : t -> unit
val send_packet : t -> Jsonrpc.Packet.t -> unit
val send_request : t -> 'a Lsp.Client_request.t -> Jsonrpc.Id.t
val send_notification : t -> Lsp.Client_notification.t -> unit
val recv_packet : t -> Jsonrpc.Packet.t option
val recv_response : ?log:bool -> t -> Jsonrpc.Id.t -> Jsonrpc.Json.t
val call : t -> 'a Lsp.Client_request.t -> Jsonrpc.Json.t
val call_init : t -> Lsp.Types.InitializeResult.t
val print_stderr : t -> unit
val next_id : t -> Jsonrpc.Id.t
