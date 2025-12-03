val check_multiline_diff :
  title:string -> expected:string -> actual:string -> unit

val check_multiline_diff_td :
  title:string -> expected:string -> actual:Lsp.Text_document.t -> unit

val lsp_init : unit -> Test_lsp_client.t
val lsp_stop : Test_lsp_client.t -> unit

val lsp_ca :
  lsp:Test_lsp_client.t ->
  ?name:string ->
  text:string ->
  line:int ->
  string ->
  Lsp.Text_document.t
