val check_multiline_diff :
  title:string -> expected:string -> actual:string -> unit

val check_multiline_diff_td :
  title:string -> expected:string -> actual:Lsp.Text_document.t -> unit
