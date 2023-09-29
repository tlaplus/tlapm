type t

val create :
  Eio.Switch.t ->
  Eio__.Fs.dir_ty Eio.Path.t ->
  Eio_unix.Process.mgr_ty Eio.Process.mgr ->
  Tlapm_lsp_docs.t ->
  t

val start_async :
  t -> Tlapm_lsp_docs.tk -> int -> int -> int -> (t, string) result
