type transport = Stdio | Socket of int

(**
Here we serve the LSP RPC over TCP.
This module contains only the generic server-related functions,
the tlapm-specifics is moved to tlapm_lsp_packets.
*)

val run :
  transport -> bool -> Eio_unix.Stdenv.base -> string Eio.Std.Promise.t -> unit
