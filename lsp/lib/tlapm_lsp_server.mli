type transport = Stdio | Socket of int

(**
Here we serve the LSP RPC over TCP.
This module contains only the generic server-related functions.
*)

val run :
  transport -> bool -> Eio_unix.Stdenv.base -> string Eio.Std.Promise.t -> unit
