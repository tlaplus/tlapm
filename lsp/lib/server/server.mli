(** Here we serve the LSP RPC over TCP. This module contains only the generic
    server-related functions. *)

type transport = Stdio | Socket of int

val run :
  transport -> bool -> Eio_unix.Stdenv.base -> string Eio.Std.Promise.t -> unit
