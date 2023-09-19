module EioLspServer : sig
  val run : Eio_unix.Stdenv.base -> string Eio.Std.Promise.t -> unit
end