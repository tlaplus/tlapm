module Server : sig
  type transport = Stdio | Socket of int

  val run :
    transport ->
    bool ->
    Eio_unix.Stdenv.base ->
    string Eio.Std.Promise.t ->
    unit
end
