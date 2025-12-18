(* Command-line arguments to `tlapm`.

Copyright (C) 2011  INRIA and Microsoft Corporation
*)

(** Given the executable name and an array of command-line arguments, parses
    those arguments then either sets associated values in the Params module
    or directly takes action such as printing out file contents or deleting
    directories. Returns a list of files for proof checking. The optional
    arguments are used for unit tests.
*)
val init: ?out:Format.formatter -> ?err:Format.formatter -> ?terminate:(int -> unit) -> string -> string array -> string list
