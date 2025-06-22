(*
 * loc.mli --- source locations
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

(** Source locations *)

(** A location represents a col in a source file *)
type pt_ = { line : int ;  (* line number *)
              bol : int ;  (* beginning of line *)
              col : int ;  (* column number relative to beginning of line,
                see the implementation of the function `locus_of_position`. *)
            }

type pt = Actual of pt_ | Dummy

(** A location that is always invalid (but both = and == itself). *)
val dummy : pt

(** The line number of the location, starting from 1. Raises [Failure
    "Loc.line"] if the location is a dummy. *)
val line : pt -> int

(** The column number of the location, starting from 1. Raises
    [Failure "Loc.col"] if the location is a dummy. *)
val column : pt -> int

(** The character offset of a location in a file. Raises [Failure
    "Loc.point"] if the location is a dummy. *)
val offset : pt -> int

(** String representation of a location. The [file] argument is by
    default "<nofile>". *)
val string_of_pt : ?file:string -> pt -> string

(** The area of a locus is the space between [start] and [end],
    excluding both. *)
type locus = {
  start : pt ;
  stop  : pt ;
  file  : string ;
}

(** left edge *)
val left_of : locus -> locus

(** right edge *)
val right_of : locus -> locus

(** A bogus locus *)
val unknown : locus

(** Convert a [Lexing.position] to a [locus] of 0 width. *)
val locus_of_position : Lexing.position -> locus

(** Merge two loci. Raises [Failure "Loc.merge"] if the loci are in
    different files. *)
val merge : locus -> locus -> locus

(** String representation of a locus. Capitalize the first word in the
    result iff [cap] is true (the default). *)
val string_of_locus : ?cap:bool -> locus -> string

(** String representation of a locus without filename. *)
val string_of_locus_nofile : locus -> string

(** Compact representation of a locus without a file. *)
val pp_locus_compact : Format.formatter -> locus -> unit
val pp_locus_compact_opt : Format.formatter -> locus option -> unit

(** Comparing loci *)
val compare : locus -> locus -> int
