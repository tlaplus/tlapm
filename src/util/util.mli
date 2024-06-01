(*
 * util.mli --- format utilities
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

(** A collection of utilities *)

open Property

(** {3 Locations} *)

val locate      : 'a -> Loc.locus -> 'a wrapped
val location    : ?cap:bool -> 'a wrapped -> string

val get_locus   : 'a wrapped -> Loc.locus
val query_locus : 'a wrapped -> Loc.locus option
val set_locus   : 'a wrapped -> Loc.locus -> 'a wrapped

(** {3 Hinting and collections of hints} *)

type hint = string wrapped
type hints = hint list

val pp_print_hint : Format.formatter -> hint -> unit

module Coll : sig
  module Im : Map.S with type key = int
  module Sm : Map.S with type key = string
  module Hm : Map.S with type key = hint

  module Is : Set.S with type elt = int
  module Ss : Set.S with type elt = string
  module Hs : Set.S with type elt = hint

  module Sh : Weak.S with type data = string
end

(** {3 Printing with locations} *)

val sprintf :
  ?debug:string -> ?at:('a wrapped) -> ?prefix:string -> ?nonl:unit ->
  ('r, Format.formatter, unit, string) Stdlib.format4 -> 'r
val printf  :
  ?debug:string -> ?at:('a wrapped) -> ?prefix:string -> ?nonl:unit ->
  ('r, Format.formatter, unit) Stdlib.format -> 'r
val eprintf :
  ?debug:string -> ?at:('a wrapped) -> ?prefix:string -> ?nonl:unit ->
  ('r, Format.formatter, unit) Stdlib.format -> 'r
val fprintf :
  ?debug:string -> ?at:('a wrapped) -> ?prefix:string -> ?nonl:unit ->
  Format.formatter ->
  ('r, Format.formatter, unit) Stdlib.format -> 'r

(** {3 Convenience functions for exceptions} *)

exception Bug
val bug: ?at:('a wrapped) -> string -> 'failure

exception Not_implemented
val not_implemented: ?at:('a wrapped) -> string -> 'failure

(** {3 File and object checksumming} *)

type csum
val checksum: string -> csum
val pp_print_csum: Format.formatter -> csum -> unit

(** {3 Text wrangling} *)

val plural: ?ending:string -> int -> string -> string
val line_wrap: ?cols:int -> string -> string

(** {3 Misc} *)

val heap_stats: unit -> unit
val temp_file:
    (unit -> unit) ref -> string -> string * out_channel
(** [temp_file clean_hook suffix]
    Create a temporary file, return its name and an output channel to it.
    Add to [clean_hook] a clean-up action that closes the out_channel
    and removes the file.
*)

val rm_temp_file: string -> unit
(** Remove the given temporary file unless debugging "tempfiles" *)

val add_hook: (unit -> unit) ref -> ('a -> unit) -> 'a -> unit
(** [add_hook cleanup fn argument]
    Adds to [cleanup] the action of calling [fn argument] before doing
    whatever was in [cleanup] already.
*)

exception Internal_timeout
(** exception raised by the timer interrupt handler to prevent looping within
    PM code. *)

val run_with_timeout: float -> ('a -> 'b) -> 'a -> 'b option
(** [run_with_timeout tmo f x]
    Run [f] with argument [x], with a time limit of [tmo]. Return
    [Some result] if [f] managed to finish before the timeout, or
    [None] if it didn't. *)
