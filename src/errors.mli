(*
 * Copyright (C) 2011  INRIA and Microsoft Corporation
 *)

open Property;;

exception Fatal;;

val info : ?at:('a wrapped) -> ('b, unit, string, unit) format4 -> 'b;;
(* Informational message: print on console, but do not display in a
   toolbox window.
 *)

val warn : ?at:('a wrapped) -> ('b, unit, string, unit) format4 -> 'b;;
(* Warning: print on console, and store for printing with the obligation
   in the toolbox message, but do not pop up a window.
 *)

val get_warnings : unit -> string;;
(* Get the stored warnings so far and empty the store. *)

val set_warnings : string -> unit;;
(* Reset the warnings store to a previous state. *)

val err : ?at:('a wrapped) -> ('b, unit, string, unit) format4 -> 'b;;
(* Error: print on console, pop up a window if toolbox mode. *)

val fatal : ?at:('a wrapped) -> ('b, unit, string, 'c) format4 -> 'b;;
(* Fatal error: print on console, pop up a window if toolbox mode,
   raise Fatal.
 *)

val bug : ?at:('a wrapped) -> string -> 'b;;
(* Bug: this is equivalent to assert false but prints the given information
   before raising Assert_failure.
 *)


(********** old stuff ********* FIXME remove **********)

val loc : string option ref;;
val msg : string option ref;;
val warning : bool ref;;        (* FIXME remove this obsolete variable *)
val set : 'a Property.wrapped -> string -> unit;;
