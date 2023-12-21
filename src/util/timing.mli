(*
 * Copyright (C) 2011  INRIA and Microsoft Corporation
 *)

(**********************************************)
(* Simple timers *)

type timer
(** The time of running timers. Note that timers are just data structures,
    when a timer is not needed any more, you don't need to do anything to
    release it. *)

val start_timer: unit -> timer
(** Allocate and start a new timer. *)

val get_timer: timer -> float
(** Return the elapsed time for the given timer. *)

(**********************************************)
(* Old clock stuff (remove?) *)

type clock = {
  desc : string;         (** description string *)
  mutable time : float;  (** cumulative time *)
  mutable count : int;   (** number of time this clock was started *)
}
(** The type of clocks. *)

val start: clock -> unit
(** [start c]
    Stop the current clock and start clock [c]. *)

val stop: unit -> unit
(** Stop the current clock and start the ambient clock. *)

val new_clock: string -> clock
(** [new_clock desc] Create a new clock with description [desc] and
    both counters at 0. Do not start the new clock, do not change the
    running clock. *)

val total: string -> clock
(** [total desc]
    Create a new clock with description [desc], time initialized to
    the total running time of the program up to now, and count
    initialized to 0. Do not start the new clock, do not change the
    running clock. *)

val ambient: clock
(** The default clock that runs before any other clock is started.
    It also runs when [stop] is called. *)

val string_of_clock: clock -> string
(** [string_of_clock c]
    Return a printable representation of [c] that includes its description
    and current total time. *)
