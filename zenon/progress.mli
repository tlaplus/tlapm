(*  Copyright 2005 INRIA  *)

type progress = No | Bar | Msg;;
val level : progress ref;;
val do_progress : (unit -> unit) -> char -> unit;;
val end_progress : string -> unit;;
