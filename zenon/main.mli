(*  Copyright 2000 INRIA  *)

val argspec : (Arg.key * Arg.spec * Arg.doc) list;;
val parse_command_line : (Arg.key * Arg.spec * Arg.doc) list -> unit;;
val do_main : unit -> unit;;
