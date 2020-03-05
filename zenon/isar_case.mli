(*  Copyright 2009 INRIA  *)

(* Utility for printing and proving the lemmas for the CASE rule
   for the Isar format output.
   Also for the recordset intro rule.
*)

val print_case : string -> int -> bool -> out_channel -> unit;;

val print_record : string -> int -> out_channel -> unit;;
