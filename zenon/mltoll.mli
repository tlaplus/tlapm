(*  Copyright 2004 INRIA  *)

val translate : string -> Phrase.phrase list -> Mlproof.proof -> Llproof.proof;;

val is_meta : string -> bool;;
val get_meta_type : string -> string;;
