(*  Copyright 2005 INRIA  *)

val warn :
  (Phrase.phrase * bool) list -> Llproof.proof Lazy.t -> string list -> unit
;;
val warn_unused_var : (Phrase.phrase * bool) list -> unit;;
