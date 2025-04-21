val find_ranges :
  Range.t -> Tlapm_lib.Module.T.mule -> (string * int * Range.t list) option
(** Find ranges related to the step at the cursor position. *)

val step_label : string -> int -> string
val step_label_range : Range.t -> int -> Range.t
