module StepInfo : sig
  type t = { name : string; label_offset : int; step_ranges : Range.t list }

  val matching_range : t -> Range.t -> Range.t option
  (** Returns a range where the step was mentioned and matches the specified
      range. *)

  val step_label : t -> string
  (** Returns the label part of the step. *)

  val step_label_range : t -> Range.t -> Range.t
  (** Returns a label part range of a step. The range must be one of the step
      ranges. *)
end

val find_ranges : Range.t -> Tlapm_lib.Module.T.mule -> StepInfo.t option
(** Find ranges related to the step at the cursor position. *)
