open Tlapm_lib

module StepInfo : sig
  type t = {
    name : string;
    target_name : string;
    prefix_len : int;
    ranges : Range.t list;
  }
  [@@deriving show]
end

val find_ranges : Range.t -> Module.T.mule -> StepInfo.t list
