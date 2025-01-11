open Prover

type t = Proved | Failed | Omitted | Missing | Pending | Progress
[@@deriving show]

let of_tlapm_obl_state = function
  | Toolbox.ToBeProved -> Progress
  | Toolbox.BeingProved -> Progress
  | Toolbox.Normalized -> Progress
  | Toolbox.Proved -> Proved
  | Toolbox.Failed -> Failed
  | Toolbox.Interrupted -> Failed
  | Toolbox.Trivial -> Proved
  | Toolbox.Unknown _ -> Failed

let to_string = function
  | Proved -> "proved"
  | Failed -> "failed"
  | Omitted -> "omitted"
  | Missing -> "missing"
  | Pending -> "pending"
  | Progress -> "progress"

let to_message = function
  | Failed -> "Proof failed."
  | Missing -> "Proof missing."
  | Omitted -> "Proof omitted."
  | Progress -> "Proving in progress."
  | Pending -> "Proof pending."
  | Proved -> "Proof checked successfully."

(** For a proof step, we will take the maximum of statuses returned by different
    provers for each obligation and the minimum across the obligations. *)
let to_order = function
  | Pending -> 0
  | Failed -> 1
  | Missing -> 2
  | Omitted -> 3
  | Progress -> 4
  | Proved -> 5

let of_order = function
  | 0 -> Pending
  | 1 -> Failed
  | 2 -> Missing
  | 3 -> Omitted
  | 4 -> Progress
  | 5 -> Proved
  | _ -> failwith "Impossible order"

let bot = Pending
let top = Proved
let min a b = of_order (min (to_order a) (to_order b))
let max a b = of_order (max (to_order a) (to_order b))
let yojson_of_t t = `String (to_string t)

let is_diagnostic = function
  | Failed -> true
  | Missing -> false
  | Omitted -> false
  | Progress -> false
  | Pending -> false
  | Proved -> false
