module TL = Tlapm_lib
open TL.Proof.T
open TL.Expr.T

let noprops = TL.Property.noprops

(** Usable, but cannot be used if left empty. *)
let empty : usable = { facts = []; defs = [] }

let add_steps (step_names : stepno list) (usable : usable) : usable =
  let new_facts =
    List.map (fun sn -> Opaque (string_of_stepno sn) |> noprops) step_names
  in
  { usable with facts = List.append usable.facts new_facts }

let add_defs new_defs usable : usable =
  { usable with defs = List.append usable.defs new_defs }

let add_defs_str def_names usable : usable =
  let new_defs =
    def_names |> List.map @@ fun def_name -> Dvar def_name |> noprops
  in
  add_defs new_defs usable

let add_defs_from_pf (pf : proof) usable : usable =
  match pf.core with
  | By ({ defs; _ }, _) -> { usable with defs = List.append usable.defs defs }
  | Obvious | Omitted _ | Steps (_, _) | Error _ -> usable
