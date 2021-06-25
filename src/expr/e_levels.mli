(* Compute expression levels. *)
open Property

open E_t
open E_visit


module StringSet: Set.S with type elt = string


type level_info = LevelInfo of int * bool list * StringSet.t


val exprlevel: level_info pfuncs
val has_level: 'a Property.wrapped -> bool
val rm_level: 'a Property.wrapped -> 'a Property.wrapped
val get_level_info: 'a Property.wrapped -> level_info
val get_level: 'a Property.wrapped -> int
val get_level_weights: 'a Property.wrapped -> bool list
val get_level_args: 'a Property.wrapped -> StringSet.t
val assert_has_correct_level: expr -> unit
val kind_to_level: kind -> int


class virtual ['s] level_computation : ['s] E_visit.map
class virtual ['s] _rm_expr_level : ['s] E_visit.map_visible_hyp

val compute_level: ctx -> expr -> expr
val rm_expr_level: ctx -> expr -> expr
