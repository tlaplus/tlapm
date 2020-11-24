(*
    expr/e_substitutive.mli --- compute substitutivity information
*)
open Property

open E_t


type substitutive_args = bool array


val substitutive_arg: substitutive_args pfuncs
val has_substitutive: 'a Property.wrapped -> bool
val get_substitutive: 'a Property.wrapped -> substitutive_args
val get_substitutive_arg: 'a Property.wrapped -> int -> bool

val compute_subst: ctx -> expr -> expr
