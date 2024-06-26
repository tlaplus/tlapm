(* Parser of expressions.

Copyright (C) 2008-2010  INRIA and Microsoft Corporation
*)
open Tla_parser
open E_t


type boundeds
val has_tuply_bounded:
    boundeds -> bool
val tuply_bounds_of_boundeds:
    boundeds -> tuply_bounds
val bounds_of_boundeds:
    boundeds -> bounds
val quantifier_boundeds:
    bool -> (pcx, boundeds) P.prs
val colon_expr:
    bool -> (pcx, expr) P.prs
val expr : bool -> expr lprs
val bounds : bool -> bound list lprs
val defn : bool -> defn lprs
val instance : bool -> instance lprs
val subst : bool -> (Util.hint * expr) list lprs
val hyp : bool -> hyp lprs
val sequent : bool -> sequent lprs
val opdecl : (Util.hint * shape) lprs
