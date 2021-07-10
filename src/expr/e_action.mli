(*
 * expr/e_action.mli --- expand action operators using quantification
 *
 *
 *)
open E_t


val expand_definition:
    hyp -> expr ->
    active_expansion:bool ->
    opname:string ->
    pfdirective:string ->
        expr
val var_to_fresh: int -> string -> string
val invert_renaming: ctx -> expr -> expr
val expand_definitions:
    ctx -> expr ->
    expand_enabled:bool ->
    expand_cdot:bool ->
    autouse:bool ->
        expr
val expand_propositional_action_operators: expr -> expr
val implication_to_enabled: ctx -> expr -> expr
val lambdify:
    ctx -> expr ->
    lambdify_enabled:bool ->
    lambdify_cdot:bool ->
    autouse:bool ->
        expr
val quantify:
    ctx -> expr ->
    expand_enabled:bool ->
    expand_cdot:bool ->
        expr
val expand_action_operators:
    ctx -> expr ->
    expand_enabled:bool ->
    expand_cdot:bool ->
    autouse:bool ->
        expr
