open Expr.T
open Proof.T
open Util

open M_t


class map: object
    method module_units: Expr.T.ctx -> M_t.modunit list ->
        ctx * M_t.modunit list
    method module_unit: ctx -> M_t.modunit ->
        ctx * modunit
    method constants: ctx -> (hint * shape) list ->
        ctx * modunit_
    method variables: ctx -> hints ->
        ctx * modunit_
    method recursives: ctx -> (hint * shape) list ->
        ctx * modunit_
    method definition: ctx -> defn -> wheredef -> visibility -> export ->
        ctx * modunit_
    method axiom: ctx -> hint option -> expr ->
        ctx * modunit_
    method theorem:
        ctx -> hint option -> sequent -> int -> proof -> proof -> summary ->
        ctx * modunit_
    method submod: ctx -> mule ->
        ctx * modunit_
    method mutate: ctx -> [`Use of bool | `Hide] -> usable ->
        ctx * modunit_
    method anoninst: ctx -> Expr.T.instance -> export ->
        ctx * modunit_
    method tla_module:
        ctx -> mule -> ctx * mule
    method tla_module_root:
        mule -> mule
    method tla_modules:
        ctx -> mule list -> ctx * mule list
    method tla_modules_root:
        mule list -> mule list
end


class deep_map: object
    inherit map
    inherit [unit] Proof.Visit.map
end
