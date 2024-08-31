(* Visitor class for module syntax graphs.

Based on the modules:
    - `Expr.Visit`
    - `Module.Elab`
    - `Module.T`

*)
open Expr.T
open Property

open M_t


module Dq = Deque


let update_cx (cx: ctx) mu =
    let hyps = M_t.hyps_of_modunit (noprops mu) in
    Dq.append_list cx hyps


class map =
    object (self: 'self)

    method module_units cx tla_module =
        (* The context `cx` would be relevant for
        modules that extend modules
        or for submodules.
        *)
        let new_module = [] in
        let init = (cx, new_module) in
        let f (cx, new_module) mu =
            let (cx, mu) = self#module_unit cx mu in
            let new_module = List.append new_module [mu] in
            (cx, new_module) in
        let (cx, new_module) = List.fold_left
            f init tla_module in
        (cx, new_module)

    method module_unit (cx: ctx) (mu: M_t.modunit) =
        let (cx, core) = match mu.core with
        (* Declarations *)
        | Constants decls -> self#constants cx decls
        | Variables names -> self#variables cx names
        | Recursives decls -> self#recursives cx decls
        (* Definitions *)
        | Definition (df, wd, vsbl, local) ->
            self#definition cx df wd vsbl local
        (* Theorems and proofs *)
        | Axiom (name, expr) -> self#axiom cx name expr
        | Theorem (name, sq, naxs, pf, orig_pf, summ) ->
            self#theorem cx name sq naxs pf orig_pf summ
        | Mutate (change, usable) -> self#mutate cx change usable
        (* Modules and instances *)
        | Submod tla_module -> self#submod cx tla_module
        | Anoninst (inst, local) -> self#anoninst cx inst local
        in
        (cx, core @@ mu)

    method constants cx decls =
        let mu = Constants decls in
        let cx = update_cx cx mu in
        (cx, mu)

    method variables cx names =
        let mu = Variables names in
        let cx = update_cx cx mu in
        (cx, mu)

    method recursives cx decls =
        let mu = Recursives decls in
        let cx = update_cx cx mu in
        (cx, mu)

    method definition cx df wd vsbl local =
        (* TODO: assumes that `INSTANCE` statements
        have been expanded *)
        let mu = Definition (df, wd, vsbl, local) in
        let cx = update_cx cx mu in
        (cx, mu)

    method axiom cx name expr =
        let mu = Axiom (name, expr) in
        (* add a fact for the axiom, and,
        if named, then also a definition,
        to the context `cx`
        *)
        let cx = update_cx cx mu in
        (cx, mu)

    method theorem cx name sq naxs pf orig_pf summ =
        (* add the hypotheses of the
        theorem to the context `cx` *)
        let mu = Theorem (name, sq, naxs, pf, orig_pf, summ) in
        (* add a fact for the theorem, and,
        if named, then also a definition,
        to the context `cx`
        *)
        let cx = update_cx cx mu in
        (cx, mu)

    method mutate cx change usable =
        let mu = Mutate (change, usable) in
        (* TODO: change the visibility of
        facts in `cx` based on the
        `Mutate` statement.
        *)
        (cx, mu)

    method submod cx tla_module =
        let mu = Submod tla_module in
        (cx, mu)

    method anoninst cx inst local =
        (* TODO: expand statements from `INSTANCE` *)
        let mu = Anoninst (inst, local) in
        (cx, mu)

end
