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
    let hyps = M_t.hyps_of_modunit
        (noprops mu) in
    Dq.append_list cx hyps


class map =
    (* Shallow mapping of modules.

    The methods of this class do not
    traverse expressions,
    only module units.
    The methods can be overridden to
    traverse also expressions.
    *)
    object (self: 'self)

    method tla_modules_root mods =
        (* Wrapper of method `tla_modules`. *)
        let cx = Deque.empty in
        let _, mods = self#tla_modules
            cx mods in
        mods

    method tla_module_root module_ =
        (* Wrapper of method `tla_module`. *)
        let cx = Deque.empty in
        let _, module_ = self#tla_module
            cx module_ in
        module_

    method tla_modules cx mods =
        let step (cx, out_modules) module_ =
            let cx, module_ = self#tla_module
                cx module_ in
            let out_modules =
                module_ :: out_modules in
            (cx, out_modules) in
        let init = (cx, []) in
        let cx, mods = List.fold_left
            step init mods in
        let mods = List.rev mods in
        (cx, mods)

    method tla_module cx module_ =
        let module_units = module_.core.body in
        let cx, module_units =
            self#module_units
                cx module_units in
        let module_ = {module_.core with
            body=module_units} @@ module_ in
        (cx, module_)

    method module_units cx units =
        List.fold_left_map
            self#module_unit cx units

    method module_unit
            (cx: ctx)
            (mu: M_t.modunit) =
        let cx, core =
            match mu.core with
            (* Declarations *)
            | Constants decls ->
                self#constants cx decls
            | Variables names ->
                self#variables cx names
            | Recursives decls ->
                self#recursives cx decls
            (* Definitions *)
            | Definition (
                    df, wd, vsbl, local) ->
                self#definition
                    cx df wd vsbl local
            (* Theorems and proofs *)
            | Axiom (
                    name, expr) ->
                self#axiom cx name expr
            | Theorem (
                    name, sq, naxs,
                    pf, orig_pf, summ) ->
                self#theorem
                    cx name sq naxs
                    pf orig_pf summ
            | Mutate (
                    change, usable) ->
                self#mutate
                    cx change usable
            (* Modules and instances *)
            | Submod tla_module ->
                self#submod cx tla_module
            | Anoninst (
                    inst, local) ->
                self#anoninst
                    cx inst local
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

    method definition
            cx df wd vsbl local =
        (* TODO: assumes that
        `INSTANCE` statements
        have been expanded *)
        let mu = Definition (
            df, wd, vsbl, local) in
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

    method theorem
            cx name sq naxs
            pf orig_pf summ =
        (* add the hypotheses of the
        theorem to the context `cx` *)
        let mu = Theorem (
            name, sq, naxs,
            pf, orig_pf, summ) in
        (* add a fact for the theorem, and,
        if named, then also a definition,
        to the context `cx`
        *)
        let cx = update_cx cx mu in
        (cx, mu)

    method mutate cx change usable =
        let mu = Mutate (
            change, usable) in
        let cx = update_cx cx mu in
        (cx, mu)

    method submod cx tla_module =
        let mu = Submod tla_module in
        (cx, mu)

    method anoninst cx inst local =
        let mu = Anoninst (inst, local) in
        (cx, mu)

end


class deep_map =
    (* Deep mapping of modules.

    The methods of this class
    traverse expressions.
    *)
    object (self: 'self)
    inherit map as m_super
    inherit [unit]
        Proof.Visit.map as p_super

    method definition
            cx df wd vsbl local =
        let scx = ((), cx) in
        let _, dfs = self#defns scx [df] in
        let df = match dfs with
            | df :: _ -> df
            | [] -> failwith "unexpected case"
            in
        let mu = Definition (
            df, wd, vsbl, local) in
        let cx = update_cx cx mu in
        (cx, mu)

    method axiom cx name expr =
        let scx = ((), cx) in
        let expr = self#expr scx expr in
        let mu = Axiom (name, expr) in
        let cx = update_cx cx mu in
        (cx, mu)

    method theorem
            cx name sq naxs
            pf orig_pf summ =
        let scx = ((), cx) in
        let scx, sq = self#sequent
            scx sq in
        let pf = self#proof scx pf in
        (* NOTE: `orig_pf` is not mapped *)
        let mu = Theorem (
            name, sq, naxs,
            pf, orig_pf, summ) in
        let cx = update_cx cx mu in
        (cx, mu)

    method mutate cx change usable =
        let scx = ((), cx) in
        let usable = self#usable scx usable in
        let mu = Mutate (change, usable) in
        let cx = update_cx cx mu in
        (cx, mu)

    method submod cx tla_module =
        let cx, tla_module = self#tla_module
            cx tla_module in
        let mu = Submod tla_module in
        (cx, mu)

    method anoninst cx inst local =
        let scx = ((), cx) in
        let inst = self#instance scx inst in
        let mu = Anoninst (inst, local) in
        (* NOTE: `inst_sub` expressions mapped,
        not full instantiation, so `cx` unchanged. *)
        (cx, mu)
end
