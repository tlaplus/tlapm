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
    object (self : 'self)

    method module_units cx tla_module =
        (* The context `cx` would be relevant for modules that extend modules
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
        (* TODO: assumes that `INSTANCE` statements have been expanded *)
        let mu = Definition (df, wd, vsbl, local) in
        let cx = update_cx cx mu in
        (cx, mu)

    method axiom cx name expr =
        let mu = Axiom (name, expr) in
        (* add a fact for the axiom, and, if named, then also a definition,
        to the context `cx`
        *)
        let cx = update_cx cx mu in
        (cx, mu)

    method theorem cx name sq naxs pf orig_pf summ =
        (* add the hypotheses of the theorem to the context `cx` *)
        let mu = Theorem (name, sq, naxs, pf, orig_pf, summ) in
        (* add a fact for the theorem, and, if named, then also a definition,
        to the context `cx`
        *)
        let cx = update_cx cx mu in
        (cx, mu)

    method mutate cx change usable =
        let mu = Mutate (change, usable) in
        (* TODO: change the visibility of facts in `cx` based on the
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



let format_thm_name name_opt =
    match name_opt with
    | None -> ""
    | Some name ->
        "\"Name\": \"" ^
            name.core ^ "\", "


class json_map =
    (* Map module to JSON string.

    The methods of this class
    traverse expressions too.
    *)
    object (self: 'self)
    inherit [unit] Proof.Visit.json_map as super

    method module_units cx tla_module =
        let json = [] in
        let init = (cx, json) in
        let fold (cx, new_module) mu =
            let (cx, mu) = self#module_unit cx mu in
            let json = List.append json [mu] in
            (cx, json) in
        let (cx, json) = List.fold_left
            fold init tla_module in
        let json = Fmtutil.join "" json in
        (cx, json)

    method module_unit
            (cx: ctx)
            (mu: M_t.modunit) =
        let (cx, json) =
            match mu.core with
            | Constants decls ->
                self#constants cx decls
            | Variables names ->
                self#variables cx names
            | Recursives decls ->
                self#recursives cx decls
            | Definition (df, wd, vsbl, local) ->
                self#definition cx df wd vsbl local
            | Axiom (name, expr) ->
                self#axiom cx name expr
            | Theorem (name, sq, naxs, pf, orig_pf, summ) ->
                self#theorem cx name sq naxs pf orig_pf summ
            | Mutate (change, usable) ->
                self#mutate cx change usable
            | Submod tla_module ->
                self#submod cx tla_module
            | Anoninst (inst, local) ->
                self#anoninst cx inst local
            in
        (cx, json)

    method constants cx decls =
        let json = decls
            |> List.map Expr.Visit.format_parameter
            |> Fmtutil.comma in
        let json = "{\"CONSTANT\": [" ^ json ^ "]}" in
        let mu = Constants decls in
        let cx = update_cx cx mu in
        (cx, json)

    method variables cx names =
        let mapper name = "\"" ^ name.core ^ "\"" in
        let json = names
            |> List.map mapper
            |> Fmtutil.comma in
        let json = "" ^ json ^ "]}" in
        let mu = Variables names in
        let cx = update_cx cx mu in
        (cx, json)

    method recursives cx decls =
        let json = decls
            |> List.map Expr.Visit.format_parameter
            |> Fmtutil.comma in
        let mu = Recursives decls in
        let cx = update_cx cx mu in
        (cx, json)

    method definition cx df wd vsbl local =
        let json = match df.core with
            | Recursive (name, shape) ->
                failwith "not implemented"
            | Operator (name, expr) ->
                let scx = ((), cx) in
                let expr = self#expr scx expr in
                ("{\"==\": {" ^
                    "\"Name\": \"" ^ name.core ^
                        "\", " ^
                    "\"Expr\": " ^ expr ^
                "}}")
            | Instance (name, inst) ->
                let scx = ((), cx) in
                let expr = self#instance scx inst in
                ("{\"==\": {" ^
                    "\"Name\": \"" ^ name.core ^
                        "\", " ^
                    "\"Expr\": " ^ expr ^
                "}}")
            | Bpragma (name, expr, args) ->
                (* TODO: format backend pragmas ? *)
                let scx = ((), cx) in
                let expr = self#expr scx expr in
                ("{\"==\": {" ^
                    "\"Name\": \"" ^ name.core ^
                        "\", " ^
                    "\"Expr\": " ^ expr ^
                "}") in
        let mu = Definition (df, wd, vsbl, local) in
        let cx = update_cx cx mu in
        (cx, json)

    method axiom cx name expr =
        let scx = ((), cx) in
        let expr_json = self#expr scx expr in
        let name_json = format_thm_name name in
        let json = (
            "{\"AXIOM\": {" ^
                name_json ^
                "\"Expr\": " ^ expr_json ^
            "}}") in
        let mu = Axiom (name, expr) in
        let cx = update_cx cx mu in
        (cx, json)

    method theorem
            cx name sq naxs
            proof orig_pf summ =
        let scx = ((), cx) in
        let name_json = format_thm_name name in
        let sq_json = self#sequent scx sq in
        let proof_json =
            let scx = Expr.Visit.adjs
                scx (Deque.to_list sq.context) in
            self#proof scx proof in
        let json = (
            "{\"THEOREM\": {" ^
                name_json ^
                "\"Expr\": " ^ sq_json ^
                "\"PROOF\": " ^ proof_json ^
            "}}") in
        let mu = Theorem (
            name, sq, naxs, proof,
            orig_pf, summ) in
        let cx = update_cx cx mu in
        (cx, json)

    method mutate cx change usable =
        (* TODO *)
        (cx, "")

    method submod cx tla_module =
        let name = tla_module.core.name in
        let extendees = tla_module.core.extendees in
        let extendees_json = extendees
            |> List.map (fun s -> s.core)
            |> Fmtutil.comma in
        let modunits = tla_module.core.body in
        let _, modunits_json = self#module_units
            cx modunits in
        let json = (
            "{\"MODULE\": {" ^
                "\"Name\": \"" ^ name.core ^
                    "\", " ^
                "\"EXTENDS\": [" ^ extendees_json ^
                    "], " ^
                "\"Units\": " ^ modunits_json ^
            "}}") in
        (cx, json)

    method anoninst cx inst local =
        failwith "not implemented"
end


let json_of_module cx (tla_module: mule) =
    let visitor = new json_map in
    let _, json = visitor#submod cx tla_module in
    json
