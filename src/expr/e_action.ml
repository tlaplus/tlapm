(*
 * expr/e_action.ml --- expand action operators using quantification
 *)


(*


References
==========

[1] Leslie Lamport, Specifying Systems, Addison-Wesley, 2002
    https://lamport.azurewebsites.net/tla/book.html

[2] Leslie Lamport, TLA+ Version 2: A Preliminary Guide, 2018
    https://lamport.azurewebsites.net/tla/tla2-guide.pdf

[3] Leslie Lamport, TLA+2: A Preliminary Guide, 2014

[4] Leslie Lamport, Proving safety properties, 2019
    https://lamport.azurewebsites.net/tla/proving-safety.pdf

[5] Leslie Lamport, LevelSpec specification, from the repository `tlaplus` at:
    https://github.com/tlaplus/tlatools/src/tla2sany/semantic/LevelNode.java

*)



open Ext
open Property

module Subst = E_subst
module T = E_t
open E_t
module Visit = E_visit


type set = (string, unit) Hashtbl.t
let temp_bound = "_"
type bounds = (set * int) option
let param_name = "r#"
let enabled_op_name = "EnabledWrapper"
    (* occurrences need to be renamed below if renamed here *)
let cdot_op_name = "CdotWrapper"
    (* occurrences need to be renamed below if renamed here *)
let enabled_cdot_to_op_name op =
    match op with
    | Internal ENABLED -> enabled_op_name
    | Internal Cdot -> cdot_op_name
    | _ -> assert false


(* Stores whether a (`\E` quantifier) node resulted from an `ENABLED` node. *)
let is_enabled : bool pfuncs =
    Property.make "Expr.Action.is_enabled"
(* Stores whether a (`\E` quantifier) node resulted from a `\cdot` node. *)
let is_cdot : bool pfuncs =
    Property.make "Expr.Action.is_cdot"
(* Stores the name of the variable that was replaced. *)
let variable_name : string pfuncs =
    Property.make "Expr.Action.variable_name"
(* `is_enabled` functions *)
let has_is_enabled x = Property.has x is_enabled
let get_is_enabled x = Property.get x is_enabled
let rm_is_enabled x = Property.remove x is_enabled
(* `is_cdot` functions *)
let has_is_cdot x = Property.has x is_cdot
let get_is_cdot x = Property.get x is_cdot
let rm_is_cdot x = Property.remove x is_cdot
(* `variable_name` functions *)
let has_variable_name x = Property.has x variable_name
let get_variable_name x = Property.get x variable_name
let rm_variable_name x = Property.remove x variable_name


let assert_level_bounds (level: int) =
    assert ((level = 1) || (level = 2))
let init_level level init_value =
    (* initialize level to `init_value`,
    or minimum of `init_value` and `level`,
    if already initialized.
    *)
    match level with
    | None -> Some init_value
    | Some level ->
        assert_level_bounds level;
        Some (min init_value level)
let dec_level = function
    (* decrement level value by 1, with minimum 1 *)
    | None -> None
    | Some level ->
        assert_level_bounds level;
        Some (max 1 (level - 1))


exception SoundnessCheck


let expand_definition hyp expr
        ~(active_expansion: bool)
        ~(opname: string)
        ~(pfdirective: string) =
    let df = match hyp.core with
        | Defn (df, _, _, _) -> df
        | _ -> assert false
        in
    let (name, def_expr) = match df.core with
        | Operator (name, def_expr)
        | Bpragma (name, def_expr, _) -> name.core, def_expr
        | _ -> assert false
        in
    let hyp_locus = E_t.format_locus hyp in
    let expr_locus = E_t.format_locus expr in
    let msg = (
        "Hidden definition of operator `" ^ name ^ "` needs expansion " ^
        "for soundly expanding " ^ opname ^ " " ^
        "(using rigid quantification).\n" ^
        "The expansion of " ^ opname ^ " has been activated with the " ^
        pfdirective ^ " from the module `TLAPS`.\n" ^
        "The operator `" ^ name ^ "` is defined at: \n\t" ^ hyp_locus ^
        "\nand the operator `" ^ name ^ "` occurs at: \n\t" ^ expr_locus ^
        "\nUsing the proof directive `AutoUSE` from " ^
        "the module `TLAPS`, or `BY DEF " ^ name ^
        "` is expected to avoid this error.\n"
        ) in
    if (not active_expansion) then
        begin
        (Util.eprintf ~at:expr "%s" msg);
        failwith msg  (* SoundnessCheck *)
        end;
    Util.printf ~at:expr ~prefix:"[INFO]: "
        "Auto-expanding the definition of operator:  %s\n" name;
    match expr.core with
        | Apply ({core=Ix n}, args) ->
            let op_expr = Subst.app_expr (Subst.shift n) def_expr in
            let new_core = Subst.normalize op_expr args in
            new_core @@ expr
        | Ix n ->
            let e_ = Subst.app_expr (Subst.shift n) def_expr in
            e_.core @@ expr
        | _ -> assert false


class auto_expansion_of_defs =
    object (self: 'self)
    inherit [int option] Visit.map_visible_hyp as super

    val mutable active_expansion: bool = false
    val mutable _expand_enabled: bool = false
    val mutable _expand_cdot: bool = false

    method expand
            (cx: E_t.ctx)
            (e: E_t.expr)
            ~(expand_enabled: bool)
            ~(expand_cdot: bool)
            ~(autouse: bool) =
            (* calling with `autouse=false` is useful for
            invoking the soundness checks *)
        active_expansion <- autouse;
        _expand_enabled <- expand_enabled;
        _expand_cdot <- expand_cdot;
        let level = None in
        let scx = (level, cx) in
        self#expr scx e

    method expr (((level: int option), cx) as scx) e =
        let (opname, pfdirective) = match (_expand_enabled, _expand_cdot) with
            | (false, false) -> assert false
            | (true, false) -> (
                    "the operator `ENABLED`",
                    "`ExpandENABLED` proof directive")
            | (false, true) -> (
                    "the operator `\\cdot`",
                    "`ExpandCdot` proof directive")
            | (true, true) -> (
                    "the operators `ENABLED` and `\\cdot`",
                    "the proof directives `ExpandENABLED` and `ExpandCdot`") in
        let expand_def hyp expr = expand_definition
            hyp expr
            ~active_expansion:active_expansion
            ~opname:opname
            ~pfdirective:pfdirective
            in
        match e.core with
        (* Assume that if an occurrence of `ENABLED` or `\cdot` has already
        been lambdified, then all occurrences of `ENABLED` and `\cdot` in its
        scope have been lambdified.

        This case arises when sequents from instantiated theorems are
        given to `lambdify` for a second time.

        Recursing here leads to encountering the newly introduced `LAMBDA`
        parameters, which are declared with kind `Unknown`.

        An alternative approach (and more representative of the information
        available in the syntax graph) is to declare in the first pattern
        case the `Lambda` parameters as `Fresh` with `Constant` as `kind`.
        Doing so avoids the errors when occurrences of these parameters are
        encountered within the expression that is the argument of the `LAMBDA`.

        Also, this is the only case of an occurrence of `LAMBDA` where the
        recursion could proceed inside the `LAMBDA` without first expanding
        the operator that takes the `LAMBDA` as argument (and applying
        beta-reduction via `Expr.Subst.app_expr`).

        This case arises due to using `ENABLED` and `\cdot` as second-order
        operators (with the proof directive `Lambdify`).
        *)
        | Apply ({core=Internal (ENABLED | Cdot)},
                [{core=Lambda _}]) ->
            e
        | Apply ({core=Opaque s}, [{core=Lambda _}])
                when (s = enabled_op_name) || (s = cdot_op_name) ->
            e
        | Apply ({core=Internal Cdot} as op, [arg1; arg2]) ->
            begin match level with
                | None -> ()
                    (* outside of scope of active expansion. *)
                | Some _ ->
                    if (not _expand_cdot) then begin
                    Util.eprintf ~at:e "%s" (
                        "Nested occurrence of the operator `\\cdot` found " ^
                        "in scope of `ENABLED` when expanding `ENABLED`. " ^
                        "Using the proof directive `ExpandCdot` from " ^
                        "the module `TLAPS` is expected to avoid this error." ^
                        "For example, writing `BY ExpandCdot`.");
                    failwith "Expr.Action"
                    end;
                    assert _expand_cdot
                (* raise error if expansion of \cdot inactive *)
                (* this is a difference of a one-pass expansion before
                any expansions of operators, as compared to interleaving
                of expansions of nested operators and of definitions
                *)
                (* An alternative is to consider
                expansion of nested occurrences of `\cdot` as active
                when in the scope of an `ENABLED`. In this case,
                `init_level` unless `None` above and `not _expand_cdot`.
                *)
                (* If `not _expand_cdot`,
                then this call is from expansion of `ENABLED`,
                and in case level of `arg1` < 2,
                then sound to not expand `\cdot`. *)
            end;
            (* `arg1` *)
            (* same effect on level as `ENABLED`
            *)
            (* The value `level = 1` results from a prime.
            `\cdot` has level 2, so cannot be primed,
            but can occur as `ENABLED ( (ENABLED (A \cdot B))' )`.
            The outer `ENABLED` initializes `level = 2`, and the
            prime changes this to `level = 1`.
            *)
            (* The same algorithm works if `A \cdot B` could
            appear primed. *)
            if _expand_cdot then
                begin
                let level_arg1 = init_level level 2 in
                let scx_ = (level_arg1, cx) in
                let arg1_ = self#expr scx_ arg1 in
                (* `arg2` *)
                let level_arg2 = Some 1 in
                    (* could be optimized by tracking presence of
                    unprimed variables *)
                let scx_ = (level_arg2, cx) in
                let arg2_ = self#expr scx_ arg2 in
                (* result *)
                Apply (op, [arg1_; arg2_]) @@ e
                end
            else
                begin
                let arg1_ = self#expr scx arg1 in
                let arg2_ = self#expr scx arg2 in
                Apply (op, [arg1_; arg2_]) @@ e
                end
        | Apply ({core=Internal ENABLED} as op, [arg]) ->
            begin match level with
                | None -> ()
                | Some _ ->  (* see comments for `\cdot` *)
                    if (not _expand_enabled) then begin
                    Util.eprintf ~at:e "%s" (
                        "Nested occurrence of the operator `ENABLED` found " ^
                        "in scope of `\\cdot` when expanding `\\cdot`. " ^
                        "Using the proof directive `ExpandENABLED` from " ^
                        "the module `TLAPS` is expected to avoid this error." ^
                        "For example, writing `BY ExpandENABLED`.");
                    failwith "Expr.Action"
                    end;
                    assert _expand_enabled
                    (* If `not _expand_enabled`,
                    then this call is from expansion of `\cdot`,
                    and in case not in unprimed scope and `arg` of level 2,
                    then sound to not expand `ENABLED`.
                    *)
            end;
            if _expand_enabled then
                begin
                let level_arg = init_level level 2 in
                let scx_ = (level_arg, cx) in
                let arg_ = self#expr scx_ arg in
                Apply (op, [arg_]) @@ e
                end
            else
                begin
                let arg_ = self#expr scx arg in
                Apply (op, [arg_]) @@ e
                end
        | Apply ({core=Internal Prime} as op, [arg]) ->
            let level_arg = dec_level level in
            let scx_ = (level_arg, cx) in
            let arg_ = self#expr scx_ arg in
            Apply (op, [arg_]) @@ e
        | Apply ({core=Internal UNCHANGED} as op, [arg]) ->
            let level_arg = dec_level level in
            let scx_ = (level_arg, cx) in
            let arg_ = self#expr scx_ arg in
            Apply (op, [arg_]) @@ e
        | Sub (modal_op, action, subscript) ->
            let level_action = level in
            let scx_ = (level_action, cx) in
            let action_ = self#expr scx_ action in
            (* count as prime *)
            let level_subscript = dec_level level in
            let scx_ = (level_subscript, cx) in
            let subscript_ = self#expr scx_ subscript in
            (* result *)
            Sub (modal_op, action_, subscript_) @@ e
        | Apply ({core=Ix n}, _)
        | Ix n ->
            assert (n >= 1);
            begin match level with
            | None -> e
            | Some level_bound -> begin
                E_levels.assert_has_correct_level e;
                let e_level = E_levels.get_level e in
                let hyp = E_t.get_val_from_id cx n in
                begin match hyp.core with
                | Fresh (op_name, shape, kind, _) ->
                    (* parameter of unspecified expression level occurs in
                    a scope where operators may need expansion
                    (depending on their expression level) ?
                    *)
                    if kind = Unknown then
                        let arity = E_t.shape_to_arity shape in
                        let msg = (
                            "Declared operator `" ^ op_name.core ^
                            "` has unknown level and occurs within the " ^
                            "scope of `ENABLED` or `\\cdot` where " ^
                            "soundness requires expanding expressions " ^
                            "of level >= " ^ (string_of_int level_bound) ^
                            ".\n" ^
                            "If a constant operator is substituted for " ^
                            "this operator, then the expression that " ^
                            "results from applying " ^
                            "this declared operator has expression level " ^
                            (string_of_int e_level) ^
                            ".\n May need expansion. " ^
                            "A declared operator cannot be expanded.\n" ^
                            "The operator `" ^ op_name.core ^
                            "` is declared at:\n" ^ (format_locus hyp) ^
                            "\n and has arity: " ^ (string_of_int arity)
                            )
                            in
                        Util.eprintf ~at:e "%s" msg;
                    assert (kind <> Unknown)
                | _ -> () end;
                if (e_level >= level_bound) then
                    (* expand *)
                    begin
                    assert (e_level <= 2);
                    match hyp.core with
                        | FreshTuply _
                        | Fact _ -> assert false
                        | Flex _  -> assert (e.core = Ix n); e
                        | Fresh (op_name, shape, kind, _) ->
                            (* Note: Even if the declared operator
                            has lower level than the level of expression `e`,
                            we cannot expand the operator in the expression,
                            because this is a declared operator.
                            *)
                            let arity = E_t.shape_to_arity shape in
                            let op_level = E_levels.kind_to_level kind in
                                (* see assertion above that
                                `kind <> Unknown`
                                *)
                            let msg = (
                                "The expression that results from applying " ^
                                "the declared operator `" ^
                                op_name.core ^ "` has expression level " ^
                                (string_of_int e_level) ^ " within the " ^
                                "scope of `ENABLED` or `\\cdot` where " ^
                                "soundness requires expanding expressions " ^
                                "of level >= " ^ (string_of_int level_bound) ^
                                ". A declared operator cannot be expanded.\n" ^
                                "The operator `" ^ op_name.core ^
                                "` is declared at:\n" ^ (format_locus hyp) ^
                                "\n and has level: " ^
                                (string_of_int op_level) ^
                                "\n and arity: " ^ (string_of_int arity)
                                )
                                in
                            Util.eprintf ~at:e "%s" msg;
                            (* raise SoundnessCheck *)
                            failwith msg
                                (* because:
                                    assert (e_level < level_bound) *)
                        | Defn (df, _, visibility, scope) ->
                            let e_ = expand_def hyp e in
                            let e_ = noprops e_.core in
                            let e_ = E_levels.rm_expr_level cx e_ in
                            let e_ = E_levels.compute_level cx e_ in
                            self#expr scx e_
                    end
                else
                    begin
                    e
                    end
                end
            end
        | _ -> super#expr scx e
end


let expand_definitions cx e
        ~(expand_enabled: bool)
        ~(expand_cdot: bool)
        ~(autouse: bool) =
    (* Expand definitions with one traversal of the syntax tree,
    by propagating the least level of expressions that need to be
    expanded. `ENABLED` sets this to `min(current, 2)`,
    same for the first argument of `\cdot`,
    the second argument of `\cdot` sets this to 1, and
    `prime` reduces the level to 1 by `max(current - 1, 1)`.
    *)
    let visitor = new auto_expansion_of_defs in
    visitor#expand cx e
        ~expand_enabled:expand_enabled
        ~expand_cdot:expand_cdot
        ~autouse:autouse


let expand_propositional_action_operators e =
    (* Expand the operators `UNCHANGED`, `[A]_v`, `<<A>>_v`
    by calling the function `Expr.Tla_norm.rewrite_unch` that
    rewrites `UNCHANGED` using prime and propositional logic.
    *)
    match e.core with
    | Apply ({core=Internal Builtin.UNCHANGED}, [a]) ->
        E_tla_norm.rewrite_unch a
    | Sub (Box, a, b) ->
        begin
            let op = Internal Builtin.Disj @@ e in
            let unchanged = E_tla_norm.rewrite_unch b in
            let args = [a; unchanged] in
            Apply (op, args) @@ e
        end
    | Sub (Dia, a, b) ->
        begin
            let op = Internal Builtin.Conj @@ e in
            let unchanged = E_tla_norm.rewrite_unch b in
            let changed =
                let op = Internal Builtin.Neg @@ e in
                Apply (op, [unchanged]) @@ e in
            let args = [a; changed] in
            Apply (op, args) @@ e
        end
    | _ ->
        Util.eprintf ~at:e "unexpected action operator to expand\n";
        assert false


let var_to_fresh
        (nesting: int)
        (name: string):
            string =
    (* Return a fresh identifier for a constant bound by `\E`. *)
    assert (nesting >= 0);
    (* "enabled" is used here both for constants bound by quantifiers
    that are introduced for representing `ENABLED`, and
    for constants bound by quantifiers that are introduced for
    representing `\cdot`.
    *)
    name ^ "#enabled#prime" ^ (string_of_int nesting)


let flex_to_fresh_opaque
        (nesting: int)
        (cx: T.ctx)
        (e: expr)
        (h: set):
            expr =
    (* Return fresh constant as `Opaque`, if `e` references a variable.
    Store the name of the fresh constant in `h`.
    *)
    assert (nesting >= 1);
    let n = match e.core with
        | Ix n -> assert (n >= 1); n
        | _ -> assert false
        in
    let hyp = T.get_val_from_id cx n in
    match hyp.core with
        | Flex name ->
            let fresh = var_to_fresh nesting name.core in
            if not (Hashtbl.mem h fresh) then
                Hashtbl.add h fresh ();
            let expr = Opaque fresh @@ e in  (* could use `noprops` *)
            assign expr variable_name name.core
        | Fact _ -> assert false
        | _ -> e


let apply_conj (args: expr list): expr = match args with
    (* Conjoin `args`. Return head if `args` is a singleton. *)
    | [] -> assert false
    | [arg] -> arg
    | _ ->
        (*
        let op = noprops (Internal Conj) in
        let conj = Apply (op, args) in
        *)
        let conj = List (And, args) in
        noprops conj


let annotate_bounds bounds signature =
    let params = List.map (fun (p, _) -> p) signature in
    let annotate_bound (bound: E_t.bound) (h: Util.hint) =
        let name = E_t.name_of_bound bound in
        assert (has_variable_name h);
        let flex_name = get_variable_name h in
        let name = assign name variable_name flex_name in
        let bound = Visit.rename_bound bound name in
        bound in
    List.map2 annotate_bound bounds params


(* This implementation of `make_quantifier` differs in that that shifting of
indices is applied after all new quantifiers have been introduced,
by calling the function `shift_indices` below, instead of calling the
function `app_expr` when each quantifier is introduced, which would
result in quadratic (instead of linear) time complexity.
*)
let make_quantifier
        (fresh_names: string list)
        (expr: expr):
            expr =
    (* Return quantified expression `\E fresh_names:  expr`. *)
    if (List.length fresh_names) = 0 then
        expr  (* no bound constants *)
    else begin
        let temp_names = temp_bound :: fresh_names in
        let bounds = E_t.From_string.make_const_decls temp_names in
        (*
        (* This call to `app_expr` is present in `Expr.Action` and
        `Expr.Action_iter`.
        The effect of this call to `app_expr` is obtained by calling the
        function `shift_indices` below and the method `E_anon.anon#expr`
        from the method `expansion_of_action_operators#expand` below.
        *)
        let n_bounds = List.length bounds in
        let new_expr = app_expr (shift n_bounds) expr in
        let core = Quant (Exists, bounds, new_expr) in
        *)
        let core = Quant (Exists, bounds, expr) in
        noprops core
        (* TODO: consider representing as a location that
            this node replaces an expression `Apply (op, expr)`. *)
    end


class check_arity =
    object (self: 'self)
    inherit [unit] Visit.iter_visible_hyp as super

    method expr (((), cx) as scx) e =
        match e.core with
        | Apply ({core=Internal Cdot}, [arg]) ->
            (match arg.core with
                | Lambda _ -> ()
                | _ ->
                    E_t.print_cx cx;
                    print_string (E_fmt.string_of_expr cx arg);
                    assert false)
        | _ -> super#expr scx e
end


class commute_exists_disjunction =
    object (self: 'self)
    inherit [unit] Visit.map_visible_hyp as super

    method expr (((), cx) as scx) e =
        match e.core with
        | Quant (Exists, bounds, expr) ->
            begin match expr.core with
            | List (Or, exprs) ->
                let exprs_ = List.map
                    (fun x -> Quant (Exists, bounds, x) @@ e) exprs in
                let e_ = List (Or, exprs_) @@ expr in
                self#expr scx e_
            | Apply ({core=Internal Disj} as op, exprs) ->
                assert ((List.length exprs) = 2);
                let exprs_ = List.map
                    (fun x -> Quant (Exists, bounds, x) @@ e) exprs in
                let e_ = Apply (op, exprs_) @@ expr in
                self#expr scx e_
            | _ -> super#expr scx e end
        | _ -> super#expr scx e
end


let commute_exists_disjunction cx expr =
    let visitor = new commute_exists_disjunction in
    visitor#expr ((), cx) expr


class inverse_mapping =
    object (self: 'self)
    inherit [unit] Visit.map_visible_hyp as super

    method expr (((), cx) as scx) e =
        match e.core with
        | Quant (Exists, bounds, expr) when has_is_enabled e ->
            (* map `bounds_` *)
            let rename_bound bound =
                let name = E_t.name_of_bound bound in
                assert (has_variable_name name);
                let flex_name = get_variable_name name in
                let flex_name = List.hd (String.split_on_char '#' flex_name) in
                let flex_name = flex_name ^ "__Primed" in
                let new_name = noprops flex_name in
                (* Could assign param name.
                The param name is known by the index in the parameter list,
                so normalization of signature could be re-applied.
                *)
                Visit.rename_bound bound new_name in
            let bounds_ = List.map rename_bound bounds in
            (* `expr` has indices referring to the bounds,
            so no renaming needed there
            *)
            Quant (Exists, bounds_, expr) @@ e
        | _ -> super#expr scx e
end


let invert_renaming cx expr =
    let visitor = new inverse_mapping in
    let expr_ = visitor#expr ((), cx) expr in
    commute_exists_disjunction cx expr_


let mk_lambda_signature
        (fresh_names: string list):
            (Util.hint * shape) list =
    let mk_parameter name =
        let h = noprops name in
        let shp = Shape_expr in
        (h, shp) in
    List.map mk_parameter fresh_names


let make_lambda
    (fresh_names: string list)
    (expr: expr):
        expr =
    if (List.length fresh_names) = 0 then begin
        (* quantify over a constant that does not occur in `expr`,
        to in all cases return a `Lambda` (with nonempty signature).
        Returning a `Lambda` signifies that lambdification has occurred.

        `expr` may include operators that could be substituted by variables.

        Currently, this case would raise an error in definition expansion.
        The case of length 0 means that no variables have been bound in `expr`,
        so it would be sound to not raise errors for occurrences of operators.

        (Also, for the case of instantiation, if the variables bound in `expr`
        could not occur in expressions substituted for operators within the
        instantiating module, then it would be sound to not raise errors for
        operators in definition expansion.)

        Using a `Lambda` in the case of length 0 signifies that if variables
        occur in operator substitutions, binding and replacement by quantifiers
        would be needed.

        Returning in all cases a `Lambda` reduces the number of pattern cases
        needed for detecting lambdified forms.
        *)
        let temp_names = [temp_bound; param_name ^ "0"] in
        let signature = mk_lambda_signature temp_names in
        let core = Lambda (signature, expr) in
        noprops core
            (* when binding primed variables before instantiation,
            this trasformation occurs even when `ExpandENABLED` and
            `ExpandCdot` are not given by the user.

            So the operators `ENABLED` and `\cdot` remain then in place
            even if there are no primed/unprimed variable occurrences to bind,
            because lambdification keeps the operators until
            replacement by quantification, which is active only if
            `ExpandENABLED` or `ExpandCdot` are given by the user.
            *)
        end
    else begin
        let temp_names = temp_bound :: fresh_names in
            (* `temp_bound` used to avoid double index shifts in
            `shift_indices_after_lambdify` *)
        let signature = mk_lambda_signature temp_names in
        let core = Lambda (signature, expr) in
        noprops core
    end


let lambdify_action_operator
        (op: expr)
        (fresh_names: string list)
        (expr: expr):
            expr_ =
    begin match op.core with
        | Internal (ENABLED | Cdot) -> ()
        | _ -> assert false
    end;
    let lambda_expr = make_lambda fresh_names expr in
    let core = Apply (op, [lambda_expr]) in
    core


class shift_indices_after_lambdify =
    object (self: 'self)
    inherit Subst.map_visible_hyp as super

    method expr
            (s: Subst.sub)
            (oe: expr):
                expr =
        match oe.core with
        | Apply ({core=Internal (ENABLED | Cdot)} as op,
                [{core=Lambda ((nm, _) :: signature, expr)}])
                    when nm.core = temp_bound ->
            let n = List.length signature in
            assert (n >= 1);
            let s = Subst.compose s (Subst.shift n) in
            let expr_ = self#expr s expr in
            let lambda = Lambda (signature, expr_) in
            let expr_ = noprops lambda in
            let core = Apply (op, [expr_]) in
            noprops core
        | Apply ({core=Internal (ENABLED | Cdot)},
                [{core=Lambda _}]) ->  (* avoid duplicating index shifts *)
            oe
        | Apply ({core=Internal (ENABLED | Cdot)}, _) -> assert false
        | _ -> super#expr s oe
end


let shift_indices_after_lambdify (e: expr): expr =
    (* Wraps the class `shift_indices_after_lambdify`. *)
    let visitor = new shift_indices_after_lambdify in
    let s = Subst.shift 0 in
    visitor#expr s e


let normalize_lambda_signature signature keep_same_names =
    let n = List.length signature in
    assert (n >= 1);
    let names = List.init n (fun i -> param_name ^ string_of_int i) in
    let params = List.map (fun (p, _) -> p.core) signature in
    let mk_parameter name flex_name =
        let h = noprops name in
        (* store name for inverse renaming *)
        let h = assign h variable_name flex_name in
        let shp = Shape_expr in
        (h, shp) in
    if keep_same_names then
        List.map2 mk_parameter params params
    else
        List.map2 mk_parameter names params


class normalize_lambda_param_names =
    (* Rename the bound variables using indexing by position in signature.

    This renaming is applied after anonymization to ensure that the names
    collected in `Lambda` signatures match the opaque names introduced in
    place of primed occurrences of `VARIABLES`.

    When using only lambdification (without replacement by quantifiers),
    this parameter name normalization is sound for occurrences of `ENABLED`
    and `\cdot` that are not nested.
    *)
    object (self: 'self)
    inherit [unit] Visit.map_visible_hyp as super

    val mutable _keep_same_names: bool = true

    method config keep_same_names =
        _keep_same_names <- keep_same_names

    method expr
            (((), (cx: T.ctx)) as scx)
            (e: expr):
                expr =
        match e.core with
        | Apply ({core=Internal (ENABLED | Cdot)} as op,
                [{core=Lambda (signature, expr)}]) ->
            let (fst, _) = List.hd signature in
            assert (fst.core <> temp_bound);
            let expr_ = self#expr scx expr in
            let signature = normalize_lambda_signature
                signature _keep_same_names in
            let lambda = Lambda (signature, expr_) in
            let expr_ = noprops lambda in
            (* without renaming, even without coalescing,
            the operator `ENABLED` is unsupported by first-order backends.
            *)
            let op_name = enabled_cdot_to_op_name op.core in
                (* This substitution also ensures arity correctness of
                applications of the operator `Internal Cdot`.
                Otherwise, errors would be raised at assertions about arity.
                *)
            let op = Opaque op_name @@ op in
            let core = Apply (op, [expr_]) in
            noprops core
        | Apply ({core=Internal (ENABLED | Cdot)}, _) -> assert false
        | _ -> super#expr scx e
end


(* Binding or lambdification step  --->  Replacement by quantifiers step *)


class lambdify_action_operators =
    object (self: 'self)
    inherit [bounds * bounds] Visit.map_visible_hyp as super

    val mutable _lambdify_enabled: bool = false
    val mutable _lambdify_cdot: bool = false

    (* This class does not introduce quantifiers, it only binds occurrences
    of variables in the scope of primes within `ENABLED` and the first
    argument of `\cdot`, and outside primes within the second argument of
    `\cdot`. The bound occurrences are represented as fresh identifiers,
    bound as `LAMBDA` parameters
    (in a traversal of the syntax graph, these parameters would be declared
    in the context as `Fresh` with kind `Constant`).

    The `LAMBDA` is introduced fresh, as the argument of `ENABLED`,
    which is thus used as a second-order operator. In effect, the `ENABLED` is
    replaced with an (unexpanded) reference to the following first-order
    operator `ApplyE` that takes a single operator argument `Op` of
    unspecified arity >= 1, and quantifies existentially its parameters:

    (For the case of arity 0 (no primed variables in `ENABLED`, or
    no primed variables in the first argument of `\cdot` and no unprimed
    variables in the second argument of `\cdot`), the `ENABLED` or `\cdot`
    can be eliminated from the syntax graph.)

    ```tla
    ApplyE(Op(_, _, ...)) = \E c1, c2, ...:  Op(c1, c2, ...)
    ```

    The `Lambda` node introduced by this class formalizes the
    effect obtained by `"_"` in the class `expansion_of_action_operators`.
    The result is less efficient (by a constant), because of the additional
    nodes being created. The function `shift_indices` has been rewritten in
    the same way, detecting the pattern:

    ```ocaml
    Apply({core=Internal ENABLED}, [arg])
        when arg.core = Lambda (sig, expr)
    ```

    instead of a quantifier with `"_"` as first bound constant.
    The function result is the function `shift_indices_after_lambdify`
    that replaces the application and `Lambda` nodes with a `Quant` node.

    This arrangement of the two steps as binding of primed variables
    / lambdification (in effect alpha-conversion of primed variables) and
    quantification (in effect beta-reduction, when viewed as applying
    `ENABLED` to the `LAMBDA` argument) formalizes the transformation,
    and allows for moving the lambdification earlier, to apply it before
    instantiation (flattening of instance statements in `Module.Elab`.

    Lambdification before substitutions performed by instantiation is
    described in [1] for defining the meaning of instantiation
    (in particular of `ENABLED`, `\cdot`, and `-+->`
    when instantiating a module).

    The step that was shifting of indices, and the introduction of quantifiers
    need not be performed in one graph traversal. The shifting of indices is
    necessary to complete the lambdification, and forms a separate traversal
    only for reasons of efficiency (namely to reduce time complexity from
    quadratic to linear). So shifting of indices is performed as the last
    step of lambdification, without replacing `ENABLED` and `LAMBDA` by
    quantifiers (`Quant(Exists, ...)`).

    Replacement by quantifiers is described as a separate step in [1],
    and is performed in this way, after instantiation (substitutions)
    takes place, and after expanding all definitions as needed for soundness.

    Note that lambdification cannot occur without expansion of definitions,
    so the relevant soundness checks need to be performed before instantiation,
    and in all cases (so also when `ExpandENABLED` and `ExpandCdot` are not
    given by the user, which answers the question of whether ensuring soundness
    requires performing any soundness checks in all cases, even if
    substitutivity of operators is taken into account correctly for coalescing).

    The auto-expansion of definitions need not occur in all cases,
    but if not, then the soundness checks will raise an error before
    instantiation. The user will then need to provide the directive
    `AutoUSE`, even if the user does not provide `ExpandENABLED` or
    `ExpandCdot`. Rephrased, the user may need to expand definitions
    (and one way is to invoke `AutoUSE`) for lambdification, and not for
    replacement of `ENABLED` and `\cdot` by quantification.

    The quantification step then reduces to a single graph traversal that
    replaces all occurrences of `Apply({core=Internal ENABLED},
    [{core=Lambda (sig, expr)}])` with `Quant (Exists, bounds, expr)`.

    The lambdification step transforms an expression with `ENABLED` or
    `\cdot` to a constant-level expression, even without quantification.
    This change of expression level simplifies reasoning,
    because the `ENABLED` and `\cdot` from that point further could be
    regarded as constant operators.
    *)

    method expand
            (cx: T.ctx)
            (e: expr)
            ~(lambdify_enabled: bool)
            ~(lambdify_cdot: bool)
            ~(keep_same_names: bool):
                expr =
        _lambdify_enabled <- lambdify_enabled;
        _lambdify_cdot <- lambdify_cdot;
        let e_ =
            let scope = (None, None) in
            self#expr (scope, cx) e in
        let e_ = shift_indices_after_lambdify e_ in
        let e_ = E_anon.anon#expr ([], cx) e_ in
        let e_ =
            let visitor = new normalize_lambda_param_names in
            visitor#config keep_same_names;
            visitor#expr ((), cx) e_ in
        e_

    method expr (((a, b), cx) as scx) e =
        let get_depth = function
            | None -> 0
            | Some (_, depth) -> depth in
        let a_depth = get_depth a in
        let b_depth = get_depth b in
        let inscope = ((a, b) <> (None, None)) in
        assert (a_depth >= 0);
        assert (b_depth >= 0);
        assert ((not inscope) || a_depth <> b_depth);
        let depth = max a_depth b_depth in
        assert (depth >= 0);
        let depth_ = depth + 1 in
        assert (depth_ >= 1);
        let make_pair h = Some (h, depth_)
            in
        let recurse_ a b = function
            | None -> []
            | Some arg ->
                let scope = (a, b) in
                [self#expr (scope, cx) arg] in
        let expand arg1 arg2 op =
            let h: set = Hashtbl.create 16 in
                (* same set used for both arguments of `\cdot`,
                so that no need to compute a union of two sets
                that would result from recursing for the two arguments
                of `\cdot`.
                *)
            let t = make_pair h in
            let arg1_ = recurse_ a t arg1 in
            let arg2_ = recurse_ t b arg2 in
            let fresh_names = E_visit.set_to_list h in
            let expr = apply_conj (List.append arg1_ arg2_) in
            (* make_quantifier fresh_names expr *)
            let core = lambdify_action_operator op fresh_names expr in
            core @@ e  (* properties of `e` used because `op` below
                (`ENABLED` or `\cdot`) remains after lambdification.
                The operator is replaced when replacing by quantification.
                At that replacement `noprops` is used to annotate the
                quantifier syntax nodes.
                *)
            in
        match e.core with
        | Apply ({core=Internal (ENABLED | Cdot)},
                [{core=Lambda _}]) ->
            e
        | Apply ({core=Opaque s}, [{core=Lambda _}])
                when (s = enabled_op_name) || (s = cdot_op_name) ->
            e
        | Apply ({core=Internal ENABLED} as op, [arg1])
                when _lambdify_enabled ->
            expand (Some arg1) None op
        | Apply ({core=Internal Cdot} as op, [arg1; arg2])
                when _lambdify_cdot ->
            expand (Some arg1) (Some arg2) op
        | Apply ({core=Internal ENABLED}, _) when inscope ->
            (* Expansion of definitions is expected to have raised error
            for this case. *)
            assert ((not _lambdify_enabled) && (_lambdify_cdot));
            Util.eprintf ~at:e "%s" (
                "Nested occurrence of the operator `ENABLED` found " ^
                "in scope of `\\cdot` when expanding `\\cdot`. " ^
                "Using the proof directive `ExpandENABLED` from " ^
                "the module `TLAPS` is expected to avoid this error." ^
                "For example, writing `BY ExpandENABLED`.");
            failwith "Expr.Action"
        | Apply ({core=Internal Cdot}, _) when inscope ->
            (* Expansion of definitions is expected to have raised error
            for this case. *)
            assert ((not _lambdify_cdot) && (_lambdify_enabled));
            Util.eprintf ~at:e "%s" (
                "Nested occurrence of the operator `\\cdot` found " ^
                "in scope of `ENABLED` when expanding `ENABLED`. " ^
                "Using the proof directive `ExpandCdot` from " ^
                "the module `TLAPS` is expected to avoid this error. " ^
                "For example, writing `BY ExpandCdot`.");
            failwith "Expr.Action"
        | Apply ({core=Internal Prime} as op, [arg]) -> begin
            let arg_ =
                let scope = (b, None) in
                self#expr (scope, cx) arg in
            match b with
            | None -> Apply (op, [arg_]) @@ e
            | _ -> arg_  (* omit prime *)
            end
        | Ix n -> begin match a with
            | None -> e
            | Some (h, depth) -> assert (depth >= 1);
                flex_to_fresh_opaque depth cx e h
            end
        | Apply ({core=Internal UNCHANGED}, _)
        | Sub _  (* unexpanded outside scope of `ENABLED` and `\cdot` *)
                when inscope ->
            let e_ = expand_propositional_action_operators e in
            self#expr scx e_
        | Apply ({core=Opaque name}, _) ->
            Util.eprintf ~at:e
                "Named operator `%s` unexpected after anonymization."
                name;
            assert false
        | _ -> super#expr scx e
end


class replace_action_operators_with_quantifiers =
    object (self: 'self)
    inherit [bool] Visit.map_visible_hyp as super

    val mutable _expand_enabled: bool = false
    val mutable _expand_cdot: bool = false

    method replace cx expr
            ~(expand_enabled:bool)
            ~(expand_cdot:bool) =
        _expand_enabled <- expand_enabled;
        _expand_cdot <- expand_cdot;
        self#expr (false, cx) expr

    method expr ((scope, cx) as scx) e =
        let to_expand op =
            (_expand_enabled && (op = Internal ENABLED)) ||
            (_expand_cdot && (op = Internal Cdot)) in
        let inscope = scope in  (* for readability *)
        let replace_with_quantifier op_name signature expr =
            assert ((List.length signature) >= 1);
            let fresh_names = List.map (fun (h, _) -> h.core) signature in
            let bounds = E_t.From_string.make_const_decls fresh_names in
            let bounds = annotate_bounds bounds signature in
            let scope = true in
            let cx_ =
                let lambda_hyps = List.map
                    (fun (name, shp) ->
                        Fresh (name, shp, Unknown, Unbounded) @@ name)
                    signature in
                Deque.append_list cx lambda_hyps in
            let expr_ = self#expr (scope, cx_) expr in
            let core = Quant (Exists, bounds, expr_) in
            let expr_ = noprops core in
            let expr_ = if op_name = enabled_op_name then
                    assign expr_ is_enabled true
                else
                    assign expr_ is_cdot true
                in
            expr_ in
        match e.core with
        | Apply ({core=Opaque op_name},
                [{core=Lambda (signature, expr)}])
                    when _expand_enabled && (op_name = enabled_op_name) ->
            replace_with_quantifier op_name signature expr
        | Apply ({core=Opaque op_name},
                [{core=Lambda (signature, expr)}])
                    when _expand_cdot && (op_name = cdot_op_name) ->
            replace_with_quantifier op_name signature expr
        | Apply ({core=Ix n},
                [{core=Lambda (signature, expr)}])
                    when _expand_enabled || _expand_cdot ->
            let hyp = E_t.get_val_from_id cx n in
            begin match hyp.core with
            | Defn ({core=Operator (op_name, _)}, _, _, _)
                    when (op_name.core = enabled_op_name) ||
                         (op_name.core = cdot_op_name) ->
                    replace_with_quantifier op_name.core signature expr
            | _ -> super#expr scx e
            end
        | Apply ({core=((Internal (ENABLED | Cdot)) as op)},
                [{core=Lambda (signature, expr)}])
                    when to_expand op ->
            let op_name = enabled_cdot_to_op_name op in
            replace_with_quantifier op_name signature expr
        | Apply ({core=((Internal (ENABLED | Cdot)) as op)}, [arg])
                when to_expand op ->
            (* This pattern case corresponds to no occurrences of
            primed variables in `ENABLED`, or
            no occurrences of primed variables in the first argument of `\cdot`
            and no occurrences of unprimed variables in the second argument of
            `\cdot`.
            *)
            (* eliminate the operator `ENABLED` or `\cdot` *)
            let scope = true in
            self#expr (scope, cx) arg
        (* The warnings in the following two pattern cases are the same
        in the class `expansion_of_action_operators`.
        *)
        | Apply ({core=Internal ENABLED}, _) when inscope ->
            (* Expansion of definitions is expected to have raised error
            for this case. *)
            assert ((not _expand_enabled) && (_expand_cdot));
            Util.eprintf ~at:e "%s" (
                "Nested occurrence of the operator `ENABLED` found " ^
                "in scope of `\\cdot` when expanding `\\cdot`. " ^
                "Using the proof directive `ExpandENABLED` from " ^
                "the module `TLAPS` is expected to avoid this error." ^
                "For example, writing `BY ExpandENABLED`.");
            failwith "Expr.Action"
        | Apply ({core=Internal Cdot}, _) when inscope ->
            (* Expansion of definitions is expected to have raised error
            for this case. *)
            assert ((not _expand_cdot) && (_expand_enabled));
            Util.eprintf ~at:e "%s" (
                "Nested occurrence of the operator `\\cdot` found " ^
                "in scope of `ENABLED` when expanding `ENABLED`. " ^
                "Using the proof directive `ExpandCdot` from " ^
                "the module `TLAPS` is expected to avoid this error. " ^
                "For example, writing `BY ExpandCdot`.");
            failwith "Expr.Action"
        | _ -> super#expr scx e
end


class shift_indices =
    object (self: 'self)
    inherit Subst.map_visible_hyp as super
    (* Add to de Bruijn indices shift from newly introduced quantifiers. *)

    (* In the call to the normalization step in `Subst.map#expr`,
    in the pattern case for `Apply`, if `Lambda`s have been already normalized,
    then `self#expr` is not recursively called.
    *)

    method expr
            (s: Subst.sub)
            (oe: expr):
                expr =
        match oe.core with
        | Quant (Exists, (nm, _, _) :: bs, expr)
                when nm.core = temp_bound ->
            assert ((List.length bs) >= 1);
            let n = List.length bs in
            let s = Subst.compose s (Subst.shift n) in
            (*
            let oe_ = Quant (Exists, bs, expr) @@ oe in
            super#expr s oe_

            The above two lines were an error, because `super#expr`
            will modify only indices that are larger than `n`
            (see the first pattern case for `Bump` in `Expr.Subst.app_ix`),
            as if the indices were already counting the bounds in `bs`.
            This is due to the `bumpn n s` in `super#bounds`.
            *)
            (* `bs` is unchanged because there are no domain bounds in `bs`. *)
            (* Note that `self#expr` is called on `expr`,
            instead of `super#expr`. *)
            let expr_ = self#expr s expr in
            let core = Quant (Exists, bs, expr_) in
            noprops core
        | _ -> super#expr s oe
end


let shift_indices (e: expr): expr =
    (* Wraps the class `shift_indices`. *)
    let visitor = new shift_indices in
    let s = Subst.shift 0 in
    visitor#expr s e


(* Replace the operators `ENABLED` and `\cdot` with `\E` quantifiers. *)
class expansion_of_action_operators =
    object (self: 'self)
    inherit [bounds * bounds] Visit.map_visible_hyp as super

    val mutable _expand_enabled: bool = false
    val mutable _expand_cdot: bool = false

    method expand
            (cx: T.ctx)
            (e: expr)
            ~(expand_enabled: bool)
            ~(expand_cdot: bool):
                expr =
        assert (expand_enabled || expand_cdot);
        _expand_enabled <- expand_enabled;
        _expand_cdot <- expand_cdot;
        let e_ =
            let scope = (None, None) in
            self#expr (scope, cx) e in
        let e_ = shift_indices e_ in
        E_anon.anon#expr ([], cx) e_

    method expr (((a, b), cx) as scx) e =
        let get_depth = function
            | None -> 0
            | Some (_, depth) -> depth in
        let a_depth = get_depth a in
        let b_depth = get_depth b in
        let inscope = ((a, b) <> (None, None)) in
        assert (a_depth >= 0);
        assert (b_depth >= 0);
        assert ((not inscope) || a_depth <> b_depth);
        let depth = max a_depth b_depth in
        assert (depth >= 0);
        let depth_ = depth + 1 in
        assert (depth_ >= 1);
        let make_pair h = Some (h, depth_) in
        (*
        (* `recurse` is used by the commented pattern cases. *)
        let recurse a b arg =
            let scope = (a, b) in
            self#expr (scope, cx) arg in
        *)
        let recurse_ a b = function
            | None -> []
            | Some arg ->
                let scope = (a, b) in
                [self#expr (scope, cx) arg] in
        let expand arg1 arg2 =
            let h: set = Hashtbl.create 16 in
                (* same set used for both arguments of `\cdot`,
                so that no need to compute a union of two sets
                that would result from recursing for the two arguments
                of `\cdot`.
                *)
                (* (depth + 1) is needed in first argument because
                otherwise `ENABLED (x' /\ ENABLED x')` results in:
                `\E x#1:  x#1 /\ \E x#1:  x#1`
                because the incrementing would be performed only at primes.

                The depth is paired with the set of bounds because of
                the above example and the example
                `ENABLED (TRUE \cdot x')`
                which would increment depth in the second argument of `\cdot`,
                and then need to decrement depth in order to bind the `x'`
                correctly by `ENABLED`.
                *)
            let t = make_pair h in
            let arg1_ = recurse_ a t arg1 in
            let arg2_ = recurse_ t b arg2 in
            let fresh_names = E_visit.set_to_list h in
            let expr = apply_conj (List.append arg1_ arg2_) in
            make_quantifier fresh_names expr
            in
        match e.core with
        | Apply ({core=Internal ENABLED}, [arg1]) when _expand_enabled ->
            expand (Some arg1) None
        | Apply ({core=Internal Cdot}, [arg1; arg2]) when _expand_cdot ->
            expand (Some arg1) (Some arg2)
        (*
        (* This pattern case is equivalent to the first two cases. *)
        | Apply ({core=Internal ((ENABLED | Cdot) as op)}, arg1 :: args)
                when ((op = ENABLED) && _expand_enabled) ||
                     ((op = Cdot) && _expand_cdot) -> begin
            let h: set = Hashtbl.create 16 in
            let t = make_pair h in
            let arg1_ = recurse a t arg1 in
            let expr = match op with
                | ENABLED -> assert (args = []); arg1_
                | Cdot -> assert ((List.length args) = 1);
                    let arg2_ = recurse t b (List.hd args) in
                    apply_conj [arg1_; arg2_]
                | _ -> assert false in
            let fresh_names = E_visit.set_to_list h in
            make_quantifier fresh_names expr
            end
        *)
        (*
        (* This pattern case is equivalent to the first pattern case. *)
        | Apply ({core=Internal ENABLED}, [arg1])
                when _expand_enabled -> begin
            let h: set = Hashtbl.create 16 in
            let t = make_pair h in
            let expr = recurse a t arg1 in
            let fresh_names = E_visit.set_to_list h in
            make_quantifier fresh_names expr
            end
            (* Expression levels are not needed here,
            because definition expansion has been completed by this point.
            Level information could be removed or recomputed before returning
            from the root of the recursion.
            *)
        *)
        | Apply ({core=Internal ENABLED}, _) when inscope ->
            (* Expansion of definitions is expected to have raised error
            for this case. *)
            assert ((not _expand_enabled) && (_expand_cdot));
            Util.eprintf ~at:e "%s" (
                "Nested occurrence of the operator `ENABLED` found " ^
                "in scope of `\\cdot` when expanding `\\cdot`. " ^
                "Using the proof directive `ExpandENABLED` from " ^
                "the module `TLAPS` is expected to avoid this error." ^
                "For example, writing `BY ExpandENABLED`.");
            failwith "Expr.Action"
        (* This pattern case is equivalent to the second pattern case. *)
        (*
        | Apply ({core=Internal Cdot}, [arg1; arg2])
                when _expand_cdot -> begin
            let h: set = Hashtbl.create 16 in
            let t = make_pair h in
            let arg1_ = recurse a t arg1 in
            let arg2_ = recurse t b arg2 in
            let expr = apply_conj [arg1_; arg2_] in
            let fresh_names = E_visit.set_to_list h in
            make_quantifier fresh_names expr
            end
        *)
        (*
        (* This pattern case is equivalent to the second pattern case. *)
        | Apply ({core=Internal Cdot}, [arg1; arg2])
                when _expand_cdot -> begin
            let arg2_a: set = Hashtbl.create 16 in
            let arg1_b: set = Hashtbl.create 16 in
            (* replace primed vars in `arg1` *)
            let arg1_ = recurse a (make_pair arg1_b) arg1 in
            (* replace unprimed vars in `arg2` *)
            let arg2_ = recurse (make_pair arg2_a) b arg2 in
            let expr = apply_conj [arg1_; arg2_] in
            (* merge the sets `arg2_a` and `arg1_b` *)
            let union h1 h2 =
                let add x _ =
                    if not (Hashtbl.mem h1 x) then Hashtbl.add h1 x () in
                Hashtbl.iter add h2 in
            union arg2_a arg1_b;
            let fresh_names = E_visit.set_to_list arg2_a in
            (* replace `\cdot` with `\E` and conjunction *)
            make_quantifier fresh_names expr
            end
        *)
        | Apply ({core=Internal Cdot}, _) when inscope ->
            (* Expansion of definitions is expected to have raised error
            for this case. *)
            assert ((not _expand_cdot) && (_expand_enabled));
            Util.eprintf ~at:e "%s" (
                "Nested occurrence of the operator `\\cdot` found " ^
                "in scope of `ENABLED` when expanding `ENABLED`. " ^
                "Using the proof directive `ExpandCdot` from " ^
                "the module `TLAPS` is expected to avoid this error. " ^
                "For example, writing `BY ExpandCdot`.");
            failwith "Expr.Action"
        | Apply ({core=Internal Prime} as op, [arg]) -> begin
            let arg_ =
                let scope = (b, None) in
                self#expr (scope, cx) arg in
            match b with
            | None -> Apply (op, [arg_]) @@ e
            | _ -> arg_  (* omit prime *)
            end
        | Ix n -> begin match a with
            | None -> e
            | Some (h, depth) -> assert (depth >= 1);
                flex_to_fresh_opaque depth cx e h
            end
        | Apply ({core=Internal UNCHANGED}, _)
        | Sub _  (* unexpanded outside scope of `ENABLED` and `\cdot` *)
                when inscope ->
            let e_ = expand_propositional_action_operators e in
            self#expr scx e_
        | Apply ({core=Opaque name}, _) ->
            Util.eprintf ~at:e
                "Named operator `%s` unexpected after anonymization."
                name;
            assert false
        | _ -> super#expr scx e
end


let implication_to_enabled cx expr =
    let expr = E_levels.compute_level cx expr in
    let found = ref false in
    let found_a_type = ref false in
    let found_b_type = ref false in
    let check_context hyps a b rule =
        let a = Option.get a in
        let b = Option.get b in
        let visitor = object (self: 'self)
            inherit [unit] E_visit.iter_visible_hyp

            method hyp (((), cx2) as scx) h =
                let shift_n = (Deque.size hyps) - (Deque.size cx2) in
                let shift = E_subst.shift shift_n in
                begin match h.core with
                    | Fact (expr, Visible, _) ->
                        begin match expr.core with
                        | Apply ({core=Internal ENABLED}, [{core=
                                    Apply ({core=Internal Conj}, [p; q])
                                }]) when
                                    let p_ = E_subst.app_expr shift p in
                                    let q_ = E_subst.app_expr shift q in
                                    (E_eq.expr p_ a) && (E_eq.expr q_ b) &&
                                    (rule = "pconj")
                                ->
                            found := true
                        | Apply ({core=Internal ENABLED}, [{core=
                                    Apply ({core=Internal Disj}, [p; q])
                                }]) when
                                    let p_ = E_subst.app_expr shift p in
                                    let q_ = E_subst.app_expr shift q in
                                    (E_eq.expr p_ a) && (E_eq.expr q_ b) &&
                                    (rule = "abdisj")
                                ->
                            found := true
                        | Apply ({core=Internal Disj}, [
                                    {core=Apply ({core=Internal ENABLED}, [p])};
                                    {core=Apply ({core=Internal ENABLED}, [q])}
                                ]) when
                                    let p_ = E_subst.app_expr shift p in
                                    let q_ = E_subst.app_expr shift q in
                                    (E_eq.expr p_ a) && (E_eq.expr q_ b) &&
                                    (rule = "abdisj_inverse")
                                ->
                            found := true
                        | Apply ({core=Internal ENABLED}, [{core=
                                    Apply ({core=Internal Conj}, [p; q])
                                }]) when
                                    let p_ = E_subst.app_expr shift p in
                                    let q_ = E_subst.app_expr shift q in
                                    (E_eq.expr p_ a) && (E_eq.expr q_ b) &&
                                    (rule = "abconj")
                                ->
                            found := true
                        | Apply ({core=Internal Conj}, [
                                    {core=Apply ({core=Internal ENABLED}, [p])};
                                    {core=Apply ({core=Internal ENABLED}, [q])}
                                ]) when
                                    let p_ = E_subst.app_expr shift p in
                                    let q_ = E_subst.app_expr shift q in
                                    (E_eq.expr p_ a) && (E_eq.expr q_ b) &&
                                    ((rule = "abconj_inverse") ||
                                     (rule = "pconj_inverse"))
                                ->
                            found := true
                        | Apply ({core=Internal Conj}, [p; {core=
                                Apply ({core=Internal ENABLED}, [q])}]) when
                                let p_ = E_subst.app_expr shift p in
                                let q_ = E_subst.app_expr shift q in
                                (E_eq.expr p_ a) && (E_eq.expr q_ b) &&
                                (rule = "pconj_inverse") ->
                            found := true
                        | Apply ({core=Internal Equiv}, [p; q]) when
                                let p_ = E_subst.app_expr shift p in
                                let q_ = E_subst.app_expr shift q in
                                (E_eq.expr p_ a) && (E_eq.expr q_ b) &&
                                (rule = "equiv") ->
                            found := true;
                            found_a_type := true;
                            found_b_type := true
                        | Apply ({core=Internal Eq}, [p; q]) when
                                let p_ = E_subst.app_expr shift p in
                                let q_ = E_subst.app_expr shift q in
                                (E_eq.expr p_ a) && (E_eq.expr q_ b) &&
                                (rule = "equiv") ->
                            found := true
                        | Apply ({core=Internal Mem},
                                    [p; {core=Internal BOOLEAN}]) when
                                let p_ = E_subst.app_expr shift p in
                                (E_eq.expr p_ a) ->
                            found_a_type := true
                        | Apply ({core=Internal Mem},
                                    [q; {core=Internal BOOLEAN}]) when
                                let q_ = E_subst.app_expr shift q in
                                (E_eq.expr q_ b) ->
                            found_b_type := true
                        | Apply ({core=Internal Implies}, [p; q]) when
                                (*
                                print_string "\n";
                                print_string (E_fmt.string_of_expr cx2 expr);
                                print_string (E_fmt.string_of_expr cx2 p);
                                print_string (E_fmt.string_of_expr cx2 q);
                                *)
                                let p_ = E_subst.app_expr shift p in
                                let q_ = E_subst.app_expr shift q in
                                (E_eq.expr p_ a) && (E_eq.expr q_ b) &&
                                (rule = "implies") ->
                            found := true
                        | _ -> () end
                    | _ -> ()
                end;
                E_visit.adj scx h
        end in
        let (_, cx3) = visitor#hyps ((), cx) hyps in
        ignore cx3
        (*
        print_string (E_fmt.string_of_expr cx3 a);
        print_string (E_fmt.string_of_expr cx3 b);
        *)
        in
    let check_active cx_goal expr =
        match expr.core with
        | Apply ({core=Internal ENABLED}, [{core=
                    Apply ({core=Internal Disj}, [a; b])
                }]) ->
            let a_level = E_levels.get_level a in
            let b_level = E_levels.get_level b in
            assert (a_level <= 2);
            assert (b_level <= 2);
            (Some a, Some b, "abdisj_inverse")
        | Apply ({core=Internal Disj}, [
                    {core=Apply ({core=Internal ENABLED}, [a])};
                    {core=Apply ({core=Internal ENABLED}, [b])}
                ]) ->
            let a_level = E_levels.get_level a in
            let b_level = E_levels.get_level b in
            assert (a_level <= 2);
            assert (b_level <= 2);
            (Some a, Some b, "abdisj")
        | Apply ({core=Internal ENABLED}, [{core=
                    Apply ({core=Internal Conj}, [a; b])
                }]) ->
            let a_variables = E_visit.collect_primed_vars cx_goal a in
            let b_variables = E_visit.collect_primed_vars cx_goal b in
            let cap = List.filter
                        (fun x -> List.mem x a_variables) b_variables in
            let isempty = (List.length cap) = 0 in
            let a_level = E_levels.get_level a in
            let b_level = E_levels.get_level b in
            assert (a_level <= 2);
            assert (b_level <= 2);
            if isempty then
                begin
                if (a_level = 2) then
                    (Some a, Some b, "abconj_inverse")
                else
                    (Some a, Some b, "pconj_inverse")
                end
            else
                begin
                (None, None, " ")
                end
        | Apply ({core=Internal Conj}, [
                    {core=Apply ({core=Internal ENABLED}, [a])};
                    {core=Apply ({core=Internal ENABLED}, [b])}
                ]) ->
            let a_variables = E_visit.collect_primed_vars cx_goal a in
            let b_variables = E_visit.collect_primed_vars cx_goal b in
            let cap = List.filter
                        (fun x -> List.mem x a_variables) b_variables in
            let isempty = (List.length cap) = 0 in
            if isempty then
                begin
                (Some a, Some b, "abconj")
                end
            else
                begin
                (None, None, " ")
                end
        | Apply ({core=Internal Conj}, [p; {core=
                Apply ({core=Internal ENABLED}, [a])}]) ->
            let p_level = E_levels.get_level p in
            let a_level = E_levels.get_level a in
            if (p_level <= 1) && (a_level <= 2) then
                (Some p, Some a, "pconj")
            else
                (None, None, " ")
        | Apply ({core=Internal Equiv}, [
            {core=Apply ({core=Internal ENABLED}, [a])};
            {core=Apply ({core=Internal ENABLED}, [b])}
            ]) -> (Some a, Some b, "equiv")
        | Apply ({core=Internal Implies}, [
            {core=Apply ({core=Internal ENABLED}, [a])};
            {core=Apply ({core=Internal ENABLED}, [b])}
            ]) -> (Some a, Some b, "implies")
        | Apply ({core=Internal Eq}, [
            {core=Apply ({core=Internal ENABLED}, [a])};
            {core=Apply ({core=Internal ENABLED}, [b])}
            ]) -> (Some a, Some b, "equiv")
        | _ -> (None, None, " ")
        in
    match expr.core with
    | Sequent sq -> begin
        let hyps = sq.context in
        let active = sq.active in
        let visitor = object (self: 'self)
            inherit [unit] E_visit.iter_visible_hyp
        end in
        let (_, cx_goal) = visitor#hyps ((), cx) hyps in
        let (a, b, rule) = check_active cx_goal active in
        if a <> None then begin
            check_context hyps a b rule
        end;
        let proved = !found && !found_a_type && !found_b_type in
        begin if proved then
            Util.printf ~at:expr ~prefix:"[INFO]" "%s"
                ("\nProved " ^ rule ^ "\n")
        else
            failwith "ENABLEDaxioms proof directive did not succeed.\n" end;
        let core = (if proved then Internal TRUE else expr.core) in
        let active = noprops core in
        let sq = {sq with active=active} in
        noprops (Sequent sq)
        end
    | _ -> assert false


let lambdify cx e
        ~(lambdify_enabled:bool)
        ~(lambdify_cdot:bool)
        ~(autouse:bool) =
    let e = E_levels.rm_expr_level cx e in
    let e = E_levels.compute_level cx e in
    let e = expand_definitions cx e
        ~expand_enabled:lambdify_enabled
        ~expand_cdot:lambdify_cdot
        ~autouse:autouse in
    let visitor = new lambdify_action_operators in
    let e = visitor#expand cx e
        ~lambdify_enabled:lambdify_enabled
        ~lambdify_cdot:lambdify_cdot
        ~keep_same_names:false in
    let visitor = new check_arity in
    visitor#expr ((), cx) e;
    e


let quantify
        (cx: T.ctx)
        (e: expr)
        ~(expand_enabled: bool)
        ~(expand_cdot: bool):
            expr =
    let visitor = new replace_action_operators_with_quantifiers in
    visitor#replace cx e
        ~expand_enabled:expand_enabled
        ~expand_cdot:expand_cdot


let expand_action_operators
        (cx: T.ctx)
        (e: expr)
        ~(expand_enabled: bool)
        ~(expand_cdot: bool)
        ~(autouse: bool):
            expr =
    assert (expand_enabled || expand_cdot);
    (* compute expression level information *)
    let e_ = E_levels.rm_expr_level cx e in
    let e_ = E_levels.compute_level cx e_ in
    (* auto-expand definitions as needed *)
    let e_ = expand_definitions cx e_
        ~expand_enabled:expand_enabled
        ~expand_cdot:expand_cdot
        ~autouse:autouse in
    (* replace `ENABLED` and `\cdot` with `\E` *)
    (*
    let visitor = new expansion_of_action_operators in
    visitor#expand cx e_
        ~expand_enabled:expand_enabled
        ~expand_cdot:expand_cdot
    *)
    let visitor = new lambdify_action_operators in
    (* Not lambdifying an operator is expected to raise the same errors that
    not passing `expand_operator` does for the class
    `expansion_of_action_operators`.
    *)
    let e_ = visitor#expand cx e_
        ~lambdify_enabled:expand_enabled
        ~lambdify_cdot:expand_cdot
        ~keep_same_names:true in
    let visitor = new replace_action_operators_with_quantifiers in
    let e_ = visitor#replace cx e_
        ~expand_enabled:expand_enabled
        ~expand_cdot:expand_cdot in
    commute_exists_disjunction cx e_
