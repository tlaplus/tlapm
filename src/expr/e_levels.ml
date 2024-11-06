(* Compute expression levels.


References
==========

[1] Leslie Lamport, Specifying Systems, Addison-Wesley, 2002
    https://lamport.azurewebsites.net/tla/book.html

[2] Leslie Lamport, TLA+ Version 2: A Preliminary Guide, 2018
    https://lamport.azurewebsites.net/tla/tla2-guide.pdf

[3] Leslie Lamport, LevelSpec specification, from the repository `tlaplus` at:
    https://github.com/tlaplus/tlatools/src/tla2sany/semantic/LevelNode.java

[4] Leslie Lamport, Proving safety properties, 2019
    https://lamport.azurewebsites.net/tla/proving-safety.pdf

*)


(* See Section 17.2 on pages 321--324 of Specifying Systems.
See `LevelSpec.tla` in `tla2sany.semantic.LevelNode`.

level numbers:
    0 = constant
    1 = state
    2 = action
    3 = temporal

A relevant computation is in the module `e_constness.ml`.
*)

open Ext
open Property
open Util

open E_t
open E_visit


module Dq = Deque
module Visit = E_visit
module StringSet = Set.Make(String)


type level_info =  (* Stores information for computing the
        levels of syntax tree nodes *)
    LevelInfo of
        int *  (* operator level *)
            (* `OpDefNode.level`, `OpApplNode.level`, ... *)
        bool list *  (* weights of operator arguments *)
            (* `OpDefNode.weights` *)
        StringSet.t  (* set of argument names that the level depends on *)
            (* `LevelConstraintFields.levelParams` *)


let exprlevel : level_info pfuncs =
    Property.make "Expr.Levels.exprlevel"
let assert_is_level (level: int) =
    assert ((level >= 0) && (level <= 3))
    (* The value 4 signifies that the notion of level is undefined for
    the syntax node. *)
let assert_is_arity (arity: int) =
    assert (arity >= 0)

let has_level x = Property.has x exprlevel
let get_level_info x = Property.get x exprlevel
let get_level x =
    let level_info = get_level_info x in
    let level = match level_info with
        | LevelInfo (level, _, _) -> level
    in
    level
let rm_level x = Property.remove x exprlevel
let get_level_weights x =
    let level_info = get_level_info x in
    let weights = match level_info with
        | LevelInfo (_, weights, _) -> weights
    in
    weights
let get_level_args x =
    let level_info = get_level_info x in
    let level_args = match level_info with
        | LevelInfo (_, _, level_args) -> level_args
    in
    level_args

let make_level_info (level: int) =
    assert_is_level level;
    let level_args = StringSet.empty in
    let weights = [] in
    LevelInfo (level, weights, level_args)
let make_undefined_level_info =  (* separate function to
        include assertion in `make_level_info` *)
    let level_args = StringSet.empty in
    let weights = [] in
    LevelInfo (4, weights, level_args)
let make_weights (arity: int) =
    assert_is_arity arity;
    List.init arity (fun x -> true)
let make_level_info_arity (level: int) (arity: int) =
    assert_is_level level;
    assert_is_arity arity;
    let level_args = StringSet.empty in
    let weights = make_weights arity in
    LevelInfo (level, weights, level_args)


let assert_has_correct_level expr =
    let (e_level: int) = get_level expr in
    (match expr.core with
        | Sequent _ -> assert (e_level = 4)
            (* notion of level undefined *)
        | _ -> assert_is_level e_level)


let kind_to_level (kind: kind): int =
    (* Return expression level of declared identifier with `kind`. *)
    match kind with
    | Constant -> 0
    | State -> 1
    | Action -> 2
    | Temporal -> 3
    | Unknown -> assert false


(*
The level property is stored in the syntax tree nodes.
Therefore, the level computation is recursive over the syntax tree structure.
This ensures the presence of level information (as a property that annotates
each relevant syntax node) so that it can be used later, without further
calls to invoke level computation.
(It is also a form of memoization of intermediate results.)

Note: Expanding declarations has linear complexity, but expanding definitions
could have exponential complexity.
*)
class virtual ['s] level_computation = object (self : 'self)
    inherit ['s] Visit.map as super

    method expr ((_, cx) as scx) e =
        if (has_level e) then
            e
        else
        begin
        let max_args_level scx args = (
            let es_ = List.map (self#expr scx) args in
            let es_levels = List.map get_level es_ in
            let e_level = List.fold_left max 0 es_levels in
            let level_args_sets = List.map get_level_args es_ in
            let level_args = List.fold_left StringSet.union
                StringSet.empty level_args_sets in
            (e_level, level_args, es_)
            ) in
        let level_info_from_args scx args = (
            let (level, level_args, es_) = max_args_level scx args in
            let level_info = LevelInfo (level, [], level_args) in
            (level_info, es_)
            ) in
        let bounds_level scx (bs: bounds) = (
            (* `bs` is a list of domain expressions (`Domain (expr)`),
            one expression for each constant bound by the quantifier.
            The expressions in `bs` contain level information.

            This function is called only for bound constants.
            *)
            let (e_scx, bs) = self#bounds scx bs in
            let (dom_es, bs_levels, level_args_sets) =
                let prev_dom = ref e in
                let bs_levels = ref [] in
                let level_args_sets = ref [] in
                let f ((v: hint),
                       (k: kind),
                       (dom: bound_domain)):
                        bound = begin
                    match dom with
                    | Domain d ->
                        begin
                        begin
                        match k with
                        | Constant -> ()
                        | _ -> assert false
                        end;
                        let d_ = self#expr scx d in
                        let d_level = get_level d_ in
                        bs_levels := d_level :: !bs_levels;
                        let d_level_args = get_level_args d_ in
                        level_args_sets := d_level_args :: !level_args_sets;
                        prev_dom := d_;
                        (v, k, Domain d_)
                        end
                    | Ditto -> (v, k, Ditto)
                    | No_domain ->  (* `\E x:` yields
                            no level constraints. *)
                        (v, k, No_domain)
                    end
                in
                (List.map f bs, !bs_levels, !level_args_sets) in
            let doms_level = List.fold_left max 0 bs_levels in
            let level_args = List.fold_left
                StringSet.union StringSet.empty level_args_sets in
            (e_scx, dom_es, doms_level, level_args)
            ) in
        let apply_operator op_ es =
            begin
            assert ((List.length es) >= 1);
            (* operator `op` *)
            let op_level = get_level op_ in
            let op_level_args = get_level_args op_ in
            let op_weights = get_level_weights op_ in
            (* expressions `es` of operator arguments *)
            let es_ = List.map (self#expr scx) es in
            let es_levels = List.map get_level es_ in
            let es_level_args_list = List.map get_level_args es_ in
            (* combine level info *)
            (*
            Interaction between parameters of second-order operators occurs
            when a parameter of positive arity is applied to another parameter
            (necessarily of arity 0, because parameters can be up to
            first-order). This interaction is taken into account by using
            a weights array with all elements equal to `true` for operator
            parameters, as declared in `self#hyp` below.
            *)
            let f weights values op c =
                if List.length weights <> List.length values then (
                    Util.eprintf ~at:op_ "Invalid number of arguments";
                    Errors.set op_ (Printf.sprintf "Invalid number of arguments");
                    failwith "Expr.Levels: ARITY");
                let pairs = List.combine weights values in
                let w (weight, value) = if weight then value else c in
                let values = List.map w pairs in
                List.fold_left op c values
                in
            (* levels based on weights *)
            let es_level = f op_weights es_levels max 0 in
            (* level args based on weights *)
            let es_level_args = f op_weights es_level_args_list
                StringSet.union StringSet.empty in
            let level = max op_level es_level in
            let level_args = StringSet.union
                op_level_args es_level_args in
            let weights = [] in
            let level_info = LevelInfo (level, weights, level_args) in
            (* returned expression *)
            let new_apply = Apply (op_, es_) in
            let new_e = new_apply @@ e in
            assign new_e exprlevel level_info
            end
            in
        let e_ = match e.core with
        | Ix n -> begin
            assert (n >= 1);
            let hyp = E_t.get_val_from_id cx n in
            let e_level_info = match hyp.core with
                | Fresh _
                | Flex _
                | Defn _ ->
                    (* For definitions, this call can recurse in the body
                    of the definition. If the level computation has been
                    called on a sequent, then level information for all
                    definitions in the context `cx` has been computed,
                    so this call will return after finding the level
                    information in the property that annotates the
                    definition. *)
                    let hyp_scx = E_t.scx_front scx n in
                    let (_, e_) = self#hyp hyp_scx hyp in
                    get_level_info e_
                | FreshTuply _ ->
                    assert false  (* not implemented *)
                | Fact (e_, _, _) ->
                    (*
                    E_t.print_cx cx;
                    print_string "Index in context:\n";
                    print_int n;
                    Util.eprintf ~at:e "%s"
                        (let hyp_cx = E_t.cx_front cx n in
                        (E_fmt.string_of_expr hyp_cx e));
                    *)
                    let hyp_scx = E_t.scx_front scx n in
                    let (_, e_) = self#hyp hyp_scx hyp in
                    get_level_info e_
                    (*
                    assert false  (* A de Bruijn index
                        refers to a declared or defined operator.
                        *)
                    *)
                in
            assign e exprlevel e_level_info
            end
        | Internal b -> begin
            let e_level_info = match b with
            (* Logic *)
            | Builtin.TRUE | Builtin.FALSE -> make_level_info 0
            | Builtin.Implies | Builtin.Equiv
            | Builtin.Conj | Builtin.Disj ->
                make_level_info_arity 0 2
            | Builtin.Neg ->
                make_level_info_arity 0 1
            | Builtin.Eq | Builtin.Neq ->
                make_level_info_arity 0 2
            (* Sets *)
            | Builtin.STRING | Builtin.BOOLEAN ->
                make_level_info 0
            | Builtin.SUBSET | Builtin.UNION | Builtin.DOMAIN ->
                make_level_info_arity 0 1
            | Builtin.Subseteq | Builtin.Mem | Builtin.Notmem
            | Builtin.Setminus | Builtin.Cap | Builtin.Cup ->
                make_level_info_arity 0 2
            (* Modal *)
            | Builtin.Actplus ->
                make_level_info_arity 3 2
            | Builtin.Box _ | Builtin.Diamond ->
                make_level_info_arity 3 1
                (* The operators:
                    Prime, StrongPrime, ENABLED, UNCHANGED, Leadsto, Cdot
                are implemented separately at
                operator application below, but included here to
                annotate the operator nodes. *)
            | Builtin.Prime | Builtin.StrongPrime ->
                make_level_info_arity 2 1
            | Builtin.ENABLED ->
                make_level_info_arity 1 1
            | Builtin.UNCHANGED ->
                make_level_info_arity 2 1
            | Builtin.Leadsto ->
                make_level_info_arity 3 2
            | Builtin.Cdot ->
                make_level_info_arity 2 2
            (* Arithmetic *)
            | Builtin.Nat | Builtin.Int
            | Builtin.Real | Builtin.Infinity ->
                make_level_info 0
            | Builtin.Plus | Builtin.Minus
            | Builtin.Times | Builtin.Ratio | Builtin.Quotient
            | Builtin.Remainder | Builtin.Exp | Builtin.Divides
            | Builtin.Lteq | Builtin.Lt
            | Builtin.Gteq | Builtin.Gt
            | Builtin.Range ->
                make_level_info_arity 0 2
            | Builtin.Uminus ->
                make_level_info_arity 0 1
            (* Sequences *)
            | Builtin.Seq | Builtin.Len ->
                make_level_info_arity 0 1
            | Builtin.BSeq ->
                make_level_info_arity 0 2
            | Builtin.Cat | Builtin.Append ->
                make_level_info_arity 0 2
            | Builtin.Head | Builtin.Tail ->
                make_level_info_arity 0 1
            | Builtin.SubSeq ->
                make_level_info_arity 0 3
            | Builtin.SelectSeq ->
                make_level_info_arity 0 2
            | Builtin.OneArg ->  (* :> *)
                make_level_info_arity 0 2
            | Builtin.Extend -> (* @@ *)
                make_level_info_arity 0 2
            | Builtin.Print ->
                make_level_info_arity 0 2
            | Builtin.PrintT ->
                make_level_info_arity 0 1
            | Builtin.Assert ->
                make_level_info_arity 0 2
            | Builtin.JavaTime ->
                make_level_info_arity 0 0
            | Builtin.TLCGet ->
                make_level_info_arity 0 1
            | Builtin.TLCSet ->
                make_level_info_arity 0 2
            | Builtin.Permutations ->
                make_level_info_arity 0 1
            | Builtin.SortSeq ->
                make_level_info_arity 0 2
                (* LevelInfo (0, [true, [...]],
                    StringSet.empty) *)
            | Builtin.RandomElement ->
                make_level_info_arity 0 1
            | Builtin.Any ->
                make_level_info_arity 0 0
            | Builtin.ToString ->
                make_level_info_arity 0 1
              (* special *)
            | Builtin.Unprimable ->
                make_level_info_arity 0 1
            | Builtin.Irregular -> assert false
                (* make_level_info_arity 0 1 *)
            in
            assign e exprlevel e_level_info
            end
        | Apply ({core=Opaque name} as op, args) ->
            (* case of opaque operator with arity <_, ... > . *)
            let arity = List.length args in
            let level_info = make_level_info_arity 0 arity in
            let op = assign op exprlevel level_info in
            apply_operator op args
        | Opaque name ->
            (* Opaque operator with arity `_` *)
            let level_info = make_level_info 0 in
            assign e exprlevel level_info
        | Bang (e, sels) -> assert false  (* subexpression references are
                expanded before expanding `ENABLED` and `\cdot`. *)
        | Lambda (vs, e) ->
            (* Note: 2nd-order operators (signified via `shp` below) are
            handled by the declarations in `e_scx` below and the call to
            the method `self#hyp` in the pattern case `Apply (op, es)` below.
            *)
            (* extend context with `vs` *)
            let e_scx = Visit.adjs scx
                (List.map
                    (fun (v, shp) ->
                        Fresh (v, shp, Unknown, Unbounded)
                        @@ v)
                    vs) in
            (* expression `e` *)
            let e_ = self#expr e_scx e in
            let e_level = get_level e_ in
            (*
            if e_level > 2 then
                begin
                let msg = (
                    "The `Lambda` with signature:\n" ^
                        (String.concat ", " (List.map
                            (fun (h, _) -> h.core) vs)) ^
                    "\n and body `e`:\n" ^
                        (let cx = snd e_scx in
                        E_fmt.string_of_expr cx e) ^
                    "\n has a body with expression level:\n" ^
                    (string_of_int e_level) ) in
                Util.eprintf ~at:e ~prefix:"[INFO]: " "%s" msg
                end;
            *)
            assert ((e_level <= 3) || (e_level = 4));
                (* The case `e_level = 4` corresponds to sequents that
                represent theorems that result from parameteric
                module instantiation.

                The case `e_level = 3` corresponds to a `LAMBDA` with
                a temporal expression. For example, `LAMBDA P:  [] P`.
                *)
            let e_level_args = get_level_args e_ in
            (* `vs` as level args *)
            let vs_list = List.map (fun (v, shp) -> v.core) vs in
            let vs_set = StringSet.of_list vs_list in
            (* combine level arg info *)
            let level_args = StringSet.diff e_level_args vs_set in
            (* weights *)
            let level_weights = List.map
                (fun v -> StringSet.mem v e_level_args)
                vs_list
                in
            (* The level of a defined operator is defined to correspond to
            the case with all formal parameters in `vs` having constant level.
            *)
            let level_info = LevelInfo (e_level, level_weights, level_args) in
            let new_lambda = Lambda (vs, e_) in
            let new_e = new_lambda @@ e in
            assign new_e exprlevel level_info
        | String s ->
            let level_info = make_level_info 0 in
            assign e exprlevel level_info
        | Num (m, n) ->
            let level_info = make_level_info 0 in
            assign e exprlevel level_info
        | Apply ({core=Internal Builtin.Prime} as op, [arg]) ->
            begin
            let op_ = self#expr scx op in
            let arg_ = self#expr scx arg in
            let arg_level = get_level arg_ in
            assert (arg_level <= 1);
            let level_info = make_level_info_arity 2 1 in
                (* the level of a primed expression is 2
                (so independent of level parameters of `arg`) *)
            let new_apply = Apply (op_, [arg_]) in
            let new_e = new_apply @@ e in
            assign new_e exprlevel level_info
            end
        | Apply ({core=Internal Builtin.StrongPrime} as op, [arg]) ->
            begin
            (* assume that level correctness has been checked by SANY *)
            let op_ = self#expr scx op in
            let arg_ = self#expr scx arg in
            let arg_level = get_level arg_ in
            assert (arg_level <= 1);
            let level_info = make_level_info_arity 2 1 in
                (* level is independent of level parameters of `arg` *)
            let new_apply = Apply (op_, [arg_]) in
            let new_e = new_apply @@ e in
            assign new_e exprlevel level_info
            end
        | Apply ({core=Internal Builtin.ENABLED} as op, [arg]) ->
            begin
            (* assume that level correctness has been checked by SANY *)
            let op_ = self#expr scx op in
            let arg_ = self#expr scx arg in
            let arg_level = get_level arg_ in
            assert (arg_level <= 2);
            let level_args = get_level_args arg_ in
            let level = 1 in
            let weights = [] in
            let level_info = LevelInfo (level, weights, level_args) in
            let new_enabled = Apply (op_, [arg_]) in
            let new_e = new_enabled @@ e in
            assign new_e exprlevel level_info
            end
        | Apply ({core=Internal Builtin.UNCHANGED} as op, [arg]) ->
            let op_ = self#expr scx op in
            let arg_ = self#expr scx arg in
            let arg_level = get_level arg_ in
            assert (arg_level <= 1);
            let level_args = get_level_args arg_ in
            let level = 2 in
            let weights = [] in
            let level_info = LevelInfo (level, weights, level_args) in
            let new_unchanged = Apply (op_, [arg_]) in
            let new_e = new_unchanged @@ e in
            assign new_e exprlevel level_info
        | Apply ({core=Internal Builtin.Cdot} as op, args) ->
            begin
            assert ((List.length args) = 2);
            let op_ = self#expr scx op in
            let args_ = List.map (self#expr scx) args in
            (* let arg_levels = List.map get_level args_ in
            let op_level = get_level op_ in
            let level = List.fold_left max op_level arg_levels in *)
            let level = 2 in  (* SANY appears to assign level 2 to
                `\cdot` for any levels of the arguments.
                If changed here, remember to update also the
                pattern case for `Internal.Builtin` leaf nodes above.
                *)
            assert (level <= 2);
            let weights = [] in
            (* `\cdot` is of level 2 *)
            (*
            let a_level_args = get_level_args (List.nth args_ 1) in
            *)
                (* The level of `A \cdot B` depends on only unprimed
                level parameters from action `A`. *)
            (* let level_info = LevelInfo (level, weights, a_level_args) in *)
            (* `\cdot` is of level 2, so level does not depend on params *)
            let level_args = StringSet.empty in
            let level_info = LevelInfo (level, weights, level_args) in
            let new_cdot = Apply (op_, args_) in
            let new_e = new_cdot @@ e in
            assign new_e exprlevel level_info
            end
        (* Temporal operators *)
        | Apply ({core=Internal Builtin.Leadsto} as op, args) ->
            assert ((List.length args) == 2);
            let op_ = self#expr scx op in
            let level_info = make_level_info_arity 3 2 in
            let args_ = List.map (self#expr scx) args in
            let new_leadsto = Apply (op_, args_) in
            let new_e = new_leadsto @@ e in
            assign new_e exprlevel level_info
        (* Operator application *)
        | Apply (op, es) ->
            let op_ = self#expr scx op in
            assert ((List.length es) >= 1);
            apply_operator op_ es
        | Sequent sq ->
            begin
            let (_, sq_) = self#sequent scx sq in
            (* A sequent has expression level equal to the maximum
            expression level over antecedents and consequent.
            *)
            let rec hyps_level hs =
                match Dq.front hs with
                | None -> 0
                | Some (h, hs) ->
                    let h_level = get_level h in
                    let hs_level = hyps_level hs in
                    max h_level hs_level
                in
            let level_hyps = hyps_level sq_.context in
            let level_active = get_level sq_.active in
            let level = max level_hyps level_active in
            (* store the level info *)
            let new_sq = Sequent sq_ in
            let new_e = new_sq @@ e in
            let level_info = make_level_info level in
            assign new_e exprlevel level_info
            end
        | With (expr, m) ->
            let expr_ = self#expr scx expr in
            let level_info = get_level_info expr_ in
            let new_with = With (expr_, m) in
            let new_e = new_with @@ e in
            assign new_e exprlevel level_info
        | Let (ds, e) ->
            let (e_scx, ds_) = self#defns scx ds in
            let e_ = self#expr e_scx e in
            let level_info = get_level_info e_ in
            let new_let = Let (ds_, e_) in
            let new_e = new_let @@ e in
            assign new_e exprlevel level_info
        | If (e, f, g) ->
            let es = [e; f; g] in
            let (level_info, es_) = level_info_from_args scx es in
            let e_ = List.nth es_ 0 in
            let f_ = List.nth es_ 1 in
            let g_ = List.nth es_ 2 in
            let new_if = If (e_, f_, g_) in
            let new_e = new_if @@ e in
            assign new_e exprlevel level_info
        | List (q, es) ->
            let (level_info, es_) = level_info_from_args scx es in
            let new_list = List (q, es_) in
            let new_e = new_list @@ e in
            assign new_e exprlevel level_info
        | Quant (q, bs, e) ->
            (* The expression `\E x:  P(x)` has the same level as `P(x)`.
            So the expression `\E x \in S:  P(x)` has the same level as the
            expression `P(x) /\ (x \in S)`.
            The expression `P(x) /\ (x \in S)` has level = max of levels of
            `P(x)` and `(x \in S)`, and the level of `(x \in S)` equals the
            level of `S` (because in this case `x` is a constant).
            *)
            (* domain bounds `bs` *)
            let (e_scx, bs_, doms_level, doms_level_args) =
                bounds_level scx bs in
            (* expression `e` *)
            let e_ = self#expr e_scx e in
            let e_level = get_level e_ in
            let e_level_args = get_level_args e_ in
            (* combine level info *)
            let level = max e_level doms_level in
            let level_args = StringSet.union e_level_args doms_level_args in
            let level_info = LevelInfo (level, [], level_args) in
            let new_quant = Quant (q, bs_, e_) in
            let new_e = new_quant @@ e in
            assign new_e exprlevel level_info
        | Tquant (q, vs, e) ->
            let new_tquant =
                let scx = adjs scx (List.map (fun v -> Flex v @@ v) vs) in
                let e = self#expr scx e in
                Tquant (q, vs, e) in
            let new_e = new_tquant @@ e in
            let level_info = make_level_info_arity 3 0 in
            assign new_e exprlevel level_info
        | Choose (v, optdom, e) ->  (* 0, 1, 2 *)
            (* extend context with bound constant *)
            let optdom_ = Option.map (self#expr scx) optdom in
            let dom = match optdom_ with
                | None -> Unbounded
                | Some dom -> Bounded (dom, Visible)
                in
            let h = Fresh (v, Shape_expr, Constant, dom) @@ v in
            let e_scx = adj scx h in
            (* expression `e` *)
            let e_ = self#expr e_scx e in
            let e_level = get_level e_ in
            let e_level_args = get_level_args e_ in
            (* domain `dom` *)
            let (dom_level, dom_level_args) = match optdom_ with
                | None -> (0, StringSet.empty)
                | Some dom ->
                    let dom_ = self#expr scx dom in
                    let dom_level = get_level dom_ in
                    let dom_level_args = get_level_args dom_ in
                    (dom_level, dom_level_args)
                in
            (* combine level info *)
            let level = max dom_level e_level in
            let level_args = StringSet.union
                dom_level_args e_level_args in
            let level_info = LevelInfo (level, [], level_args) in
            let new_choose = Choose (v, optdom_, e_) in
            let new_e = new_choose @@ e in
            assign new_e exprlevel level_info
        | SetSt (v, dom, e) ->  (* {x \in S:  P(x)} *)
            (* domain bound `dom` *)
            let dom_ = self#expr scx dom in
            let dom_level = get_level dom_ in
            let dom_level_args = get_level_args dom_ in
            (* expression `e` *)
            let e_scx = adj scx (
                Fresh (v, Shape_expr, Constant,
                       Bounded (dom, Visible)) @@ v) in
            let e_ = self#expr e_scx e in
            let e_level = get_level e_ in
            let e_level_args = get_level_args e_ in
            (* combine level info *)
            let level = max dom_level e_level in
            let level_args = StringSet.union
                dom_level_args e_level_args in
            let level_info = LevelInfo (level, [], level_args) in
            let new_setst = E_t.From_hint.make_setst
                v dom_ e_ in
            let new_e = new_setst.core @@ e in
            assign new_e exprlevel level_info
        | SetOf (e, bs) ->  (* {f(x):  x \in S} *)
                (* There is one bound constant in the expression
                `{x \in S:  P(x)}`, so the constructor `SetSt` takes
                one domain `dom`.
                There can be multiple bound constants in the expression
                `{f(x, ...):  x \in S, ...}`, so the constructor `SetOf`
                takes multiple domain bounds.
                *)
            (* domain bounds `bs` *)
            let (e_scx, bs_, doms_level, doms_level_args) =
                bounds_level scx bs in
            (* expression `e` *)
            let e_ = self#expr e_scx e in
            let e_level = get_level e_ in
            let e_level_args = get_level_args e_ in
            (* combine level info *)
            let level = max e_level doms_level in
            let level_args = StringSet.union
                e_level_args doms_level_args in
            let level_info = LevelInfo (level, [], level_args) in
            let new_setof = SetOf (e_, bs_) in
            let new_e = new_setof @@ e in
            assign new_e exprlevel level_info
        | SetEnum es -> (* {1, 2, 3} *)
            let (level, level_args, es_) = max_args_level scx es in
            let level_info = LevelInfo (level, [], level_args) in
            let new_setenum = SetEnum es_ in
            let new_e = new_setenum @@ e in
            assign new_e exprlevel level_info
        | Fcn (bs, e) ->  (* [x \in S |-> P(x)] *)
            (* domain bounds `bs` *)
            let (e_scx, bs_, doms_level, doms_level_args) =
                bounds_level scx bs in
            (* expression `e` *)
            let e_ = self#expr e_scx e in
            let e_level = get_level e_ in
            let e_level_args = get_level_args e_ in
            (* combine level info *)
            let level = max e_level doms_level in
            let level_args = StringSet.union
                e_level_args doms_level_args in
            let level_info = LevelInfo (level, [], level_args) in
            let new_fcn = Fcn (bs_, e_) in
            let new_e = new_fcn @@ e in
            assign new_e exprlevel level_info
        | FcnApp (f, es) ->  (* f[x] *)
                (* function `f` *)
            let fes = f :: es in
            let (level_info, fes_) = level_info_from_args scx fes in
            let f_ = List.hd fes_ in
            let es_ = List.tl fes_ in
            let new_fcnapp = FcnApp (f_, es_) in
            let new_e = new_fcnapp @@ e in
            assign new_e exprlevel level_info
        | Arrow (a, b) ->
            let args = [a; b] in
            let (level_info, args_) = level_info_from_args scx args in
            assert (List.length args_ = 2);
            let a_ = List.hd args_ in
            let b_ = List.nth args_ 1 in
            let new_arrow = Arrow (a_, b_) in
            let new_e = new_arrow @@ e in
            assign new_e exprlevel level_info
        | Product es ->
            let (level_info, es_) = level_info_from_args scx es in
            let new_product = Product es_ in
            let new_e = new_product @@ e in
            assign new_e exprlevel level_info
        | Tuple es ->
            let (level_info, es_) = level_info_from_args scx es in
            let new_tuple = Tuple es_ in
            let new_e = new_tuple @@ e in
            assign new_e exprlevel level_info
        | Rect fs ->
            let (ps, es) = List.split fs in
            let (level_info, es_) = level_info_from_args scx es in
            let fs_ = List.combine ps es_ in
            let new_rect = Rect fs_ in
            let new_e = new_rect @@ e in
            assign new_e exprlevel level_info
        | Record fs ->
            let (ps, es) = List.split fs in
            let (level_info, es_) = level_info_from_args scx es in
            let fs_ = List.combine ps es_ in
            let new_record = Record fs_ in
            let new_e = new_record @@ e in
            assign new_e exprlevel level_info
        | Except (e, xs) ->
            (* e *)
            let e_ = self#expr scx e in
            let e_level = get_level e_ in
            let e_level_args = get_level_args e_ in
            (* xs *)
            let (xs_level, xs_level_args, xs_) = (
                let f (trail, res) = (
                    let trail_arg_level = function
                        | Except_dot s ->
                            ((0, StringSet.empty),
                            Except_dot s)
                        | Except_apply e ->
                            let e_ = self#expr scx e in
                            let e_level = get_level e_ in
                            let e_level_args = get_level_args e_ in
                            ((e_level, e_level_args),
                            Except_apply e_)
                    in
                    let r = List.map trail_arg_level trail in
                    let (trail_levels, trail_) = List.split r in
                    let (trail_level, trail_level_args) = List.fold_left
                        (fun (xy: int * StringSet.t)
                             (uv: int * StringSet.t) ->
                            let (x, y) = xy in
                            let (u, v) = uv in
                            let r = max x u in
                            let w = StringSet.union y v in
                            (r, w)
                            )
                        (0, StringSet.empty) trail_levels in
                    let res_ = self#expr scx res in
                    let res_level = get_level res_ in
                    let res_level_args = get_level_args res_ in
                    let level = max res_level trail_level in
                    let level_args = StringSet.union
                        res_level_args trail_level_args in
                    ((level, level_args), (trail_, res_))
                    ) in
                let trail_levels_xs_ = List.map f xs in
                let (trail_levels, xs_) = List.split trail_levels_xs_ in
                let (xs_level, xs_level_args) = List.fold_left
                    (fun (xy: (int * StringSet.t))
                         (uv: (int * StringSet.t)) ->
                        let (x, y) = xy in
                        let (u, v) = uv in
                        (max x u, StringSet.union y v))
                    (0, StringSet.empty) trail_levels
                    in
                (xs_level, xs_level_args, xs_)
                ) in
            (* combine level info *)
            let level = max e_level xs_level in
            let level_args = StringSet.union e_level_args xs_level_args in
            let level_info = LevelInfo (level, [], level_args) in
            let new_except = Except (e_, xs_) in
            let new_e = new_except @@ e in
            assign new_e exprlevel level_info
        (* Record field operator:  r.a *)
        | Dot (e, f) ->
            let e_ = self#expr scx e in
            let level_info = get_level_info e_ in
            let new_dot = Dot (e_, f) in
            let new_e = new_dot @@ e in
            assign new_e exprlevel level_info
        (* The subscript in the action-level expression:  [A]_v *)
        | Sub (s, e, f) ->
            let level = 2 in
            let (_, level_args, ef_) = max_args_level scx [e; f] in
            assert ((List.length ef_) == 2);
            let e_ = List.nth ef_ 0 in
            let f_ = List.nth ef_ 1 in
            let level_info = LevelInfo (level, [], level_args) in
            let new_sub = Sub (s, e_, f_) in
            let new_e = new_sub @@ e in
            assign new_e exprlevel level_info
        (* The subscript in the temporal-level expression:  [][A]_v *)
        | Tsub (s, e, f) ->
            let level_info = make_level_info 3 in
            let e_ = self#expr scx e in
            let f_ = self#expr scx f in
            let new_tsub = Tsub (s, e_, f_) in
            let new_e = new_tsub @@ e in
            assign new_e exprlevel level_info
        | Fair (fop, e, f) ->
            let level_info = make_level_info 3 in
            let e_ = self#expr scx e in
            let f_ = self#expr scx f in
            let new_fair = Fair (fop, e_, f_) in
            let new_e = new_fair @@ e in
            assign new_e exprlevel level_info
        | Case (efs, oth) ->
            let (es, fs) = List.split efs in
            (* let esfs = List.append es fs in
            let (efs_level, efs_level_args, es_) =
                max_args_level scx esfs in *)
            let es_ = List.map (self#expr scx) es in
            let fs_ = List.map (self#expr scx) fs in
            let efs_ = List.combine es_ fs_ in
            let esfs = List.append es_ fs_ in
            let (efs_level, efs_level_args, es_) =
                (* level already computed, so the
                computation is not repeated for elements
                of `esfs`. *)
                max_args_level scx esfs in
            let (oth_, oth_level, oth_level_args) =
                match oth with
                | Some e ->
                    let e_ = self#expr scx e in
                    let level = get_level e_ in
                    let level_args = get_level_args e_ in
                    (Some e_, level, level_args)
                | None -> (None, 0, StringSet.empty)
            in
            let level = max efs_level oth_level in
            let level_args = StringSet.union
                efs_level_args oth_level_args in
            let level_info = LevelInfo (level, [], level_args) in
            let new_case = Case (efs_, oth_) in
            let new_e = new_case @@ e in
            assign new_e exprlevel level_info
        | At b ->
            assert false
            (*
            let level_info = make_level_info 0 in
            let new_at = At b in
            let new_e = new_at @@ e in
            assign new_e exprlevel level_info
            *)
        | Parens (e, pf) ->
            let e_ = self#expr scx e in
            let e_level_info = get_level_info e_ in
            (* `super#pform` returns `pf` *)
            let pf_ = self#pform scx pf in
            let new_parens = Parens (e_, pf_) in
            let new_e = new_parens @@ e in
            assign new_e exprlevel e_level_info
        | QuantTuply _
        | ChooseTuply _
        | SetStTuply _
        | SetOfTuply _
        | FcnTuply _ ->
            assert false  (* not implemented *)
        in
        e_
        end

    method defn scx df =
        match df.core with
        | Recursive (nm, shp) ->
                Util.eprintf ~at:df "%s" (
                    "Recursive operator definitions are " ^
                    "not supported. ");
                assert false
            (* Reasoning about recursive operator definitions
            is unimplemented. *)
        | Operator (nm, e) ->
            (* Operator signatures are represented as `Lambda`.
            So the `Lambda` parameters will have kind `Unknown`.
            This kind is assumed to be constant for computing the
            level of an operator, and this level is used together
            with the argument weights and levels of arguments to
            compute the level of an application of the operator to
            specific expressions as arguments.
            *)
            let e_ = self#expr scx e in
            let core = Operator (nm, e_) in
            let df_ = {df with core = core} in
            let level_info = get_level_info e_ in
            assign df_ exprlevel level_info
        | Bpragma (nm, e, args) ->  (* similar to pattern case for
                `Operator` above *)
            let e_ = self#expr scx e in
            let core = Bpragma (nm, e_, args) in
            let df_ = {df with core = core} in
            let level_info = get_level_info e_ in
            assign df_ exprlevel level_info
        | Instance (nm, i) -> assert false
            (* Operators from instantiation are expanded before
            generating proof obligations. See the function
            `normalize` in the module `module/m_elab`.
            *)

    method hyp scx h =
        let level_info = begin match h.core with
            (* declared variable *)
            | Flex _ -> make_level_info 1
            (* declared operator of any arity *)
            | Fresh (name, op_shape, kind, _) -> begin
                let level = match kind with
                    | Constant -> 0
                        (* Using the following levels for identifiers
                        declared as `STATE`, `ACTION`, `TEMPORAL`
                        ensures soundness when using the computed level. *)
                    | State -> 1
                    | Action -> 2
                    | Temporal -> 3
                    | Unknown -> 0
                        (* Describes the kind of arguments of
                        `LAMBDA` (see case for `Lambda` below),
                        and of parameters of instantiation
                        (see `super#instance`).
                        Has level 0 by comment in `BoundSymbolNode` and
                        comment about what the level of a syntax tree node
                        means. See also comment of
                        `OpDefOrDeclNodeFields.level`. *)
                    in
                let weights = match op_shape with
                    | Shape_expr -> []  (* declared operator of arity 0 *)
                    | Shape_op arity ->  (* declared operator of positive arity
                        This case of arity of declared operators includes
                        parameters of a second-order operator that have
                        positive arity. Thus, second-order operators are
                        handled here.
                        *)
                        assert (arity >= 1);
                        make_weights arity
                    in
                let level_args = StringSet.singleton name.core in
                LevelInfo (level, weights, level_args)
                end
            | FreshTuply _ ->
                assert false  (* not implemented *)
            (* defined operator of any arity *)
            | Defn (df, _, _, _) ->
                let df_ = self#defn scx df in
                get_level_info df_
            | Fact (e, _, _) ->
                let e_ = self#expr scx e in
                begin
                if (has_level e_) then
                    get_level_info e_
                else
                    (* For example, the notion of expression level is
                    undefined for theorems. *)
                    make_undefined_level_info
                end
            end in
        (* Hidden definitions need to be visited to
        have level information available for computing the
        level of expressions where the operator occurs. *)
        let (scx_, e_) = match h.core with
            | Fresh (nm, shp, lc, dom) ->
                let dom = match dom with
                  | Unbounded -> Unbounded
                  | Bounded (r, rvis) ->
                        Bounded (self#expr scx r, rvis)
                in
                let h = Fresh (nm, shp, lc, dom) @@ h in
                (adj scx h, h)
            | FreshTuply _ ->
                assert false  (* not implemented *)
            | Flex s ->
                let h = Flex s @@ h in
                (adj scx h, h)
            | Defn (df, wd, vis, ex) ->
                let df = self#defn scx df in
                let h = Defn (df, wd, vis, ex) @@ h in
                (adj scx h, h)
            | Fact (e, vis, tm) ->
                let h = Fact (self#expr scx e, vis, tm) @@ h in
                (adj scx h, h)
            in
        let e_ = assign e_ exprlevel level_info in
        (scx_, e_)

end


let compute_level cx expr =
    let visitor = object
        inherit [unit] level_computation
    end in
    let scx = ((), cx) in
    visitor#expr scx expr


class virtual ['s] _rm_expr_level = object (self : 'self)
    (* Recursively remove level information from an expression. *)
    inherit ['s] Visit.map_visible_hyp as super

    method expr (s, cx) e =
        let scx_ = (s, cx) in
        let e_ = super#expr scx_ e in
        rm_level e_

    method pform scx pf =
        let pf_ = super#pform scx pf in
        rm_level pf_

    method defn scx df =
        let df_ = super#defn scx df in
        rm_level df_

    (* level info removed from context because the
        context is stored in sequents *)
    method hyp scx h =
        let (scx_, h_) = super#hyp scx h in
        let h_ = rm_level h_ in
        (scx_, h_)
end


let rm_expr_level cx expr =
    let visitor = object
        inherit [unit] _rm_expr_level
    end in
    let scx = ((), cx) in
    visitor#expr scx expr
