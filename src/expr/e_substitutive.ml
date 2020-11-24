(*
    expr/e_substitutive.ml --- compute substitutivity information
*)
open Ext
open Property

open E_t


type substitutive_args = bool array

let substitutive_arg: substitutive_args pfuncs =
    Property.make "Expr.Substitutive.substitutive_arg"
let has_substitutive x = Property.has x substitutive_arg
let get_substitutive x = Property.get x substitutive_arg
let get_substitutive_arg x n =
    assert (has_substitutive x);
    let arr = get_substitutive x in
    Array.get arr n


let make_lambda_hyps params =
    let hyps = List.map
        (fun (v, shp) ->
            Fresh (v, shp, Unknown, Unbounded) @@ v)
        params in
    hyps


class compute_substitutivity_array = object (self: 'self)
    inherit [bool * int * bool ref] E_visit.iter as super

    method compute cx e =
        match e.core with
            | Lambda (params, expr) ->
                let hyps = make_lambda_hyps params in
                let cx = Deque.append_list cx hyps in
                let n = List.length params in
                let f i =
                    let r = ref true in
                    let s = (true, i + 1, r) in
                    self#expr (s, cx) expr;
                    !r in
                assert (n > 0);
                Array.init n f
            | _ ->
                Array.make 0 true

    method expr (((scope, index, r), cx) as scx) e =
        match e.core with
        | Ix n when (n = index) && (scope = false) ->
            r := false
        | Lambda (params, expr) ->
            let hyps = make_lambda_hyps params in
            let cx = Deque.append_list cx hyps in
            let index = index + List.length params in
            let s = (scope, index, r) in
            self#expr (s, cx) expr
        | Apply ({core=Internal (Builtin.Prime | StrongPrime
                | Box _ | Diamond | ENABLED | UNCHANGED)},
                [expr]) ->
            let scope = false in
            let s = (scope, index, r) in
            self#expr (s, cx) expr
        | Sub (_, e1, e2)
        | Apply ({core=Internal (Builtin.Leadsto | Actplus | Cdot)},
                [e1; e2]) ->
            let scope = false in
            let s = (scope, index, r) in
            self#expr (s, cx) e1;
            self#expr (s, cx) e2
        | Apply ({core=Ix n}, args) ->
            let hyp = E_t.get_val_from_id cx n in
            begin match hyp.core with
            | Defn ({core = Operator _} as op, _, _, _) ->
                List.iteri
                    (fun i arg ->
                        let scope = get_substitutive_arg op i in
                        let s = (scope, index, r) in
                        self#expr (s, cx) arg)
                    args
            | _ -> super#expr scx e
            end
        | Tquant (_, ls, _) ->
            let index = index + (List.length ls) in
            let s = (scope, index, r) in
            super#expr (s, cx) e
        | Choose (v, optdom, expr) ->
            let bound = match optdom with
                | None -> Unbounded
                | Some dom ->
                    self#expr scx dom ;
                    Bounded (dom, Visible)
                in
            let hyp = Fresh (v, Shape_expr, Constant, bound) @@ v in
            let index = index + 1 in
            let cx = Deque.snoc cx hyp in
            let s = (scope, index, r) in
            let scx = (s, cx) in
            self#expr scx expr
        | SetSt (v, dom, expr) ->
            self#expr scx dom;
            let bound = Bounded (dom, Visible) in
            let hyp = Fresh (v, Shape_expr, Constant, bound) @@ v in
            let cx = Deque.snoc cx hyp in
            let index = index + 1 in
            let s = (scope, index, r) in
            let scx = (s, cx) in
            self#expr scx expr
        | _ -> super#expr scx e

    method defn scx df =
        let ((scope, index, r), cx) = super#defn scx df in
        let index = index + 1 in
        let scx = ((scope, index, r), cx) in
        scx

    method bounds scx bs =
        let ((scope, index, r), cx) = super#bounds scx bs in
        let index = index + (List.length bs) in
        let scx = ((scope, index, r), cx) in
        scx

    method instance scx inst =
        assert false  (* `INSTANCE` statements have been expanded *)

    method bound scx b =
        assert false  (* unused method *)

    method hyp scx h =
        assert false  (* sequents do not occur in expressions *)

    method hyps scx hs =
        assert false  (* sequents do not occur in expressions *)
end


let make_array cx e =
    let visitor = new compute_substitutivity_array in
    visitor#compute cx e


let shape_to_arity shp =
    match shp with
    | Shape_expr -> assert false
    | Shape_op n -> assert (n >= 1); n


class substitutive_op_visitor = object (self: 'self)
    inherit [unit] E_visit.map_visible_hyp as super

    method expr ((s, cx) as scx) e =
        if has_substitutive e then
            e
        else begin
        match e.core with
        | Apply ({core=Internal
                (Mem | Notmem | Subseteq | Setminus | Cap | Cup)} as op,
                args) ->
            let n = List.length args in
            assert (n = 2);
            let args = List.map (self#expr scx) args in
            let expr = Apply (op, args) @@ e in
            let e_ = E_levels.compute_level cx e in
            let level = E_levels.get_level e_ in
            let ar = if level = 0 then
                    Array.make n true
                else
                    Array.make n false in
            assign expr substitutive_arg ar
        | Apply ({core=Internal
                (Prime | StrongPrime | ENABLED | Cdot | UNCHANGED
                    | Box _ | Diamond | Leadsto | Actplus)} as op, args) ->
            let n = List.length args in
            assert (n >= 1);
            let args = List.map (self#expr scx) args in
            let expr = Apply (op, args) @@ e in
            let ar = Array.make n false in
            assign expr substitutive_arg ar
        | Sub (modal_op, action, subscript) ->
            let action = self#expr scx action in
            let subscript = self#expr scx subscript in
            let expr = Sub (modal_op, action, subscript) @@ e in
            let ar = Array.make 2 false in
            assign expr substitutive_arg ar
        | Apply ({core=Ix n} as op_index, args) ->
            let n_args = List.length args in
            assert (n_args > 0);
            let hyp = E_t.get_val_from_id cx n in
            begin match hyp.core with
            | Fresh (name, shp, kind, _) ->
                begin
                let arity = shape_to_arity shp in
                assert (arity = n_args);
                let is_constant_op = match kind with
                    | Constant -> true
                    | _ -> false in
                let args = List.map (self#expr scx) args in
                let ar = Array.make n_args is_constant_op in
                let op = assign op_index substitutive_arg ar in
                let expr = Apply (op, args) @@ e in
                let ar = Array.make n_args is_constant_op in
                assign expr substitutive_arg ar
                end
            | Defn ({core=Operator (_, expr)}, _, _, _) ->
                begin match expr.core with
                | Lambda (params, _) ->
                    let args = List.map (self#expr scx) args in
                    let is_subst = not (List.exists
                        (fun (_, shp) -> match shp with
                            | Shape_op _ -> true
                            | _ -> false)
                        params) in
                    let ar = Array.make n_args is_subst in
                    let op = assign op_index substitutive_arg ar in
                    let expr = Apply (op, args) @@ e in
                    let ar = Array.make n_args is_subst in
                    assign expr substitutive_arg ar
                | _ ->
                    let e = super#expr scx e in
                    let ar = Array.make n_args true in
                    assign e substitutive_arg ar
                end
            | _ ->
                (* TODO: logic in support of this pattern case *)
                let args = List.map (self#expr scx) args in
                let ar = Array.make n_args true in
                let op = assign op_index substitutive_arg ar in
                let expr = Apply (op, args) @@ e in
                let ar = Array.make n_args true in
                assign expr substitutive_arg ar
            end
        | _ -> super#expr scx e
        end

    method hyp scx h =
        if has_substitutive h then
            (scx, h)
        else begin
        match h.core with
        | Defn ({core=Operator (name, expr)} as op, wd, visibility, e) ->
            let expr = self#expr scx expr in
            let ar = make_array (snd scx) expr in
            let op = Operator (name, expr) @@ op in
            let op = assign op substitutive_arg ar in
            let h = Defn (op, wd, visibility, e) @@ h in
            (E_visit.adj scx h, h)
        | _ -> super#hyp scx h
        end

    method pform scx p =
        if has_substitutive p then p else super#pform scx p

    method defn scx p =
        if has_substitutive p then p else super#defn scx p
end


let compute_subst cx e =
    let visitor = new substitutive_op_visitor in
    visitor#expr ((), cx) e
