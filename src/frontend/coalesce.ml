(*
 * frontend/coalesce.ml
 *
 *
 * Copyright (C) 2013-2019  INRIA and Microsoft Corporation
 *)

open Ext
open Format
open Tla_parser
open Property

open Expr.T
open Expr.Subst

let dot = Ctx.dot


let string_to_hex s =
    (* Return hexadecimal digest of string `s`. *)
    Digest.to_hex (Digest.string s)


let shorter_string_to_hex s =
    (* Return 5-character hexadecimal digest of string `s`. *)
    String.sub (string_to_hex s) 0 5


(* to fix it to use Ix instead of variable names *)
let crypthash scx cx e =
    let s =
        let b = Buffer.create 10 in
        let fmt = Format.formatter_of_buffer b in
        Expr.Fmt.pp_print_expr (scx, cx) fmt e ;
        Format.pp_print_flush fmt () ;
        Buffer.contents b
    in
    "h" ^ shorter_string_to_hex s

(* for using it with PLTL it is enough to have a trivial coalescing returning a
 * unique constant depending on all symbols in it, TODO make a smarter (according
 * to document) coalsecing later*)
let coalesce cx e =
  Opaque (crypthash cx dot e) @@ e


let rec int_compr ls = function
  (* Return the list of numbers `[m; m-1; ..; 1]`. *)
  | 0 -> ls
  | m -> m :: (int_compr ls (m - 1))


let indexed_args args =
    (* Combine each item in `args` with an index to form the list
    `[(n, args[0]); (n - 1, args[1]); ..; (1, args[n - 1])]`
    *)
    let n = List.length args in
    List.mapi (fun i x -> (n - i, x)) args


let coalesce_operator cx op args =
    let nm = match op.core with
        | Operator (nm, _) -> nm
        | _ -> failwith "expected operator" in
    let star e = Opaque "*" @@ e in
    let args =
        let map_fun (id, arg) =
        if (
                ((Expr.Levels.get_level arg) = 0)
                || Expr.SubstOp.get_substitutive_arg op (id - 1)) then
            star arg
        else
            arg in
        List.map map_fun (indexed_args args) in
    let op_ = Opaque nm.core @@ nm in
    let expr_ = Apply (op_, args) @@ op in
    coalesce cx expr_


let coalesce_apply cx expr =
    (* Return string that uniquely describes operator application.

    Uniquely here means up to hash equality.
    *)
    match expr.core with
    | Apply (op, args) ->
        let op = Expr.SubstOp.compute_subst cx op in
        let op_name = Expr.Fmt.string_of_expr cx op in
        let op_e = (Internal TRUE) @@ expr in
        let defn = Operator (op_name @@ expr, op_e) @@ expr in
        (* print_string (Expr.Fmt.string_of_expr cx expr); *)
        assert (
            (Expr.Levels.has_level expr)
            && (Expr.SubstOp.has_substitutive expr));
        coalesce_operator cx defn args
    | _ -> assert false


(* Coalescing of modal operators follows the paper. A main difference is that we
 * do not compute a set of bound rigid variables since all variables are
 * considered bound in TLA
 *)
module IxSet = Set.Make (
    struct type t = expr
    let compare e1 e2 = match (e1.core, e2.core) with
        | (Ix n, Ix m) -> compare n m
        | _ -> failwith "illegal type"
end)


let level_to_kind level =
    match level with
    | 0 -> "CONSTANT"
    | 1 -> "STATE"
    | 2 -> "ACTION"
    | 3 -> "TEMPORAL"
    | _ -> assert false


(* If the constant `with_unique_identifiers` is `true`,
then include in the coalesced identifiers the location
of their definition in source code.
*)
let with_unique_identifiers: bool = false


let rename_with_loc cx e =
    (* Rename declared operators to include location information. *)
    let visitor = object (self)
        inherit [unit] Expr.Visit.map_rename as super

        method rename cx hyp name =
            let locus = shorter_string_to_hex (format_locus hyp) in
            let locus = if with_unique_identifiers then locus else "" in
            match hyp.core with
            | Fresh (nm, shp, kind, dom) ->
                let kind_str = match kind with
                    | Constant -> "CONSTANT"
                    | State -> "STATE"
                    | Action -> "ACTION"
                    | Temporal -> "TEMPORAL"
                    | Unknown -> "Unknown"
                    in
                let name = kind_str ^ "_" ^ nm.core ^ "_" ^ locus in
                let nm = name @@ nm in
                let h = Fresh (nm, shp, kind, dom) @@ hyp in
                (h, nm)
            | Flex var_name ->
                let str = "VARIABLE" ^ "_" ^ var_name.core ^ "_" ^ locus in
                let var_name = str @@ var_name in
                let h = Flex var_name @@ hyp in
                (h, name)
            | Defn (df, wd, vis, ex) ->
                let (core, name) = begin match df.core with
                    | Recursive (name, _) -> (df.core, name)
                    | Operator (nm, expr) ->
                        let expr = Expr.Levels.compute_level cx expr in
                        let level = Expr.Levels.get_level expr in
                        let kind_str = level_to_kind level in
                        let name = kind_str ^ "_" ^ nm.core ^ "_" ^ locus in
                        let nm = name @@ nm in
                        (Operator (nm, expr), nm)
                    | Instance (name, _) -> (df.core, name)
                    | Bpragma (name, _, _) -> (df.core, name)
                    end in
                let df = core @@ df in
                (* Same name for defined operators because `LET` definitions
                have been expanded. Definitions from only module scope remain.
                These definitions do not include multiple operators with the
                same identifier.
                *)
                let h = Defn (df, wd, vis, ex) @@ hyp in
                (h, name)
            | Fact (e, vis, tm) ->
                assert false
    end in
    visitor#expr ((), cx) e


let coalesce_primed_var cx index =
    (* Append `"#prime"` to the identifier name. *)
    let name =
        let hyp = get_val_from_id cx index in
        match hyp.core with
        | Fresh (name, _, _, _) -> name.core
        | Flex name -> name.core
        | _ -> failwith "Expecting variable or constant but got a Fact or Def"
        in
    Printf.sprintf "%s" (name ^ "#prime")


let vars_visitor = object (self: 'self)
    (* A visitor for accumulating free variables and free constants. *)
    inherit [int] Expr.Visit.iter_visible_hyp as super

    val mutable vars = ref IxSet.empty

    method compute cx e =
        let vars = ref IxSet.empty in
        let max_bound_idx = 0 in
        self#expr (max_bound_idx, cx) e;
        IxSet.elements !vars

    method expr ((max_bound_idx, cx) as scx) e =
        match e.core with
        | Ix n -> begin
            let hyp = get_val_from_id cx n in
            match hyp.core with
            | Fresh _
            | Flex _ ->
                if (n > max_bound_idx) then
                    begin
                    let m = n - max_bound_idx in
                    vars := IxSet.add (Ix m @@ e) !vars
                    end
            | Defn ({core = Operator (_, expr)}, _, Visible, _)
                when
                not ((Expr.Levels.get_level expr) = 0) ->
                (* TODO: what about considering hidden nonconstant
                operators as variables ?
                Different operator applications could be to different variables
                so there occurrences would need to be represented as different
                variables.
                *)
                (* visit both `Hidden` and `Visible` definitions
                The function `Backend.Prep.expand_defs` removes from the
                sequent context visible definitions and pragma definitions
                (both visible and hidden pragma definitions).)
                *)
                let scx = Expr.T.scx_front scx n in
                super#expr scx expr
            | _ -> super#expr scx e
            end
        | Lambda (ls, _) ->
            let max_bound_idx = max_bound_idx + (List.length ls) in
            super#expr (max_bound_idx, cx) e
        | Let (defs, expr) ->
            let scx = self#defns scx defs in
            self#expr scx expr
        | Quant (_, ls, expr) ->
            let scx_ = self#bounds scx ls in
            self#expr scx_ expr
        | Tquant (_, ls, _) ->
            let max_bound_idx = max_bound_idx + (List.length ls) in
            super#expr (max_bound_idx, cx) e
        | Choose (v, optdom, expr) ->
            let bound = match optdom with
                | None -> Unbounded
                | Some dom ->
                    self#expr scx dom ;
                    Bounded (dom, Visible)
                in
            let hyp = Fresh (v, Shape_expr, Constant, bound) @@ v in
            let max_bound_idx = max_bound_idx + 1 in
            let cx_ = Deque.snoc cx hyp in
            let scx_ = (max_bound_idx, cx_) in
            self#expr scx_ expr
        | SetSt (v, dom, expr) ->
            self#expr scx dom;
            let bound = Bounded (dom, Visible) in
            let hyp = Fresh (v, Shape_expr, Constant, bound) @@ v in
            let cx_ = Deque.snoc cx hyp in
            let max_bound_idx = max_bound_idx + 1 in
            let scx_ = (max_bound_idx, cx_) in
            self#expr scx_ expr
        | SetOf (expr, bs) ->
            let scx_ = self#bounds scx bs in
            self#expr scx_ expr
        | Fcn (bs, expr) ->
            let scx_ = self#bounds scx bs in
            self#expr scx_ expr
        | _ -> super#expr scx e

    method defn scx df =
        let (max_bound_idx, cx) = super#defn scx df in
        let max_bound_idx = max_bound_idx + 1 in
        let scx = (max_bound_idx, cx) in
        scx

    method bounds scx bs =
        let (max_bound_idx, cx) = super#bounds scx bs in
        let max_bound_idx = max_bound_idx + (List.length bs) in
        let scx = (max_bound_idx, cx) in
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


let compute_vars cx e =
    vars_visitor#compute cx e


let coalesce_modal_visitor = object (self)
    inherit [unit] Expr.Visit.map_visible_hyp as super

    method expr ((_, cx) as scx) e =
        match e.core with
        (* modal expressions *)
        | Apply ({core=Internal (Builtin.Prime | Builtin.StrongPrime)},
                [{core=Ix n}]) when
                (let hyp = get_val_from_id cx n
                in match hyp.core with
                | Fresh _ -> true
                | Flex _ -> true
                | _ -> false)
                ->
            Opaque (coalesce_primed_var cx n) @@ e
        | Apply ({core = Internal (
                Builtin.Prime | Builtin.StrongPrime
                | Builtin.Box _ | Builtin.Diamond
                | Builtin.Leadsto | Builtin.ENABLED | Builtin.Cdot
                | Builtin.UNCHANGED)}, args) ->
            begin
            let vars = compute_vars cx e in
            let op = coalesce cx e in
            match vars with
            | [] -> op
            | _ -> Apply (op, vars) @@ e
            end
        | Apply ({core = Ix n} as index, args) ->
            let hyp = get_val_from_id cx n in
            begin match hyp.core with
            (* user defined operators *)
            | Defn ({core = Operator _} as op, _, _, _) ->
                let not_to_coalesce =
                    let f (id, arg) =
                        let arg = Expr.Levels.compute_level cx arg in
                        if (
                                ((Expr.Levels.get_level arg) = 0)
                                || Expr.SubstOp.get_substitutive_arg
                                        op (id - 1)) then
                            true
                        else false
                        in
                    List.for_all f (indexed_args args) in
                if not_to_coalesce then
                    super#expr scx e
                else begin
                    Apply (coalesce_operator cx op args,
                        List.map (self#expr scx) args) @@ e end
            | Flex _ -> super#expr scx e
            | Fresh (op_name, _, kind, _) ->
                begin
                let coalesced_op = op_name in
                match kind with
                | Constant ->
                    (* let op = Opaque (coalesced_op.core) @@ index in *)
                    let op = index in
                    let args_ = List.map (self#expr scx) args in
                    Apply (op, args_) @@ e
                | _ ->
                    let expr = noprops (Internal TRUE) in
                    let op_ = (Operator (coalesced_op, expr)) @@ index in
                    coalesce_operator cx op_ args
                end
            | Fact _ -> (* unexpected `Fact` *)  assert false
            | Defn ({core=Recursive _}, _, _, _) ->
                (* not implemented case *)  assert false
            | Defn ({core=Instance _}, _, _, _) ->
                (* `INSTANCE` statements have been expanded *)  assert false
            | Defn ({core=Bpragma _}, _, _, _) ->
                (* unexpected back-end proof directive *)  assert false
            end
        | _ -> super#expr scx e
end


let coalesce_modal cx e =
    let e = rename_with_loc cx e in
    let scx = ((), cx) in
    coalesce_modal_visitor#expr scx e
