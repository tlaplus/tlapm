(*
 * Copyright (C) 2013  INRIA and Microsoft Corporation
 *)

Revision.f "$Rev$";;

open Ext
open Format
open Tla_parser
open Property

open Expr.T
open Expr.Subst

let dot = Ctx.dot

(* to fix it to use Ix instead of variable names *)
let crypthash scx cx e =
  let s =
    let b = Buffer.create 10 in
    let fmt = Format.formatter_of_buffer b in
    Expr.Fmt.pp_print_expr (scx, cx) fmt e ;
    Format.pp_print_flush fmt () ;
    Buffer.contents b
  in
  "h" ^ String.sub (Digest.to_hex (Digest.string s)) 0 30

(* for using it with PLTL it is enough to have a trivial coalescing returning a
 * unique constant depending on all symbols in it, TODO make a smarter (according
 * to document) coalsecing later*)
let coalesce cx e =
  Opaque (crypthash cx dot e) @@ e

let rec int_compr ls = function
  | 0 -> ls
  | m -> m :: (int_compr ls (m-1))

let coalesce_operator cx op args =
  let nm = match op.core with
    | Operator (nm, _) -> nm
    | _ -> failwith "expected operator" in
  let star e = Opaque "*" @@ e in
  let args =
    let map_fun (id, arg) =
      if (Expr.Constness.is_const arg || Expr.Leibniz.is_leibniz op (id-1)) then star arg
      else arg in
    List.map map_fun (List.combine (int_compr [] (List.length args)) args) in
  coalesce cx (Apply (Opaque nm.core @@ nm, args) @@ op)

(* Coalescing of modal operators follows the paper. A main difference is that we
 * do not compute a set of bound rigid variables since all variables are
 * considered bound in TLA
 *)
module IxSet = Set.Make (
  struct type t = expr
  let compare e1 e2 = match (e1.core,e2.core) with
  | (Ix n, Ix m) -> compare n m
  | _ -> failwith "illegal type"
end)

let coalesce_modal e =
  let coalesce_prime_var cx m =
    Printf.sprintf "%s#prime" (
      match (get_val_from_id cx m).core with
      | Fresh (s, _, _, _) | Flex (s) -> s.core
      | _ -> failwith "expecting only variables but got a Fact or Def"
    ) in
  let compute_vars cx e =
    let vars = ref IxSet.empty in
    let vars_visitor = object (self)
      (* a visitor for accumulating free variables indices
       * in tlapm if m is an id of a bound variable, then n < m are also bound
       * variables. therefore, we only keep track of the biggest id at each
       * point*)
      inherit [int] Expr.Visit.iter as isuper
      method expr ((max_bound_id, cx) as scx) e = match e.core with
      | Ix n -> begin
        match (get_val_from_id cx n).core with
        | Fresh _
        | Flex _ ->
            if (n > max_bound_id) then vars := IxSet.add (Ix (n -
            max_bound_id) @@ e) !vars
        | _ -> isuper#expr scx e
      end
      | Lambda (ls, _) ->
          isuper#expr (max_bound_id + (List.length ls), cx) e
      | Quant (_, ls, _) ->
          let (_, cx) = self#bounds scx ls in
          isuper#expr (max_bound_id + (List.length ls), cx) e
      | Tquant (_, ls, _) ->
          isuper#expr (max_bound_id + (List.length ls), cx) e
      | _ -> isuper#expr scx e
    end in
    let () = vars_visitor#expr (0, cx) e in
    IxSet.elements !vars in
  let visitor = object (self)
    inherit [unit] Expr.Visit.map as super
    method expr scx e = match e.core with
    (* modal expressions *)
    | Apply ({core = Internal (Builtin.Prime | Builtin.Box _  | Builtin.Diamond
    | Builtin.Leadsto | Builtin.ENABLED) as sym}, args) -> begin
      match (sym, compute_vars (snd scx) e, args) with
      | (_,[],_) -> coalesce (snd scx) e
      | (Internal Builtin.Prime, [{core = Ix m}], [{core = Ix n}]) when n = m ->
        Opaque (coalesce_prime_var (snd scx) m) @@ e
      | (_,vars,_) ->
        (Apply (coalesce (snd scx) e, vars)) @@ e
    end
    | Apply ({core = Ix n}, args) -> begin match (get_val_from_id (snd scx) n).core with
      (* user defined operators *)
      | Defn ({core = Operator (_, _)} as op, _,_,_) ->
        let not_to_coalesce =
          let funn (id, arg) =
            if (Expr.Constness.is_const arg || Expr.Leibniz.is_leibniz op (id-1)) then true
            else false in
          List.for_all funn (List.combine (int_compr [] (List.length args)) args) in
        if (not_to_coalesce) then super#expr scx e
        else Apply (coalesce_operator (snd scx) op args, List.map (self#expr scx) args) @@ e
      | _ -> super#expr scx e
    end
    | _ -> super#expr scx e
  end in
  visitor#expr ((), Deque.empty) e
