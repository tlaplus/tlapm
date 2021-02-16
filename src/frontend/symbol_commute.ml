(*
 * frontend/symbol_commute.ml
 *
 * For coalescing to be affective, we must try to push problematic symbols up
 * the term as much as possible. This will cause the coalesced part of the term
 * to be smaller and therefore will preserve as much of the logical content as
 * possible.
 *
 * For example, pushing primes to the variables is required in order for the coalescing of primes to be a
 * complete procedure. For other symbols we will not have compelteness but we
 * would like for the procedure to be as compelte as possible and therefore we
 * support here a variety of commuting algorithms.
 *
 * Copyright (C) 2014  INRIA and Microsoft Corporation
 *)

open Ext
open Format
open Tla_parser
open Property

open Expr.T
open Expr.Visit
open Proof.T
open Expr.Subst

(* all symbols must be idempotent? *)
module OrderedSymbol =
struct
  type t = expr
  let compare e1 e2 = match (e1.core,e2.core) with
  | (Apply ({core = Internal b1},_), Apply ({core = Internal b2},_)) -> if b1 < b2 then -1
                                  else if b2 < b1 then 1
                                  else 0
  | _ -> raise Not_found
end;;

module SymbolMap = Map.Make (OrderedSymbol)

let symbol_commute sym_map =
  let visitor = object
    inherit [unit] Expr.Visit.map as super
    method expr scx e =
      try
        let (ivisitor,stripper) = SymbolMap.find e sym_map in
        ivisitor#expr scx (stripper e)
      with
        | Not_found -> super#expr scx e
  end in
  fun e ->
    let cx = Deque.empty in
    let scx = ((),cx) in
    try visitor#expr scx e with
    | Failure msg ->
        Util.eprintf ~at:e
          "@[<v2>offending expr =@,%t@]@."
          (fun ff -> Expr.Fmt.pp_print_expr ((snd scx), Ctx.dot) ff e) ;
          prerr_string "Message: "; prerr_string msg;
        failwith msg

