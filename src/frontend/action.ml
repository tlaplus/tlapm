(*
 * frontend/action.ml
 * The action frontend is responsible on transforming obligations containing
 * actions to purely first-order obligations
 * 1) expend definitions of UNCHANGED, [A]_v and <<A>>_v
 * 2) distribute primes over constant operators
 * 3) for a leibniz non-constant operator op, distribute primes over hash(op) (we
 * treat all non-constant operators right now, see comment below)
 * 4) primed atoms: constant atoms -> a, else -> hash(a)
 * 5) coalesce all non-leibniz operators and primed non-leibniz operators
 * (postponed, see comment below).
 *
 * comment:
 * this will be done only after we integrate the SANY parser to TLAPM as we dont
 * have the leibnizicy information right now in TLAPM.

 * Copyright (C) 2013-2019 INRIA and Microsoft Corporation
 *)

Revision.f "$Rev$";;

open Ext
open Format
open Tla_parser
open Property

open Expr.T
open Proof.T
open Expr.Subst

open Symbol_commute
open Coalesce

module B = Builtin

type ctx = int Ctx.ctx
let dot : ctx = Ctx.dot
let bump : ctx -> ctx = Ctx.bump
let length : ctx -> int = Ctx.length



let cook x = "is" ^ pickle x

let adj cx v =
  let cx = Ctx.push cx (pickle v.core) in
  (cx, pickle (Ctx.string_of_ident (fst (Ctx.top cx))))

let rec adjs cx = function
  | [] -> (cx, [])
  | v :: vs ->
      let (cx, v) = adj cx v in
      let (cx, vs) = adjs cx vs in
      (cx, v :: vs)

let lookup_id cx n =
  assert (n > 0 && n <= Ctx.length cx) ;
  let id = Ctx.string_of_ident (fst (Ctx.index cx n)) in
  id

let crypthash (cx : ctx) e =
  let s =
    let b = Buffer.create 10 in
    let fmt = Format.formatter_of_buffer b in
    Expr.Fmt.pp_print_expr (Deque.empty, cx) fmt e ;
    Format.pp_print_flush fmt () ;
    Buffer.contents b
  in
  "hash'" ^ Digest.to_hex (Digest.string s)

(* Note: we append "#prime" to get a variable name that is not in the
   space of regular TLA identifers. It will be transcoded by
   [Tla_parser.pickle] into a regular identifier without clash.
*)
let prime_replace str = Opaque (str ^ "#prime")

let eliminate_primes =
  let visitor = object (self : 'self)
    inherit [unit] Expr.Visit.map_visible_hyp as super
    method expr scx e = match e.core with
      | Apply ({ core = (Internal B.Prime | Internal B.StrongPrime) }, args) ->
          let e2 = List.hd args in begin
        match args with
          | [{core = Ix n}] -> begin
            match Deque.nth ~backwards:true (snd scx) (n - 1) with
            | Some {core = Fresh (name,_,_,_)} -> {e2 with core = prime_replace
            name.core}
            | Some {core = Flex {core = name}} -> {e2 with core = prime_replace  name}
            | Some {core = Defn ({core = Operator (name,_)},_,_,_)} -> {e2 with core =
              prime_replace name.core }
            | _ -> failwith "Action.eliminate_primes: cannot find DB index"
          end
            (* TODO:
            since we cannot distinguish between leibniz and non-leibniz
            operators, we treat all of them as leibniz and we cannot obtain a
            primed application. We need to change distribute_primes to check for
            leibnizity and in case of non-leibniz, instead of prime-distribute,
            we jst need to return the primed application. In the prime
            elimination we need to coalesce the application
            *)
          | [{ core = Apply (op, args)}] -> failwith "Action.eliminate_primes: \
            should be impossible for now, see comment in code"
          | _ -> failwith "Action.eliminate_primes: unknown arguments for Prime"
      end
      | _ -> super#expr scx e

  end in
  fun scx e ->
    let ret = try visitor#expr scx e with
    | Failure msg ->
        Util.eprintf ~at:e
          "@[<v2>offending expr =@,%t@]@."
          (fun ff -> Expr.Fmt.pp_print_expr ((snd scx), Ctx.dot) ff e) ;
          prerr_string "Message: "; prerr_string msg;
        failwith msg
    in
    ret

let expand_prime_defs scx ob =
  let ob = Expr.Tla_norm.expand_action scx ob in
  let ob = Expr.Tla_norm.expand_unchanged scx ob in
  ob

let coalesce_non_leibniz ob = ob

(** Aux functions for commuting symbols **)

(* all symbols must be idempotent? *)

(* Prime commuter:
  * prime should be always commutted over applications since there is an
  * assumption that SANY will prevent applying a non-leibniz operator.
  * prime should not commute over other structures like sequents, etc.
  * Note1: we assume that all primed expressions must be leibniz and that
  * this is determined by SANY!
  * *)
let prime_commuter =
  let prime e = Apply (Internal Builtin.Prime @@ e, [e]) @@ e in
  object (self)
    inherit [unit] Expr.Visit.map_visible_hyp as super
(*    method expr scx e =
      (* all constant expression cancel the modality *)
      if (Expr.Constness.is_const e) then e
      else match e.core with
      (* atoms, whether definitios, variables, constants, etc, are assumed here
       * to be non-constant and therefpre prime cannot be further commuted *)
      | Ix n -> prime e
      (* we cannot commute primes over this symbols *)
      |  Opaque _ | Sequent _ | Let _ | Tquant _ | Tsub _ |
        Fair _  -> prime e
      (* for the rest, we just commute the prime one step down the structure of
       * the expression *)
      | _ -> super#expr scx e*)
    method expr scx e = match e.core with
         | Ix n -> begin
             match (get_val_from_id (snd scx) n).core with
             | Fresh (_, _, Constant, _) -> e
             | Defn ({core = Operator (_,op)}, _, _, _) when
             ((Expr.Levels.get_level op) = 0) -> e
             | _ -> prime e
           end
         | Apply ({core=Internal ENABLED; _}, _)
         | Opaque _ | Sequent _ | Let _ ->
            prime e
         | Apply ({core=Internal
                (UNCHANGED | Cdot |
                 Leadsto | Actplus | Box _ | Diamond); _}, _)
         | Tquant _ | Sub _ | Tsub _ | Fair _ ->
            assert false
         | _ -> super#expr scx e
  end

(* Box commuter:
  * Box should be computed over /\ and the two foralls
  * Box should be cancelled over constant expressions
  * *)
let box_commuter =
  let box e = Apply (Internal (Builtin.Box true) @@ e, [e]) @@ e in
  object (self)
    inherit [unit] Expr.Visit.map_visible_hyp as super
    method expr scx e =
      (* all constant expression cancel the modality *)
      if ((Expr.Levels.get_level e) = 0) then e
      else match e.core with
      (* Conjunctions *)
      | Apply ({core = Internal Builtin.Conj}, _)
      (* Universal quantifiers *)
      | Quant (Forall, _,_)
      | Tquant (Forall, _,_) ->
          super#expr scx e
      | _ -> box e
  end

(* Diamond commuter:
  * Dia should be computed over \/ and the two exists
  * Dia should be cancelled over constant expressions
  * *)
let dia_commuter =
  let dia e = Apply (Internal Builtin.Diamond @@ e, [e]) @@ e in
  object (self)
    inherit [unit] Expr.Visit.map_visible_hyp as super
    method expr scx e =
      (* all constant expression cancel the modality *)
      if ((Expr.Levels.get_level e) = 0) then e
      else match e.core with
      (* Disjunctions *)
      | Apply ({core = Internal Builtin.Disj}, _)
      (* Existential quantifiers *)
      | Quant (Exists, _,_)
      | Tquant (Exists, _,_) ->
          super#expr scx e
      | _ -> dia e
  end

(* general functions for commuting symbols
 * *)
let apply_stripper = function
  | {core = Apply(_,[e])} -> e
  | _ -> failwith "apply_stripper can be applied only to mondaic applications"


let mymap =
  let m = SymbolMap.empty in
  let m = SymbolMap.add (noprops (Apply (noprops (Internal Builtin.Prime), [])))
  (prime_commuter, apply_stripper) m in
  let m = SymbolMap.add (noprops (Apply (noprops (Internal (Builtin.Box true)), [])))
  (box_commuter, apply_stripper) m in
  let m = SymbolMap.add (noprops (Apply (noprops (Internal Builtin.Diamond), [])))
  (dia_commuter, apply_stripper) m in
  m

(* END of aux functions section *)


let process_eob ob =
  let cx = Deque.empty in
  let scx = ((), cx) in
  let ob = Expr.Levels.compute_level cx ob in
  let ob = Expr.SubstOp.compute_subst cx ob in
  let ob = expand_prime_defs scx ob in
  let ob = symbol_commute mymap ob in
  let ob = coalesce_modal cx ob in
  ob

let process_obligation ob =
  match (process_eob (noprops (Sequent ob.obl.core))).core
  with
  | Sequent sq -> { ob with obl = { ob.obl with core = sq } }
  | _ -> failwith "Proof_prep.normalize"
