(*
 * backend/smt/smtcommons.ml --- SMT backend commons
 *
 * Authors: Hernán Vanzetto <hernan.vanzetto@inria.fr>
 *
 * Copyright (C) 2011-2012  INRIA and Microsoft Corporation
 *)

Revision.f "$Rev: 33173 $";;

open Ext
open Property

open Expr.T
open Expr.Subst
open Expr.Visit

(* open Printf *)
open List

(* open Tsystem *)

module B = Builtin
module Dq = Deque

module SSet = Set.Make (String)
module SMap = Map.Make (String)

module StringList = struct
    include List
    type t = string list
    let rec compare xs ys =
        begin match xs, ys with
        | [], [] -> 0
        | _, [] -> 1
        | [], _ -> -1
        | x :: xs, y :: ys ->
            let c = String.compare x y in
            if c = 0 then compare xs ys else c
        end
end

module SSMap = Map.Make (StringList)

module Int = struct
  type t = int
  let compare i j = if i < j then -1 else if i = j then 0 else 1
end

module ISet = Set.Make (Int)

(****************************************************************************)
(* Debugging, printing errors and warning                                   *)
(****************************************************************************)

(** Level 0 = only errors, 1 = statistics, 2 = basic debug, 3 = full debug, ... *)
let verbosity = ref 0

let ifprint n =
  if n <= !verbosity then begin
    Format.print_flush () ;
    Format.kfprintf (fun ppf -> Format.fprintf ppf "\n%!") Format.err_formatter
  end else
    Format.ifprintf Format.err_formatter

let print_prop () = Expr.Fmt.pp_print_expr (Dq.empty, Ctx.dot)
(* let pp_ex e = (Expr.Fmt.pp_print_expr (Dq.empty, Ctx.dot)) e *)

let pps_ex (cx,e) = Util.sprintf ?nonl:(Some ()) "@[%a@]" (print_prop ()) ((* opaque cx *) e)

(****************************************************************************)
(* Combinators                                                              *)
(****************************************************************************)

let ( |> ) x f = f x
let ( |>> ) (x, y) f = (f x, y)
let ( ||> ) (x, y) f = (x, f y)
let kk x y = ignore x ; y
let tap f = fun x -> (f x; x)
let pairself f (x, y) = (f x, f y)

(****************************************************************************)

type provermode = Smtlib | CVC3 | Z3 | Yices | Spass (* DFG format *) | Fof
let mode = ref Smtlib

(** typesystem_mode:
  [0] = Untyped
  [1] = Elementary types
    * uses constraint generator [Typ_cg1.cg]
  [2] = Refinement types
    * uses constraint generator [Typ_cg2.cg]
    * ignores domain checking in FcnApp
 *)
let typesystem_mode =
  begin if Params.debugging "notypes" then ref 0
  else if Params.debugging "types1" then ref 1
  else if Params.debugging "types2" then ref 2
  else ref 1
  end

let filter_true  es = filter (fun e -> match e.core with Internal B.TRUE  -> false | _ -> true) es
let filter_false es = filter (fun e -> match e.core with Internal B.FALSE -> false | _ -> true) es

let boundvar : unit pfuncs = Property.make "Backend.Smt.boundvar"
let has_boundvar x = Property.has x boundvar
let is_bvar cx n =
    assert (n > 0 && n <= length cx) ;
    has_boundvar (nth cx (n - 1))

let turn_first_char is_bv id =
  let is_lowercase s = s.[0] = (Char.lowercase_ascii s.[0]) in
  let is_uppercase s = s.[0] = (Char.uppercase_ascii s.[0]) in
  if !mode = Fof
  (* then (if is_bvar cx n then String.capitalize id else String.uncapitalize id)  *)
  then (if is_bv
        then (if is_uppercase id then id else "X"^id)
        else (if is_lowercase id then id else "x"^id))
  else id

(* FIXME
   1. This is not injective.
*)
let smt_id id =
  if id = "_" then (failwith "SMT bug: identifier \"_\"") else
  let id = if Str.string_match (Str.regexp "^[0-9].*") id 0 then "x"^id else id in
  let rep s r id = Str.global_replace (Str.regexp s) r id in
  id
  |> Tla_parser.pickle
  |> rep "'" "__"

let lookup_id (cx:hyp list) n =
  assert (n > 0 && n <= length cx) ;
	hyp_name (nth cx (n - 1))

let fcnapp = "tla__fcnapp"

let nonbasic_prefix = "a__"
let is_nonbasic_var id =
    try ((String.sub id 0 (String.length nonbasic_prefix)) = nonbasic_prefix) with _ -> false

(****************************************************************************)
(* Formatting Properties 																										*)
(****************************************************************************)

let applyint2u : unit pfuncs = Property.make "Backend.Smt.applyint2u"
let apply_int2u x = Property.has x applyint2u

let applystr2u : unit pfuncs = Property.make "Backend.Smt.applystr2u"
let apply_str2u x = Property.has x applystr2u

let applyu2bool : unit pfuncs = Property.make "Backend.Smt.applyu2bool"
let apply_u2bool x = Property.has x applyu2bool

let boolify_prop : unit pfuncs = Property.make "Backend.Smt.boolify"
let has_boolify x = Property.has x boolify_prop

let fmtasint : unit pfuncs = Property.make "Backend.Smt.fmtasint"
let fmt_as_int x = Property.has x fmtasint

let fmtasbool : unit pfuncs = Property.make "Backend.Smt.fmtasbool"
let fmt_as_bool x = Property.has x fmtasbool

let pattern_prop : Expr.T.expr pfuncs = Property.make "Backend.Smt.pattern_prop"
let has_pattern x = Property.has x pattern_prop
let get_pattern x = Property.get x pattern_prop

(****************************************************************************)

let rec unditto = function
  | (_, _, Domain d) as b1 :: (h,k,Ditto) :: bs ->
      b1 :: unditto ((h,k,Domain d) :: bs)
  | b :: bs -> b :: unditto bs
  | [] -> []

let add_bs_ctx bs cx : hyp list =
  let bs = unditto bs in
  let hyps = mapi begin
    fun n (v, k, dom) ->
      (* let v = assign v boundvar () in *)
      match dom with
      | No_domain -> Fresh (v, Shape_expr, k, Unbounded) @@ v
      | Domain d -> Fresh (v, Shape_expr, k, Bounded (app_expr (shift n) d, Visible)) @@ v
      | _ -> assert false
  end bs in
  rev hyps @ cx

let rec n_to_list = function
  | 0 -> []
  | n -> (n_to_list (n-1)) @ [n]

(* let concat1 fmt ls = String.concat " " (map (Printf.sprintf fmt) ls) *)
(* let concat2 fmt ls = String.concat "," (map (Printf.sprintf fmt) ls) *)

(** Fast, but it does not preserve the order *)
let remove_repeated lst =
  let unique_set = Hashtbl.create (length lst) in
  iter (fun x -> Hashtbl.replace unique_set x ()) lst;
  Hashtbl.fold (fun x () xs -> x :: xs) unique_set []

let remove_repeated_ex es =
  let e_mem e es = exists (Expr.Eq.expr e) es in
  fold_left (fun r e -> if e_mem e r then r else e :: r) [] es

(****************************************************************************)

let ctr = ref 0

let unique_id () = incr ctr ; !ctr

let fresh_name () = "v" ^ string_of_int (unique_id ())
let fresh_id () = string_of_int (unique_id ())

(* let prime s = (* if is_bounded_var s then s else *) s ^ "#prime" *)
(* let unprime_id s = Str.replace_first (Str.regexp "#prime$") "" s *)
let is_prime id = Str.string_match (Str.regexp ".*#prime$") id 0

(** a string could be the same as a variable id *)
let mk_string s = "string__" ^ (smt_id s)

(****************************************************************************)

let rec split_domain q ex bs1 bs2 =
    match bs2 with
    | [] -> (bs1, ex)
    | (v, k, Ditto) :: bss -> split_domain q ex (bs1 @ [v, k, Ditto]) bss
    | _ ->
        let (_, bs2) = app_bounds (shift (length bs1)) bs2 in
        (bs1, Quant (q, bs2, ex) @@ ex)

let rec deconj e =
    match e.core with
    | Apply ({core = Internal B.Conj}, [e1 ; e2]) -> deconj e1 @ deconj e2
    | List (_, [ex]) -> deconj ex
    | List ((And | Refs), ex::es) -> (deconj ex) @ deconj (List (And, es) @@ e)
    | _ -> [e]

let rec dedisj e =
    match e.core with
    | Apply ({core = Internal B.Disj}, [e1 ; e2]) -> dedisj e1 @ dedisj e2
    | List (_, [ex]) -> dedisj ex
    | List (Or, ex::es) -> (dedisj ex) @ dedisj (List (Or, es) @@ e)
    | _ -> [e]

let rec deimpl e =
    match e.core with
    | Apply ({core = Internal B.Implies}, [hyps ; conc]) ->
        let (hs,c) = deimpl conc in
        (deconj (hyps) @ hs, c)
    | _ -> ([], e)

let rec unroll_seq sq =
  let app op xs = Apply (noprops (Internal op), xs) %% [] in
  match Dq.front sq.context with
  | None -> sq.active
  | Some (h, hs) ->
      let sq = { sq with context = hs } in
      begin match h.core with
        | Fresh (v, _, kn, ran) ->
        (* | Fresh (v, Shape_expr, kn, ran) -> *)
            let ran = match ran with
              | Bounded (ran, Visible) -> Domain ran
              | _ -> No_domain
            in
            let ex = unroll_seq sq in
            let hs,c = deimpl ex in
            let ex = match hs with
              | [] -> c
              | [h] -> app B.Implies [h ; c]
              | hs -> app B.Implies [List (And, hs) %% [] ; c]
            in
            Quant (Forall, [v, kn, ran], ex) @@ nowhere
        | Flex v ->
            let v_prime = (v.core ^ "'") @@ v in
            Quant (Forall, [ v, Constant, No_domain
                           ; v_prime, Constant, No_domain ],
                   unroll_seq (app_sequent (shift 1) sq)) @@ nowhere
        | Fact (e, Visible, _) ->
            let hs = deconj e in
            let c = unroll_seq (app_sequent (shift (-1)) sq) in
            begin match hs with
              | [] -> c
              | [h] -> app B.Implies [h ; c]
              | hs -> app B.Implies [List (And, hs) %% [] ; c]
            end
            (* fold_right (fun e f -> app B.Implies [e ; f]) hs c *)
        | _ ->
            let opq = Opaque (hyp_name h) @@ nowhere in
            unroll_seq (app_sequent (scons opq (shift 0)) sq)
      end

(** From sequent [sq] to list of hypotheses [hs] and [conc] expressions, all
    in the same context [scx].
    [scx] |- [ASSUME hs PROVE c]  -->  [scx'] |- [scx* @ hs, c]
      where scx' = scx + NEW variables
            scx* = visible facts from the context
    TOFIX: it needs a context to unroll a sequent [sq] occurring as hypothesis
   *)
let to_list sq =
  let rec collect_hyps scx sq =
    match Dq.front sq.context with
    | Some (h, hs) ->
        let h' = match h.core with
        | Fresh (nm, _, _, Bounded (b, Visible)) ->
            let e = Apply (Internal B.Mem %% [], [Ix 0 @@ nm ; b]) %% [] in
(* Util.eprintf "hs[] = %a // %a" (Expr.Fmt.pp_print_expr (Dq.empty, Ctx.dot)) e (Expr.Fmt.pp_print_expr (snd scx, Ctx.dot)) e ; *)
            [Dq.size (snd scx), e]
        | Fact (e, Visible, _) ->
(* Util.eprintf "hs[] = %a // %a" (Expr.Fmt.pp_print_expr (Dq.empty, Ctx.dot)) e (Expr.Fmt.pp_print_expr (snd scx, Ctx.dot)) e ; *)
            [Dq.size (snd scx), e]
        | _ -> []
        in
        let scx = Expr.Visit.adj scx h in
        h' @ collect_hyps scx { sq with context = hs }
    | None -> []
  in
  let chs = collect_hyps ((),Dq.empty) sq in
  let scx = (),sq.context in
  (** Shift all hyps [chs] to put them in the conclusion's context [scx] *)
  let hs = List.map (fun (sz,e) -> app_expr (shift ((Dq.size (snd scx)) - sz)) e) chs in
  scx,hs,sq.active

(****************************************************************************)
(* Expression visitors                                                      *)
(****************************************************************************)

let map_exp g cx e =
(* Util.eprintf "  map_exp: %a" (print_prop ()) e ;     *)
  let mk x = { e with core = x } in
  let map_exp_bs g cx bs =
    List.map
      begin function
      | (v, k, Domain d) -> (v, k, Domain (g cx d))
      | b -> b
      end
    (unditto bs)
  in
  let iter_es es = List.map (fun e -> g cx e) es in
  match e.core with
  | Quant (q, bs, ex) ->
      let bs = map_exp_bs g cx bs in
      Quant (q, bs, g (add_bs_ctx bs cx) ex) |> mk
  | Apply (op, es) -> Apply (g cx op, iter_es es) |> mk
  | FcnApp (f, es) -> FcnApp (g cx f, iter_es es) |> mk
  | List (b, es) -> List (b, iter_es es) |> mk
  | Dot (r, h) -> Dot (g cx r, h) |> mk
  | Tuple es -> Tuple (iter_es es) |> mk
  | Record rs -> Record (List.map (fun (h,e) -> h, g cx e) rs) |> mk
  | SetOf (ex, bs) ->
      let bs = map_exp_bs g cx bs in
      SetOf (g (add_bs_ctx bs cx) ex, bs) |> mk
  | SetSt (h, dom, ex) ->
      let dom = g cx dom in
      let cx = add_bs_ctx [h, Unknown, Domain dom] cx in
      SetSt (h, dom, g cx ex) |> mk
  | SetEnum es -> SetEnum (iter_es es) |> mk
  | Choose (h, d, ex) ->
      let (d,dom) = match d with
      | Some d -> let d = g cx d in (Some d, Domain d)
      | None -> (None, No_domain)
      in
      let cx = add_bs_ctx [h, Unknown, dom] cx in
      Choose (h, d, g cx ex) |> mk
  | Arrow (e1,e2) -> Arrow (g cx e1, g cx e2) |> mk
  | Expr.T.Fcn (bs, ex) ->
      let bs = map_exp_bs g cx bs in
      Expr.T.Fcn (bs, g (add_bs_ctx bs cx) ex) |> mk
  | Except (f, exs) ->
      let map_exp_ex = function Except_apply ea -> Except_apply (g cx ea) | Except_dot h -> Except_dot h in
      let exs = List.map (fun (es,ex) -> List.map map_exp_ex es, g cx ex) exs in
      Except (g cx f, exs) |> mk
  | Rect rs -> Rect (List.map (fun (h,e) -> h, g cx e) rs) |> mk
  | Product es -> Product (iter_es es) |> mk
  | If (c, t, f) -> If (g cx c, g cx t, g cx f) |> mk
  | Case (es, o) ->
      let es = List.map (fun (p,e) -> g cx p, g cx e) es in
      let o = match o with Some o -> Some (g cx o) | None -> None in
      Case (es, o) |> mk
  | Lambda (xs,ex) ->
      let add_to_ctx cx xs =
        let rec new_ctx_vars = function
        | ({core = h},_) :: xs -> ((Flex ((* quant_id *) h |> mk)) |> mk) :: new_ctx_vars xs
        | [] -> []
        in
        List.rev (new_ctx_vars xs) @ cx
      in
      Lambda (xs, g (add_to_ctx cx xs) ex) |> mk
  | Sequent seq -> g cx (unroll_seq seq)
  | Parens (ex,_) -> g cx ex
  | _ -> e

let e_map (ff:'a -> 'a -> 'a) (base:'a) (g:hyp list -> expr -> 'a) (cx:hyp list) (e:expr) : 'a =
(* Util.eprintf "  e_map: %a" (print_prop ()) e ; *)
  let ( $$ ) x y = ff x y in
  let flatten xs = List.fold_left (fun r e -> e $$ r) base xs in
  let map_es es = List.fold_left (fun r e -> g cx e $$ r) base es in
  let map_bs g cx bs =
    List.fold_left
      begin fun r -> function
      | (_, _, Domain d) -> d :: r
      | b -> r
      end []
    (unditto bs)
    |> map_es
  in
  match e.core with
  | Quant (q, bs, ex) ->
      map_bs g cx bs $$ g (add_bs_ctx bs cx) ex
  | Apply (op, es) -> map_es (op::es)
  | FcnApp (f, es) -> map_es (f::es)
  | List (b, es) -> map_es es
  | Dot (r, h) -> g cx r
  | Tuple es -> map_es es
  | Record rs -> map_es (List.map (fun (_,e) -> e) rs)
  | SetOf (ex, bs) ->
      map_bs g cx bs $$ g (add_bs_ctx bs cx) ex
  | SetSt (h, dom, ex) ->
      g cx dom $$ g (add_bs_ctx [h, Unknown, Domain dom] cx) ex
  | SetEnum es -> map_es es
  | Choose (h, d, ex) ->
      let (d,dom) = match d with
      | Some d -> (g cx d, Domain d)
      | None -> (base, No_domain)
      in
      d $$ g (add_bs_ctx [h, Unknown, dom] cx) ex
  | Arrow (e1,e2) -> g cx e1 $$ g cx e2
  | Expr.T.Fcn (bs, ex) ->
      map_bs g cx bs $$ g (add_bs_ctx bs cx) ex
  | Except (f, exs) ->
      let e_map_exc = function Except_apply ea -> g cx ea | Except_dot h -> base in
      g cx f $$ (flatten (List.map (fun (es,ex) -> flatten (List.map e_map_exc es) $$ g cx ex) exs))
  | Rect rs -> map_es (List.map (fun (_,e) -> e) rs)
  | Product es -> map_es es
  | If (c, t, f) -> map_es [c ; t ; f]
  | Case (es, o) ->
      (List.fold_left (fun r (p,e) -> g cx p $$ g cx e $$ r) base es)
      $$ (match o with Some o -> g cx o | None -> base)
  | Sequent seq -> g cx (unroll_seq seq)
  | Parens (ex,_) -> g cx ex
  | Lambda (xs,ex) ->
      let rec hs_to_ctx = function
      | ({core = h} as v,_) :: xs -> ((Flex (h @@ v)) @@ v) :: hs_to_ctx xs
      | [] -> []
      in
      g (List.rev (hs_to_ctx xs) @ cx) ex
  | _ -> base

let map_list = e_map List.append []
let map_exists = e_map (||) false
let map_forall = e_map (&&) true

(****************************************************************************)

let to_cx scx = Dq.to_list (Dq.rev scx)
let to_scx cx = fold_left (fun q h -> Dq.cons h q) Dq.empty cx

(****************************************************************************)

(** Do the [n] first variables appear in [e] ? *)
let rec free_n_vars n cx e : bool =
(* Util.eprintf "free_n_vars %d <= %a" n (Expr.Fmt.pp_print_expr (to_scx cx, Ctx.dot)) e ; *)
  match e.core with
  | Ix m -> m <= n
  | _ -> map_exists (free_n_vars n) cx e

let rec opaque ?strong:(stg=false) ?min:(k=0) cx e =
(* Util.eprintf "opaque: %a" (print_prop ()) e ; *)
  let mk x = { e with core = x } in
  match e.core with
  | Ix n when k < n ->
      if (not (n > 0 && n <= length cx))
      then  Opaque (Printf.sprintf "___%d___" n) |> mk
      else
      let id = lookup_id cx n in
      if (not stg) && (has_boundvar e) then e else
        Opaque id |> mk
  | Ix _ -> e
  | _ -> map_exp (opaque ~strong:stg) cx e

let fresh_bound_to_exp v dom =
  let id = smt_id v.core in
  let dom = app_expr (shift 1) dom in
  let exp = Apply (Internal B.Mem |> noprops, [Ix 1 @@ dom ; dom]) |> noprops in
  let fact = Flex (id @@ v) @@ v in
  exp, fact

let process_excep = function
  | Failure msg -> Util.eprintf "[TypeInfer] Failure: %s" msg
  (* | Untyped_symbol msg -> Util.eprintf "[TypeInfer Error] %s.\n" msg   *)
  (* | Unification_failed msg *)
  (* | Unsupported_type msg -> Util.eprintf "[TypeInfer Error] %s" msg   *)
  (* | Infer_other msg -> Util.eprintf "[TypeInfer] %s" msg *)
  (* | Unsupported_expression e -> Util.eprintf "[TypeInfer] Unsupported expression" *)
  | _ -> Util.eprintf "[TypeInfer] unknown exception.\n" ; assert false

(****************************************************************************)

(* let rec free_operators cx e : string list =
  match e.core with
  | Ix n ->
      begin match (List.nth cx (n - 1)).core with
      | Defn ({core = Operator (h,_)},_,_,_) -> [h.core]
      | _ -> []
      end
  | _ -> map_list free_operators cx e *)

let free_operators (sq:Expr.T.sequent) : string list =
  let ops = ref [] in
  let visitor = object (self : 'self)
    inherit [unit] Expr.Visit.iter as super
    method expr scx e =
      match e.core with
		  | Ix n ->
		      begin match (List.nth (to_cx (snd scx)) (n - 1)).core with
		      | Defn ({core = Operator (h,_)},_,_,_) -> ops := h.core :: !ops
		      | _ -> ()
		      end
      | _ -> super#expr scx e
    method hyp scx h = match h.core with
      | Defn (_, _, Hidden, _)                                                (** ignore these cases *)
      | Fact (_, Hidden, _) -> Expr.Visit.adj scx h
      | _ -> super#hyp scx h
  end in
  ignore (visitor#sequent ((),sq.context) sq) ;
(* Util.eprintf "free_ops = %s" (String.concat "," (Smt.remove_repeated !ops)) ; *)
  remove_repeated !ops

(****************************************************************************)
(* Global variables                                                         *)
(****************************************************************************)

let record_ids = ref SSMap.empty
let get_recid fs =
  try SSMap.find fs !record_ids
  with Not_found ->
    let id = unique_id () in
    (* record_ids := SSMap.add fs id !record_ids ; *)
    id

(** Two records have the same type iff they have the same fields
	(ignoring the fields position) *)
let add_record_id fs =
  let id = get_recid fs in
  record_ids := SSMap.add fs id !record_ids ;
  id

let tla_op_set = ref SSet.empty      																					(** Set of operators that appear in the obligation *)
let add_tla_op op = tla_op_set := SSet.add op !tla_op_set

let chooses = ref SMap.empty
let add_choose s cx e =
    match e.core with
    | Choose _ ->
        ignore begin
        try find (fun (_,(cx',e')) ->
            Expr.Eq.expr (opaque cx e) (opaque cx' e')) (SMap.bindings !chooses)
        with Not_found ->
            chooses := SMap.add s (cx,e) !chooses ;
            (s,(cx,e))
        end
    | _ -> ()

let skolem1_ids = ref SMap.empty																							(** Used for [Preprocess.abstract] *)
let skolem2_ids = ref SMap.empty																							(** Used for [Preprocess.abstract] *)
let record_signatures = ref []

(****************************************************************************)
(* Simple facts                                                             *)
(****************************************************************************)

let rec is_sf e =
  match e.core with
  | Apply ({core = Internal (B.Implies | B.Equiv | B.Disj)}, _)
  (* | Apply ({core = Internal B.Eq}, _) *)
  | Quant _
  | If _
  | Sequent _
      -> false
  | _ -> true

class simplefact = object (self)
  val mutable sf : (hyp Dq.dq * expr) list = []

  method reset = sf <- []

  method print =
    Util.eprintf "** SF:" ;
    iter (fun (scx,e) -> Util.eprintf "     @[<hov>%a@]"
      (Expr.Fmt.pp_print_expr (scx, Ctx.dot)) e) sf

  method private push_one (scx:hyp Dq.dq) e =
(* Util.eprintf "__SF#add1 [%d] %a" (Dq.size scx) (Expr.Fmt.pp_print_expr (scx, Ctx.dot)) e ; *)
    let es = deconj e
      |> List.filter is_sf
      |> List.map (fun e -> (scx,e))
    in
    sf <- es @ sf;
    List.length es

  (* method add scx es = ignore (List.map (self#push_one scx) es) *)

  method push scx es =
    List.fold_left (fun r e -> self#push_one scx e + r) 0 es

  method private mem scx e =
    (* let tx = Sys.time () in *)
    let r = List.fold_left
      begin fun r (scx',f) ->
      let d = Dq.size scx - Dq.size scx' in
      let f = if d > 0 then app_expr (shift d) f else f in
(* Util.eprintf "f: %a : %s" (print_prop ()) (opaque scx f) (typ_to_str e) ; *)
        (Expr.Eq.expr e f || r)
      end false sf
    in
    (* ifprint 1 "** SF#mem in %5.3fs.%!" (Sys.time() -. tx) ; *)
    r

  method simpl (scx:hyp Dq.dq) e =
(* Util.eprintf "___SF#simplify [%d] %a  using:" (Dq.size scx) (Expr.Fmt.pp_print_expr (scx, Ctx.dot)) e ; *)
(* Printf.eprintf "   ===================\n" ; (List.iter (fun (scx,e) -> Util.eprintf "   || [%d] %a" (Dq.size scx) (Expr.Fmt.pp_print_expr (scx, Ctx.dot)) e)) sf ; Printf.eprintf "   -------------------\n" ; *)
    (* let tx = Sys.time () in *)
    let e = e
      |> deconj
      |> List.filter (fun e -> not (List.exists (self#mem scx) (dedisj e)))
      (* |> fun es -> (List.iter (fun e -> Util.eprintf "  --- %a" (print_prop ()) (opaque cx e))) es ; es *)
      |> List.fold_left (fun r e ->
          let tla_false = Internal B.FALSE @@ e in
          let neg e = Apply (Internal B.Neg @@ e, [e]) @@ e in
          match e.core with
          | Apply ({core = Internal B.Neg}, [ex]) ->
              if self#mem scx ex then [tla_false] else r @ [e]
          | _ ->
              if self#mem scx (neg e) then [tla_false] else r @ [e]
          ) []
      (* |> fun es -> (List.iter (fun e -> Util.eprintf "  ''' %a" (print_prop ()) (opaque cx e))) es ; es *)
      |> fun es ->
          match es with
          | [] -> Internal B.TRUE @@ e
          | [ex] -> ex
          | _ -> List (And, es) @@ e
    in
    (* ifprint 1 "** SF#simpl in %5.3fs.%!" (Sys.time() -. tx) ; *)
    e

  method pop n =
(* Printf.eprintf "___SF#pop %d\n" n ; *)
    let rec remove_firsts n xs = match xs, n with
    | xs, 0 -> xs
    | x :: xs, n -> remove_firsts (n-1) xs
    | _ -> []
    in
    sf <- (remove_firsts n sf)

  (* method remove es =
    let rec faux xs n = match xs, n with
    | xs, 0 -> xs
    | x :: xs, n -> faux xs (n-1)
    | _ -> []
    in
    let es = es
      |> List.map deconj
      |> List.flatten
      |> List.filter is_sf
    in
    let n = List.length es in
    let sf' = faux sf n in
(* Printf.eprintf "====== after remove ======\n" ;
(List.iter (fun (scx,e) -> Util.eprintf "  --- [%d] %a" (Dq.size scx) (Expr.Fmt.pp_print_expr (scx, Ctx.dot)) e)) sf' ;
Printf.eprintf "----------------\n" ; *)
    sf <- sf' *)
end

let sf = new simplefact

let simplefacts = ref []

let rec is_simplefact e =
  (* true *)
    match e.core with
    (* | Quant _  *)
    | If _
    | Sequent _ -> false
    | _ -> true

(** [not anymore] FIX: toplevel facts "P <=> TRUE" should be added as the simplefact "P". *)
let add_simplefact cx e =
(* Util.eprintf "  add_simplefact: %a" (print_prop ()) (opaque cx e) ;     *)
    let es = deconj e
      |> List.filter is_simplefact
      |> List.map (fun e -> (cx,e))
    in
    simplefacts := es @ !simplefacts

let simp_simplefacts cx e =
  let mem_sf cx e = List.fold_left
    begin fun r (cxf,f) ->
      let d = List.length cx - List.length cxf in
      let f = if d > 0 then app_expr (shift d) f else f in
(* Util.eprintf "f: %a : %s" (print_prop ()) (opaque cx f) (typ_to_str e) ; *)
      (Expr.Eq.expr e f || r)
    end
    false !simplefacts
  in
(* Printf.eprintf "-------------------\n" ; (List.iter (fun (cx,e) -> Util.eprintf "  --- %a" (print_prop ()) (opaque cx e))) !simplefacts ; *)
  e
  |> deconj
  |> List.filter (fun e -> not (List.exists (mem_sf cx) (dedisj e)))
  (* |> fun es -> (List.iter (fun e -> Util.eprintf "  --- %a" (print_prop ()) (opaque cx e))) es ; es *)
  |> List.fold_left (fun r e ->
      let tla_false = Internal B.FALSE @@ e in
      let neg e = Apply (Internal B.Neg @@ e, [e]) @@ e in
      match e.core with
      | Apply ({core = Internal B.Neg},[ex]) ->
          if mem_sf cx ex then [tla_false] else r @ [e]
      | _ ->
          if mem_sf cx (neg e) then [tla_false] else r @ [e]
      ) []
  (* |> fun es -> (List.iter (fun e -> Util.eprintf "  ''' %a" (print_prop ()) (opaque cx e))) es ; es *)
  |> fun es ->
      match es with
      | [] -> Internal B.TRUE @@ e
      | [ex] -> ex
      | _ -> List (And, es) @@ e

let remove_simplefact es =
    let rec faux xs n = match xs, n with
    | xs, 0 -> xs
    | x :: xs, n -> faux xs (n-1)
    | _ -> []
    in
    (* Printf.eprintf "====== after remove ======\n" ;
    List.iter (fun (cx,e) -> Util.eprintf "fact: %a" (print_prop ()) (opaque cx e)) !simplefacts ;
    Printf.eprintf "----------------\n" ; *)
    let es = es
      |> List.map deconj
      |> List.flatten
      |> List.filter is_simplefact
    in
    let n = List.length es in
    simplefacts := faux !simplefacts n


(****************************************************************************)

(** List permutations *)
let rec perms xs =
  match xs with
  | [] -> []
  | x :: xs ->
    let perm2 x ys =
      match ys with
      | [] -> []
      | ys -> List.map (fun y -> x,y) ys
    in
    (perm2 x xs) @ (perms xs)

(** term ::= <Id/Opaque symbol> | String | Num | term(term,..,term) | Prime (term) | FcnApp (term, _) | Dot(term, _) *)
let rec is_term e =
    match e.core with
    | Ix _ | Opaque _ | String _ | Num _ -> true
    | Apply ({core = Internal B.Prime}, [ex]) -> is_term ex
    | Apply (ex, es) -> for_all is_term (ex :: es)
    | FcnApp (ex, _) -> is_term ex
    | Dot (ex, _) -> is_term ex
    | Internal B.Len
    | Internal B.Seq
    | Internal B.Append
    | Internal B.Tail
    | Internal B.Cat -> true
    | Tuple [] | SetEnum [] -> true
    | Internal B.Nat | Internal B.Int -> true
    | _ -> false

(** domain ::= DOMAIN (term) *)
let rec is_domain e =
    match e.core with
    | Apply ({core = Internal B.DOMAIN}, [ex]) -> is_term ex
    | _ -> false

(* let tuple_id ts = match ts with
  | [] -> "tuple0"
  (* | _ -> Printf.sprintf "tuple_%s" (String.concat "" (map (function Int -> "i" | _ -> "u") ts)) *)
  | _ -> Printf.sprintf "tuple_%s" (String.concat "" (map (function _ -> "u") ts))

let tuples = ref []
let add_tuple ts =
    add_tla_op (tuple_id ts) ;
    if not (mem ts !tuples) then tuples := ts :: !tuples *)

(****************************************************************************)

(* let rec unprime cx e =
  let opq id = function [] -> Opaque id |> noprops | es -> Apply (noprops (Opaque id), es) |> noprops in
  let us es = List.map (unprime cx) es in
  match e.core with
  | Apply ({core = Internal B.Prime}, [ex]) ->
      begin match ex.core with
      | Apply ({core = Ix n}, es)      -> opq (prime (lookup_id cx n)) (us es)
      | Apply ({core = Opaque id}, es) -> opq (prime id) (us es)
      | Ix n                           -> opq (prime (lookup_id cx n)) []
      | Opaque id                      -> opq (prime id) []
      | _                              -> Util.bug "src/smt/smtcommons.ml: unprime expression."
      end
  | _ -> map_exp unprime cx e *)

let newvars = ref SMap.empty
let mk_newvar_id cx e =
  try let id,_ = find (fun (_,(cx',e')) ->
        Expr.Eq.expr (opaque cx e) (opaque cx' e')) (SMap.bindings !newvars)
      in id
  with Not_found ->
    let id = fresh_id () in
    newvars := SMap.add id (cx,e) !newvars ;
    id

let unspec cx e = Opaque ("newvar__" ^ (mk_newvar_id cx e)) @@ e
(* let unspec cx e = Opaque ("newvar__" ^ (mk_newvar_id cx e)) |> noprops  *)

let rec insert_intdiv_cond cx e =
(* Util.eprintf "  insert_intdiv_cond: %a" (print_prop ()) (opaque cx e) ;     *)
  let app op x y = Apply (noprops (Internal op), [x ; y]) @@ e in
  match e.core with
  | Apply ({core = Internal (B.Quotient | B.Remainder)} as op, [x ; y]) ->
      let x = insert_intdiv_cond cx x in
      let y = insert_intdiv_cond cx y in
      let e = Apply (op, [x ; y]) @@ e in
      If (app B.Conj (app B.Mem y (noprops (Internal B.Int)))
                     (app B.Lt (noprops (Num ("0",""))) y), e, unspec cx e) @@ e
  | _ -> map_exp insert_intdiv_cond cx e

let allids cx =
    fold_left begin fun r h ->
      match h.core with
      | Fresh (nm, _, _, _)
      | Flex nm
      | Defn ({core = Operator (nm, _) | Instance (nm, _)
                      | Bpragma(nm,_,_) | Recursive (nm, _)},
              _, _, _)
        -> SSet.add nm.core r
      | Fact (_, _, _) -> r
    end SSet.empty cx

let subtract xs x = fold_left (fun r a -> if x = a then r else r @ [a]) [] xs
let list_minus xs ys = fold_left subtract xs ys

(* let rec free_vars cx e : string list =
(* Util.eprintf "free_vars %a" (print_prop ()) (opaque cx e) ; *)
  let free bs ex =
    let doms = fold_left (fun r (_,_,d) -> match d with Domain d -> d :: r | _ -> r) [] bs in
    let vs = map (fun (v,_,_) -> v.core) bs in
    flatten (map (free_vars cx) doms) @
    list_minus (free_vars (add_bs_ctx bs cx) ex) vs
  in
  match e.core with
  | Ix n -> [lookup_id cx n]
      (* if is_bvar cx n then [lookup_id cx n] else [] *)
  | Opaque s -> [s]
  | Quant (_,bs,ex)
  | Expr.T.Fcn (bs, ex)
  | SetOf (ex, bs) ->
      free bs ex
  | SetSt (h, dom, ex) ->
      free [h, Unknown, Domain dom] ex
  | Choose (h, d, ex) ->
      let dom = match d with
      | Some d -> Domain d
      | None -> No_domain
      in
      free [h, Unknown, dom] ex
  | _ -> map_list free_vars cx e
*)

(** from standard Option module *)
let map_default f v = function
	| None -> v
	| Some v2 -> f v2

let ph cx ff h = ignore (Expr.Fmt.pp_print_hyp cx ff h)

(** Free variables *)
let rec fv scx sq =
  let scx, fs1, bs = fv_hyps scx sq.context in
  let fs2 = fv_expr scx sq.active in
  fs1 @ (list_minus fs2 bs) |> remove_repeated
and fv_hyps scx hs =
  match Dq.front hs with
  | None -> scx, [], []
  | Some (h, hs) ->
      let scx, fs1, b = fv_hyp scx h in       (** [fs1]: list of free vars in [h], [b] : bounded var option *)
(* Util.eprintf "fv_hyp0 %a = %s \\ %s" (ph (snd scx, Ctx.dot)) h (String.concat "," fs1) (Option.default "none" b); *)
      let scx, fs2, bs = fv_hyps scx hs in    (** [fs2]: list of free vars in [hs], [bs] : bounded vars *)
      (* let fs = fs1 @ fs2 in
      let fs = map_default (subtract fs) fs b in
      (scx, fs, map_default (fun v -> v :: bs) bs b) *)
      let bs = match b with None -> bs | Some v -> v :: bs in
      let fs = list_minus (fs1 @ fs2) bs in
(* Util.eprintf "fv_hyp0 = %s \\ %s" (String.concat "," fs) (Option.default "none" b); *)
      (* let fs = match b with None -> fv | Some v -> subtract fs v in *)
      (* (scx, fs, match b with None -> b | Some v -> v :: bs) *)
      (scx, fs, bs)
and fv_hyp scx h =
  match h.core with
  | Fresh (nm, shp, lc, Bounded (r, Visible)) ->
      let fs = fv_expr scx r in
(* Util.eprintf "fv_hyp1 %a = %s \\ %s" (ph (snd scx, Ctx.dot)) h (String.concat "," fs) nm.core; *)
      (Expr.Visit.adj scx h, fs, Some nm.core)
  | Fresh (nm, shp, lc, Unbounded) ->
(* Util.eprintf "fv_hyp2 %a = [] \\ %s" (ph (snd scx, Ctx.dot)) h nm.core; *)
      (Expr.Visit.adj scx h, [], Some nm.core)
  | Flex s ->
(* Util.eprintf "fv_hyp3 %a = [] \\ %s" (ph (snd scx, Ctx.dot)) h s.core; *)
      (Expr.Visit.adj scx h, [], Some s.core)
  | Fact (e, Visible, tm) ->
      let fs = fv_expr scx e in
(* Util.eprintf "fv_hyp4 %a = %s" (ph (snd scx, Ctx.dot)) h (String.concat "," fs); *)
      (Expr.Visit.adj scx h, fs, None)
  (* | Defn ({core = Operator (nm, _)}, _, _, _) -> *)
  | _ ->
      (Expr.Visit.adj scx h, [], None)
and fv_expr scx e : string list =
  let fvs scx es = List.flatten (List.map (fv_expr scx) es) in
  match e.core with
  | Ix n ->
      [lookup_id (to_cx (snd scx)) n]
  | Opaque o ->
      [o]     (** [smt_id o] ?*)
  | Bang (e, sels) ->
      fv_expr scx e @ List.flatten (List.map (fv_sel scx) sels)
  | Lambda (vs, e) ->
      let scx = Expr.Visit.adjs scx (List.map (fun (v, shp) -> Fresh (v, shp, Unknown, Unbounded) @@ v) vs) in
      fv_expr scx e
  | Apply (op, es) ->
      fv_expr scx op @ fvs scx es
  | Sequent sq ->
      fv scx sq
  | With (e, _) ->
      fv_expr scx e
  | If (e, f, g) ->
      fv_expr scx e @ fv_expr scx f @ fv_expr scx g
  | List (_, es) | Tuple es | SetEnum es | Product es ->
      fvs scx es
  | Quant (q, bs, ex) ->
      let (scx, vs, fbs) = fv_bounds scx bs in
      fbs @ (list_minus (fv_expr scx ex) vs)
  | Choose (v, optdom, e) ->
      let fds = match optdom with Some e -> fv_expr scx e | None -> [] in
      let h = match optdom with
        | None -> Fresh (v, Shape_expr, Constant, Unbounded) @@ v
        | Some dom -> Fresh (v, Shape_expr, Constant, Bounded (dom, Visible)) @@ v
      in
      let scx = Expr.Visit.adj scx h in
      let fs = fv_expr scx e in
      fds @ (subtract fs v.core)
  | SetSt (v, dom, e) ->
      let fds = fv_expr scx dom in
      let scx = Expr.Visit.adj scx (Fresh (v, Shape_expr, Constant, Bounded (dom, Visible)) @@ v) in
      let fs = fv_expr scx e in
      fds @ (subtract fs v.core)
  | SetOf (ex, bs) ->
      let (scx, vs, fbs) = fv_bounds scx bs in
      fbs @ (list_minus (fv_expr scx ex) vs)
  | Fcn (bs, ex) ->
      let (scx, vs, fbs) = fv_bounds scx bs in
      fbs @ (list_minus (fv_expr scx ex) vs)
  | FcnApp (f, es) ->
      fv_expr scx f @ fvs scx es
  | Arrow (a, b) ->
      fv_expr scx a @ fv_expr scx b
  | Rect fs | Record fs ->
      List.flatten (List.map (fun (s, e) -> fv_expr scx e) fs)
  | Except (e, xs) ->
      fv_expr scx e @ List.flatten (List.map (fv_exspec scx) xs)
  | Dot (e, f) ->
      fv_expr scx e
  | Sub (s, e, f) ->
      fv_expr scx e @ fv_expr scx f
  | Case (arms, oth) ->
      List.flatten (List.map (fun (e, f) -> fv_expr scx e @ fv_expr scx f) arms)
        @ (match oth with Some e -> fv_expr scx e | None -> [])
  | Parens (e, pf) ->
      fv_expr scx e
  | _ -> []
and fv_sel scx = function
  | Sel_inst args ->
      List.flatten (List.map (fv_expr scx) args)
  | Sel_lab (l, args) ->
      List.flatten (List.map (fv_expr scx) args)
  | _ -> []
and fv_bounds scx bs =
  let fbs = List.map begin
    fun (_, _, dom) -> match dom with
      | Domain d -> fv_expr scx d
      | _ -> []
    end bs
    |> List.flatten
  in
  let hs = List.map begin
    fun (v, k, _) -> Fresh (v, Shape_expr, k, Unbounded) @@ v
  end bs in
  let vs = List.map (fun (v, _, _) -> v.core) bs in
  let scx = adjs scx hs in
  (scx, vs, fbs)
and fv_exspec scx (trail, res) =
  let do_trail = function
    | Except_dot s -> []
    | Except_apply e -> fv_expr scx e
  in
  List.flatten (List.map do_trail trail) @ fv_expr scx res

(** Free variable indices, context independent *)
(* let rec fv_i i sq =
  let fs1, bs = fv_hyps_i i sq.context in
  let fs2 = fv_expr_i i sq.active in
  fs1 @ (list_minus fs2 bs) |> remove_repeated
and fv_hyps_i i hs =
  match Dq.front hs with
  | None -> [], []
  | Some (h, hs) ->
      let fs1, b = fv_hyp_i i h in
      let fs2, bs = fv_hyps_i i hs in
      let bs = match b with None -> bs | Some v -> v :: bs in
      let fs = list_minus (fs1 @ fs2) bs in
      (fs, bs)
and fv_hyp_i i h =
  match h.core with
  | Fresh (nm, shp, lc, Bounded (r, Visible)) ->
      let fs = fv_expr_i i r in
      (fs, Some nm.core)
  | Fresh (nm, shp, lc, Unbounded) ->
      ([], Some nm.core)
  | Flex s ->
      ([], Some s.core)
  | Fact (e, Visible, tm) ->
      let fs = fv_expr_i i e in
      (fs, None)
  | _ ->
      ([], None) *)
let rec fv_expr_i i e : int list =
  let fvs i es = List.flatten (List.map (fv_expr_i i) es) in
(* Util.eprintf "               %d -- %a" i (Expr.Fmt.pp_print_expr (Dq.empty, Ctx.dot)) e ; *)
  match e.core with
  | Ix n ->
(* Util.eprintf "                  %d > %d ?" n i ; *)
      if n > i then [n-i] else []
  | Opaque o ->
      []
  | Bang (e, sels) ->
      fv_expr_i i e @ List.flatten (List.map (fv_sel_i i) sels)
  | Lambda (vs, e) ->
      fv_expr_i (i+1) e
  | Apply (op, es) ->
      fv_expr_i i op @ fvs i es
  (* | Sequent sq ->
      fv_i i sq *)
  | With (e, _) ->
      fv_expr_i i e
  | If (e, f, g) ->
      fv_expr_i i e @ fv_expr_i i f @ fv_expr_i i g
  | List (_, es) | Tuple es | SetEnum es | Product es ->
      fvs i es
  | Quant (q, bs, ex) ->
      (fv_bounds_i i bs) @ (fv_expr_i (i + List.length bs) ex)
  | Choose (v, optdom, e) ->
      let fds = match optdom with Some e -> fv_expr_i i e | None -> [] in
      fds @ (fv_expr_i (i + 1) e)
  | SetSt (v, dom, e) ->
      let fds = fv_expr_i i dom in
      fds @ (fv_expr_i (i + 1) e)
  | SetOf (ex, bs) ->
      (fv_bounds_i i bs) @ (fv_expr_i (i + List.length bs) ex)
  | Fcn (bs, ex) ->
      (fv_bounds_i i bs) @ (fv_expr_i (i + List.length bs) ex)
  | FcnApp (f, es) ->
      fv_expr_i i f @ fvs i es
  | Arrow (a, b) ->
      fv_expr_i i a @ fv_expr_i i b
  | Rect fs | Record fs ->
      List.flatten (List.map (fun (s, e) -> fv_expr_i i e) fs)
  | Except (e, xs) ->
      fv_expr_i i e @ List.flatten (List.map (fv_exspec_i i) xs)
  | Dot (e, f) ->
      fv_expr_i i e
  | Sub (s, e, f) ->
      fv_expr_i i e @ fv_expr_i i f
  | Case (arms, oth) ->
      List.flatten (List.map (fun (e, f) -> fv_expr_i i e @ fv_expr_i i f) arms)
        @ (match oth with Some e -> fv_expr_i i e | None -> [])
  | Parens (e, pf) ->
      fv_expr_i i e
  | _ -> []
and fv_sel_i i = function
  | Sel_inst args ->
      List.flatten (List.map (fv_expr_i i) args)
  | Sel_lab (l, args) ->
      List.flatten (List.map (fv_expr_i i) args)
  | _ -> []
and fv_bounds_i i bs =
  List.map begin
    fun (_, _, dom) -> match dom with
      | Domain d -> fv_expr_i i d
      | _ -> []
    end bs
  |> List.flatten
and fv_exspec_i i (trail, res) =
  let do_trail = function
    | Except_dot s -> []
    | Except_apply e -> fv_expr_i i e
  in
  List.flatten (List.map do_trail trail) @ fv_expr_i i res



(** rename repeated ids for bounded variables. *)
let rec renameb cx e =
(* Util.eprintf "renameb %a" (print_prop ()) e ; *)
    (* let mk x = { e with core = x } in *)
    let ren v = if SSet.mem v.core (allids cx) then (v.core^"_1") @@ v else v in
    match e.core with
    | Quant (q, bs, ex) ->
        let bs = List.map (fun (v,k,d) -> ren v,k,d) bs in
        (* Quant (q, (* map_exp_bs renameb cx *) bs, renameb (add_bs_ctx bs cx) ex) @@ e *)
        map_exp renameb cx (Quant (q, bs, ex) @@ e)
    | _ -> map_exp renameb cx e

let flatten_conj e =
    let rec collect e = match e.core with
    | Apply ({core = Internal B.Conj}, [e1 ; e2]) ->
        collect e1 @ collect e2
    | List (And, es) ->
        flatten (map collect es)
    | _ -> [e]
    in
    begin match filter_true (collect e) with
    | [] -> Internal B.TRUE @@ e
    | ex :: [] -> ex
    | es -> if exists (fun e ->
                match e.core with Internal B.FALSE -> true | _ -> false) es
                then Internal B.FALSE @@ e else (List (And, es) @@ e)
    end

let flatten_disj e =
    let rec collect e = match e.core with
    | Apply ({core = Internal B.Disj}, [e1 ; e2]) ->
        collect e1 @ collect e2
    | List (Or, es) ->
        flatten (map collect es)
    | _ -> [e]
    in
    begin match filter_false (collect e) with
    | [] -> Internal B.FALSE @@ e
    | [ex] -> ex
    | es -> if exists (fun e ->
                match e.core with Internal B.TRUE -> true | _ -> false) es
                then Internal B.TRUE @@ e else (List (Or, es) @@ e)
    end

(****************************************************************************)

let rec fix ?feq:(xeq=Expr.Eq.expr) c f xs =
  let rec eqq xs ys = match xs, ys with
  | x :: xs, y :: ys -> if xeq x y then eqq xs ys else false
  | [], [] -> true
  | _ -> false
  in
  if c = 0 then (failwith "smt/smtcommons.ml: Cannot reach fixed point [fix].\n") else
  (let ys = f xs in if eqq xs ys then xs else fix (c-1) f ys)

module Fu = Fmtutil.Minimal (Tla_parser.Prec)

let rec fix3 d f (scx,hs,c) =
  let eq (scx,hs,c) (scx',hs',c') =
    (** CHECK: compare [scx] and [scx'] ? *)
    Expr.Eq.sequent {context = hs ; active = c} {context = hs' ; active = c'}
  in
(* Util.eprintf "[-]%d: %a" (Dq.size hs) Fu.pp_print_minimal (Fu.Big (fun ff -> ignore (Expr.Fmt.pp_print_sequent (hs, Ctx.dot) ff {context=hs;active=c}))); *)
  if d = 0 then (failwith "smt/smtcommons.ml: Cannot reach fixed point [fix3].\n") else
  begin
    let scx',hs',c' = f (scx,hs,c) in
    if eq (scx,hs,c) (scx',hs',c')
     then (scx,hs,c)
     else
(* (Util.eprintf "[*1]%d: %a" (Dq.size hs) Fu.pp_print_minimal (Fu.Big (fun ff -> ignore (Expr.Fmt.pp_print_sequent (hs, Ctx.dot) ff {context=hs;active=c})));
 Util.eprintf "[*2]%d: %a" (Dq.size hs) Fu.pp_print_minimal (Fu.Big (fun ff -> ignore (Expr.Fmt.pp_print_sequent (hs', Ctx.dot) ff {context=hs';active=c'})));
 assert false) *)
			 fix3 (d-1) f (scx',hs',c')
  end

let rec fix_sq d f sq =
(* Util.eprintf "[-]%d: %a" (Dq.size hs) Fu.pp_print_minimal (Fu.Big (fun ff -> ignore (Expr.Fmt.pp_print_sequent (hs, Ctx.dot) ff {context=hs;active=c}))); *)
  if d = 0 then (failwith "smt/smtcommons.ml: Cannot reach fixed point [fix_sq].\n") else
  begin
    let sq' = f sq in
    if Expr.Eq.sequent sq sq'
     then sq
     else fix_sq (d-1) f sq'
  end

let rec fix_sqs d f sqs =
  if d = 0 then (failwith "smt/smtcommons.ml: Cannot reach fixed point [fix_sqs].\n") else
  begin
    let sqs' = f sqs in
    if List.for_all2 Expr.Eq.sequent sqs sqs'
     then sqs
     else fix_sqs (d-1) f sqs'
  end

(****************************************************************************)


(** Is expression [e] a typing hypothesis? *)
let rec is_typhyp ?var (scx:hyp Dq.dq) e =
  match e.core with
  | Apply ({core =   Internal B.Mem
                   | Internal B.Eq
                   | Internal B.Subseteq
                   }, [x ; y]) ->
      let idx =
        match x.core with
        | Ix n -> Some (lookup_id (to_cx scx) n)
        | Opaque id -> Some id
        | _ -> None
      in
      begin match idx with
      | None -> false
      | Some idx ->
          (match var with None -> true | Some v -> idx = v) &&
          not (List.mem idx (fv_expr ((),scx) y))
      end
  (** \A x \in S : op(x) \in T *)
  | Quant (Forall, [h,_,Domain s], {core = Apply ({core = Internal B.Mem},
      [{core = Apply ({core = Ix _}, [{core = Ix 1}])} ; t])}) ->
      true
  (** \A x : p(x) => op(x) \in S *)
  | Quant (Forall, [_,_,No_domain], {core = Apply ({core = Internal B.Implies}, [
  		{core = Apply ({core = Opaque "boolify"}, [
	  		{core = Apply ({core = Ix n}, [{core = Ix 1}])}
		  	])};
			{core = Apply ({core = Internal B.Mem},
    		[{core = Apply ({core = Ix m}, [{core = Ix 1}])}; s])}
			])}) ->
      true
  | _ -> false

(** unbound [bs] *)
let rec unb bs =
    let mk x = noprops x in
    (* let lAnd = function [e] -> e | es -> List (And, es) |> mk in *)
    let mem x y = Apply (Internal B.Mem |> mk, [x ; y]) |> mk in
    match bs with
    | (_, _, Domain d) as b1 :: (h,k,Ditto) :: bs ->
        unb (b1 :: (h,k,Domain d) :: bs)
    | (v, k, Domain dom) :: bs ->
        let n = (length bs) + 1 in
        let _, bs = app_bounds (shift 1) bs in
        let bs,ds = unb bs in
        let ex = mem (Ix n |> mk) (app_expr (shift n) dom) in
        (v, k, No_domain) :: bs, (ex :: ds)
    | (v, k, No_domain) :: bs ->
        let bs,ds = unb bs in
        (v, k, No_domain) :: bs, ds
    | [] -> [],[]
    | _ -> assert false

let rec_sort rs =
  let compare (h,t) (i,u) = String.compare h i in
  List.sort ~cmp:compare rs

(** Keywords *)
let smt_backend_keys = [
  "u";"bool";"int";"str";"Int";"boolify";"bool2u";"int2u";"str2u";"u2int";"u2str";
  "tla__isAFcn";"tla__fcnapp";"tla__unspec";
	"tla__STRING";"tla__BOOLEAN";"tla__SUBSET";"tla__UNION";"tla__DOMAIN";
	"tla__subseteq";"tla__in";"tla__notin";"tla__setminus";"tla__cap";"tla__cup";
	"tla__Int";"tla__Nat";"tla__Real";"tla__plus";"tla__minus";"tla__times";
	"tla__exp";"tla__ratio";"tla__div";"tla__mod";"tla__lt";"tla__le";"tla__lt";
	"tla__le";"tla__uminus";"tla__Range";"tla__Infinity";
	"exp";"mod";
	"tla__Seq";"tla__Len";"tla__BSeq";"tla__concat";"tla__Append";"tla__Head";
	"tla__Tail";"tla__SubSeq";"tla__SelectSeq";
	"tla__Cardinality";
  "tptp_plus";"tptp_minus";"tptp_times";"tptp_ratio";"tptp_div";"tptp_mod";
	"tptp_exp";"tptp_ls";"tptp_le";"tptp_uminus";
  ]
;;

let is_smt_kwd x = List.mem x smt_backend_keys

let smt_pickle isbounded id =
  if id = "_" then (failwith "SMT bug: identifier \"_\"") else
  if is_smt_kwd id then id else
  begin match id with
  | "<=" | "<" -> id
  | _ ->
    let id = if Str.string_match (Str.regexp "^[0-9].*") id 0 then "x"^id else id in 		(** identifiers cannot start with [0-9] *)
    let rep s r id = Str.global_replace (Str.regexp s) r id in
    id
    |> Tla_parser.pickle
    |> rep "'" "_" 																														(** Identifiers cannot contain "'" *)
    (* |> rep "^max$" "max__"        (** max is a reserved word in Z3 v4.0 *) *)
    (* |> rep "^u$" "u__"            (** u is also a sort: not allowed in CVC3 *) *)
    (* |> rep "^status$" "X__status" (** keyword in Spass *) *)
    (* |> rep "^repeat$" "tla_repeat" (** keyword in Spass *) *)
    |> turn_first_char isbounded
  end
