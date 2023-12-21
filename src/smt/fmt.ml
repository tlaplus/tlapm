(* Apply lifting functions (`int2u` and `str2u`).

Authors: Hernán Vanzetto <hernan.vanzetto@inria.fr>

Copyright (C) 2011-2012  INRIA and Microsoft Corporation
*)
open Ext
open Property

open Expr.T
open Expr.Subst
open Expr.Visit

open Printf

(* open Tsystem *)
open Smtcommons
(* open Typeinfer *)

module B = Builtin

open Typ_t

(** [boolify] already applied by [Boolify.mk_bool] *)
let ( <<< ) e prop : expr =
(* Util.eprintf "%a <<< %s" (print_prop ()) e prop.rep ; *)
  match prop with
  | "int2u"   -> Apply (Opaque "int2u" |> noprops, [e]) |> noprops
  | "str2u"   -> Apply (Opaque "str2u" |> noprops, [e]) |> noprops
  | "fmtasint" -> assign e fmtasint ()
  | _ -> e

(** Assigns properties [fmtasint], [fmtasint] and ["int2u"] to sub-expressions in [scx,e]
    [req] = required type for expression [scx,e]
    - Require a [Bool] only when the argument of the expression allows it. For
      example, not for the If condition. This will apply [u2bool] only to the
      correct cases. No SMT term will be declared as [Bool].
    - Require [Int] only when the expression is known to be integer.
    - If the expression is known to be integer, then format it as integer.
      get_type cx e = Int ---> e <<< fmtasint
    - No SMT term will be declared as [Bool]: always lift with [u2bool] when [Bool] is required.
    - [int2u] should be applied only to [Int]egers or formatted-as-int [fmtasint]
*)
let rec lift req scx e : Expr.T.expr =
(* Util.eprintf "lift %a\t%a" Typ_e.ppt (Typ_e.empty,req) (Typ_e.pp_print_expr (scx, Ctx.dot)) e ; *)
  let mk x = { e with core = x } in
  let apply op e1 e2 = Apply (Internal op |> mk, [e1 ; e2]) |> mk in
  let app1 op ex = Apply (Internal op |> mk, [ex]) |> mk in
  let apps op es = Apply (op, es) |> mk in
  let fcnapp f es = FcnApp (f, es) |> mk in

  let typ scx e = Option.default Top (Typ_t.get_type scx e) in
  let t = match typ scx e with
    | Int -> Int
    | Ref (_,Int,_) -> Int
    | Str -> Str
    | Ref (_,Str,_) -> Str
    | Bool -> Bool
    | _ -> Top
  in

  match e.core with
  | Ix _ ->
      lift_term t req e
  | Opaque _ ->
      lift_term t req e
  | Apply ({core = Opaque "tla__fcnapp_i"} as p, es) ->
      let e = apps p (List.map (lift Top scx) es) in
      if req = Int then e else e <<< "int2u"
  | Apply ({core = Opaque id}, es) when Smtcommons.is_smt_kwd id ->
      apps (Opaque id %% []) (List.map (lift Top scx) es)
  (* | Apply ({core = Opaque ("<="|"<")} as p, es) ->
      apps (p <<< "fmtasint") (List.map (lift Int scx) es) *)
  | Apply (({core = Ix _ | Opaque _} as f), es) ->
      let e = apps f (List.map (lift Top scx) es) in
      lift_term t req e
  | FcnApp (f, es) ->
      let e = fcnapp (lift Top scx f) (List.map (lift Top scx) es) in
      lift_term t req e
  | Dot (ex, h) ->
      let e = Dot (lift Top scx ex, h) |> mk in
      lift_term t req e
  | Apply ({core = Internal op} as o, es) ->
      begin match op, es with
      | B.Mem, [x ; {core = Internal B.Int}] when Typ_t.is_int scx x ->
          Internal B.TRUE %% []
      (* | B.Mem, [x ; ({core = Internal B.Int} as y)] when Typ_t.is_int scx x -> *)
          (* let x = if Typ_t.is_int scx x then x <<< "fmtasint" else x in *)
          (* apps (o <<< "fmtasint") [lift Int scx x ; y] *)
      (* | B.Eq, [{core = Internal B.TRUE | Internal B.FALSE} as e1 ; e2]
      | B.Eq, [e1 ; {core = Internal B.TRUE | Internal B.FALSE} as e2] ->
          apply B.Equiv (lift Bool scx e1) (lift Bool scx e2) *)
      | B.Eq, [e1 ; e2] ->
          let t1 = typ scx e1 in
          let t2 = typ scx e2 in
(* Util.eprintf "lift %a\t%a" Typ_e.ppt (Typ_e.empty,req) (Typ_e.pp_print_expr (scx, Ctx.dot)) e ; *)
(* Util.eprintf "     %a = %a" Typ_e.ppt (Typ_e.empty,t1) Typ_e.ppt (Typ_e.empty,t2); *)
          begin match t1, t2 with
          | Int,  Int  -> apply op (lift Int scx e1) (lift Int scx e2)
          | Str,  Str  -> apply op (lift Str scx e1) (lift Str scx e2)
          | Bool, Bool -> apply B.Equiv (lift Bool scx e1) (lift Bool scx e2)     (** It changes = to <=> *)
          | _ ->            apply op (lift Top scx e1) (lift Top scx e2)
          end
      | B.Conj,    [e1 ; e2]
      | B.Disj,    [e1 ; e2]
      | B.Implies, [e1 ; e2]
      | B.Equiv,   [e1 ; e2] ->
          let e1 = lift Bool scx e1 in
          let e2 = lift Bool scx e2 in
          apply op e1 e2
      | B.Neg,    [ex]      -> app1 op (lift Bool scx ex)
      | B.DOMAIN, [ex]      -> app1 op (lift Top scx ex)
      | B.Mem,    [e1 ; e2]
      | B.Range,  [e1 ; e2] -> apply op (lift Top scx e1) (lift Top scx e2)
      | B.Lteq,   [e1 ; e2]
      | B.Lt,     [e1 ; e2]
      | B.Gteq,   [e1 ; e2]
      | B.Gt,     [e1 ; e2] ->
          (* apps (o <<< "fmtasint") [lift Int scx e1 ; lift Int scx e2] *)
          begin match typ scx e1, typ scx e2 with
          | Int, Int -> apps (o <<< "fmtasint") [lift Int scx e1 ; lift Int scx e2]
          (* | Int, Top -> apps o [lift Top scx e1 ; lift Top scx e2] *)
          (* | Top, Int -> apps o [lift Top scx e1 ; lift Top scx e2] *)
          | _ ->          apps o [lift Top scx e1 ; lift Top scx e2]
          end
      | B.Plus,      [e1 ; e2]
      | B.Minus,     [e1 ; e2]
      | B.Times,     [e1 ; e2]
      | B.Ratio,     [e1 ; e2]
      | B.Quotient,  [e1 ; e2]
      | B.Remainder, [e1 ; e2]
      | B.Exp,       [e1 ; e2]
          ->
          begin match req, Typ_t.is_int scx e1 && Typ_t.is_int scx e2 with
          | Top, true -> apps (o <<< "fmtasint") [lift Int scx e1 ; lift Int scx e2] <<< "int2u"
          | _,   true -> apps (o <<< "fmtasint") [lift Int scx e1 ; lift Int scx e2]
          | _         -> apps o [lift Top scx e1 ; lift Top scx e2]
          end
      (* | B.Exp, [e1 ; e2] ->
          apps o [lift Top scx e1 ; lift Top scx e2]         *)
      | B.Uminus, [ex] ->
          begin match req, Typ_t.is_int scx ex with
          | Top, true -> apps (o <<< "fmtasint") [lift Int scx ex] <<< "int2u"
          | _, true   -> apps (o <<< "fmtasint") [lift Int scx ex]
          | _         -> apps o [lift Top scx ex]
          end
      | B.Prime, [ex] ->
          app1 op (lift req scx ex)
      (* | B.Prime, [{core = Ix _ | Opaque _} as ex] ->
          app1 op (lift req scx ex) *)

      | B.Seq,       [ex]      -> app1 op (lift Top scx ex)
      | B.Head,      [ex]      -> app1 op (lift Top scx ex)
      | B.Tail,      [ex]      -> app1 op (lift Top scx ex)
      | B.Len,       [ex]      -> let e = app1 op (lift Top scx ex) in if req = Int then e else e <<< "int2u"
      | B.BSeq,      [e1 ; e2] -> apply op (lift Top scx e1) (lift Top scx e2)
      | B.Cat,       [e1 ; e2] -> apply op (lift Top scx e1) (lift Top scx e2)
      | B.Append,    [e1 ; e2] -> apply op (lift Top scx e1) (lift Top scx e2)
      | B.SelectSeq, [e1 ; e2] -> apply op (lift Top scx e1) (lift Top scx e2)
      | B.SubSeq,    [e1;e2;e3]-> apps (Internal op |> mk) (List.map (lift Top scx) es)

      (*
      | B.OneArg,    [e ; f] -> proc_out "oneArg" es
      | B.Extend,    [e ; f] -> proc_out "extend" es
      | B.Print,     [e ; v] -> proc_out "Print" es
      | B.PrintT,    [e]     -> proc_out "PrintT" es
      | B.Assert,    [e ; o] -> proc_out "Assert" es
      | B.JavaTime,  []      -> proc_out "JavaTime" es
      | B.TLCGet,    [i]     -> proc_out "TLCGet" es
      | B.TLCSet,    [i ; v] -> proc_out "TLCSet" es
      | B.Permutations, [s]  -> proc_out "Permutations" es
      | B.SortSeq,   [s ; o] -> proc_out "SortSeq" es
      | B.RandomElement, [s] -> proc_out "RandomElement" es
      | B.Any,       []      -> prefix "Any"
      | B.ToString,  [v]     -> proc_out "ToString" es *)

      | _ ->
          Errors.set (Internal op |> mk) "lift.ml: Arity mismatch";
          Util.eprintf ~at:(Internal op |> mk) "Arity mismatch or expression not normalized" ;
          failwith "Backend.Smt.Fmt.lift"
      end
  | Internal B.TRUE | Internal B.FALSE ->
      e
  | Num (m, "") ->
      if req = Int then e else e <<< "int2u"
  (* | Internal B.Infinity ->
      if req = Top then e <<< "int2u" else e *)
  | String _ ->
      if req = Str then e else e <<< "str2u"
  | If (c, t, f) ->
      let t1 = typ scx t in
      let t2 = typ scx f in
(* Util.eprintf "lift %s %a" (TLAtype.to_string req) (print_prop ()) (opaque scx e) ; *)
(* Printf.eprintf "\te1 :: %s\n" (TLAtype.to_string t1) ; *)
(* Printf.eprintf "\te2 :: %s\n" (TLAtype.to_string t2) ; *)
      let c = lift Bool scx c in
      let t1, t2, prop = match req, t1, t2 with
      | Int, Int, Int   -> Int, Int, None
      | Top, Int, Int   -> Top, Top, None
      | Int, Int, Top   -> Top, Top, None
      | Top, Int, Top   -> Top, Top, None
      | Int, Top, Int   -> Top, Top, None
      | Top, Top, Int   -> Top, Top, None
      | Bool, Bool, Bool -> Bool, Bool, None
      | _,   Bool, Bool -> Bool, Bool, None
      | Top, Top,  Bool -> Top, Top, None
      | Top, Bool, Top  -> Top, Top, None
      | Bool, Bool, Top -> Top, Top, None
      | Bool, Top,  Bool -> Top, Top, None
      | Bool, _,    _   -> Bool, Bool, None
      | _               -> Top, Top, None
      in
      let e = If (c, lift t1 scx t, lift t2 scx f) |> mk in
      begin match prop with Some p -> e <<< p | None -> e end
  | List (b, es) ->
      List (b, List.map (lift Bool scx) es) |> mk
  | Quant (q, bs, ex) ->
      (* let bs,ds = Smtcommons.unb bs in
      let ex = match q, ds with
        | _, [] -> ex
        | Forall, _ ->
            let ds = flatten_conj (List (And, ds) %% []) in
            apply B.Implies ds ex
        | Exists, _ ->
            let ds = flatten_conj (List (And, ds) %% []) in
            apply B.Conj ds ex
      in       *)
      (** Assumption: all [Quant]'s have [No_domain] after normalization. *)
      let scx, bs = lift_bs scx bs in
      Quant (q, bs, lift Bool scx ex) |> mk
  | Record es ->
      Record (List.map (fun (f,e) -> f, lift Top scx e) es) |> mk
  | Tuple es ->
      (* add_tuple (List.map (fun e -> if typ scx e = Int then Int else Top) es) ; *)
      Tuple (List.map (fun e -> lift (* (if typ scx e = Int then Int else Top) *)Top scx e) es) |> mk
  | _ ->
      e
and lift_term t req e =
(* Util.eprintf "lift %a-%a\t%a" Typ_e.ppt (Typ_e.empty,t) Typ_e.ppt (Typ_e.empty,req) (Typ_e.pp_print_expr (Deque.empty, Ctx.dot)) e ; *)
  begin match t, req with
  | Int, Top  -> e <<< "fmtasint" <<< "int2u"
  | Str, Top  -> e <<< "str2u"
  | Int, Int -> e <<< "fmtasint"
  (* | Str, Str -> e <<< "fmtasstr" *)
  | _          -> e
  end
and lift_bs scx bs =
  let bs = Expr.Visit.map_bound_domains
    (fun d -> lift Top scx d) bs in
  let hs = Expr.Visit.hyps_of_bounds bs in
  let scx = Expr.Visit.adjs ((),scx) hs in
  (snd scx, bs)
and lift_sq scx (hs,c) =
  List.map (lift Bool scx) hs, lift Bool scx c
