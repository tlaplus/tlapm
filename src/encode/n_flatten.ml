(*
 * encode/flatten.ml --- eliminate second-order features
 *
 *
 * Copyright (C) 2022  INRIA and Microsoft Corporation
 *)

open Expr.T
open Type.T
open Property
open Ext

module Subst = Expr.Subst
module Is = Util.Coll.Is

let subst = N_subst.subst

(** Outline of the algorithm:

    Facts in a sequent are treated one by one, starting from the end.  For each
    fact, the expression is parsed until a HO application is found.  If one is
    found, it is treated immediately (the current fact is updated, and new
    hypotheses are inserted above it), then the fact is parsed again.  If no
    HO application is found, then the algorithm continues with the next fact.
    
    For this module, it is relevant to know which part of a context is global
    (hypotheses of the sequent), and which part is local (quantified variables,
    let definitions, etc.)

    Let [gtx] and [ltx] denote the global and local parts of some context, and
    assume the following HO application occurs in that context:

        F(e1, G, e2, LAMBDA x : x \in Int /\ x # y, e3)

    Where [e1], [e2] and [e3] are expressions, [G] is an operator identifier,
    and [y] is a variable that is bound locally (in [ltx]).  The blueprint
    for that application would contain:
      - The index of [F], that must be bound in [gtx];
      - The HO arguments, here [G] and [LAMBDA x : x \in Int /\ x # y];
      - The local free variables in those arguments, here just [y];
      - The context itself (otherwise the expressions cannot be made sense of).
    The blueprint is put on [F] as an annotation for later.

    (Note that [Int] and [y] are both internally represented by indexes, but
    only [y] is bound locally.  Note also that locally bound variables cannot
    refer to operators, which are only declared globally.)

    In the next step, a declaration for the replacement operator is prepared.
    This can be done systematically from the type of [F]: every first-order
    argument is kept, all HO arguments are discarded, and every local variable
    of the HO arguments leads to a new argument.  In that case, the generated
    declaration is:

        NEW F_flat(_, _, _, _)                                      (H)

    The first three arguments correspond to [e1], [e2] and [e3], the fourth is
    for the variable [y].

    There may be axioms attached to [F].  Suppose the only one is:

        ASSUME NEW H(_),
               NEW P(_),
               NEW a,
               NEW b,
               NEW c
        PROVE F(a, H, b, P, c) = { x \in H(a) : P(b) /\ c }         (A)

    It is assumed all axioms are sequents, of which the first parameters are
    operator parameters that correspond to the HO arguments of the HO operator,
    in the same order (first the leftmost argument, etc.)

    (A) must be instantiated with the relevant HO arguments.  Since these
    arguments contain variables bound locally in the original expressions,
    quantifiers must also be appended on top of (A) to recover the relevant
    variables of [ltx].  The result is:

        ASSUME NEW y,
               NEW a,
               NEW b,
               NEW c
        PROVE F(a, G, b, LAMBDA x : x \in Int /\ x # y, c)
                  = { x \in G(a) : b \in Int /\ b # y /\ c }        (A')

    Now, (A') still contains an occurrence of [F], which is similar to the one
    that was encountered in the original expression.  That [F] is annotated
    with the same blueprint.

    What remains to be done is insert (H) and (A') below [gtx], and rewrite the
    applications of [F] inside (A') and the original expression.  Since
    inserting hypotheses in [gtx] modifies the context, the blueprints
    annotations contain deprecated information.  This is not a problem, because
    the only relevant information to perform rewritings is a reference to
    [F_flat]; which arguments are first-order (easy to determine from the type
    of [F]); and the local variables of HO arguments, which are bound locally,
    so modifying [gtx] does not affect them.

    Now every occurrence of [F] applied is of the form:

        F(E1, G, E2, LAMBDA x : x \in Int /\ x # y, E3)

    With [F] annotated with a blueprint.  They are all rewritten:

        F_flat(E1, E2, E3, y)

*)


(* {3 Helpers} *)

let error ?at mssg =
  let mssg = "Encode.Flatten: " ^ mssg in
  (*Errors.bug ?at mssg*)
  failwith mssg

let is_sndord = function
  | Ty2 (ty1s, _) ->
      List.exists (function Ty1 ([], _) -> false | _ -> true) ty1s

let get_hyp ctx ix =
  Option.get (Deque.nth ~backwards:true (snd ctx) (ix - 1))

let get_ty2 h =
  let v = hyp_hint h in
  if has v Props.ty2_prop then
    get v Props.ty2_prop
  else if has v Props.ty1_prop then
    upcast_ty2 (get v Props.ty1_prop)
  else if has v Props.ty0_prop then
    upcast_ty2 (upcast_ty1 (get v Props.ty0_prop))
  else
    let mssg = "Missing type annotation on '" ^ hyp_name h ^ "'" in
    error ~at:h mssg


(* {3 Context} *)

(* NOTE Contexts are implemented in such a way that {!Expr.Visit.adj} appends
 * hypotheses in the local part of the context.  Therefore, the methods of
 * {!Expr.Visit} need not be reimplemented if visitors are only used on
 * individual facts (not used to parse a top context). *)

type ctx = int Expr.Visit.scx

let init_ctx = (0, Deque.empty)

let sz (_, cx) = Deque.size cx
let global_sz (k, _) = k
let local_sz ctx = sz(ctx) - global_sz(ctx)

let global_adj (k, cx as ctx) (h : hyp) =
  if local_sz ctx = 0 then
    (k + 1, Deque.snoc cx h)
  else
    let mssg = "Cannot append in global context from a local context" in
    error ~at:h mssg

(* For debugging *)
let pp_print_ctx ff (k, cx) =
  Format.fprintf ff "(%d, %a)"
  k
  (fun ff a -> Fmtutil.pp_print_delimited_fold Expr.Fmt.pp_print_hyp (cx, Ctx.dot) ff a |> ignore) (Deque.to_list cx)


(* {3 Blueprints} *)

(** A blueprint is a record of all information relevant
    to an application that is to be flattened.
*)
type bp =
  { bp_id : int             (** Identifier for the blueprint *)
  ; bp_ctx : ctx            (** Context of the rewritten application *)
  ; bp_orig_ix : int        (** Index of the original operator (must be declared) *)
  ; bp_ho_args : expr list  (** The original HO arguments in the order they appear *)
  ; bp_lf_vars : int list   (** The local free variables of all HO arguments (no duplicates) *)
  }

let bp_prop = make "Encode.Flatten.bp_prop"

let bp_count = ref 0
let init_bp_count () = (bp_count := 0)
let new_bp_id () = incr bp_count; !bp_count

(* For debugging *)
let pp_print_bp ff bp =
  Format.fprintf ff "{ bp_id = %d@ ; bp_ctx = %a@ ; bp_orig_ix = %d@ ; bp_ho_args = %a@ ; bp_lf_vars = %a@ }"
  bp.bp_id
  pp_print_ctx bp.bp_ctx
  bp.bp_orig_ix
  (Fmtutil.pp_print_delimited (Expr.Fmt.pp_print_expr (snd bp.bp_ctx, Ctx.dot))) bp.bp_ho_args
  (Fmtutil.pp_print_delimited Format.pp_print_int) bp.bp_lf_vars


(* {3 Functions} *)

let is_sndord_hyp h =
  match h.core with
  | Fresh (_, Shape_op _, _, _) -> true
  | _ -> false

let find_hoapp_visitor = object (self : 'self)
  inherit [int, bp option] Expr.Visit.foldmap as super

  method expr ctx obp oe =
    if Option.is_some obp then (obp, oe)
    else match oe.core with
    | Apply ({ core = Ix n } as op, es) ->
        let obp, es =
          List.fold_left begin fun (obp, r_es) e ->
            let obp, e = self#expr ctx obp e in
            (obp, e :: r_es)
          end (obp, []) es |>
          fun (obp, r_es) ->
            (obp, List.rev r_es)
        in
        if Option.is_some obp then
          (obp, Apply (Ix n @@ op, es) @@ oe)
        else begin

          let h = get_hyp ctx n in
          let ty2 = get_ty2 h in
          if not (is_sndord ty2) then
            (obp, Apply (Ix n @@ op, es) @@ oe)
          else begin

            let Ty2 (ty1s, _) = ty2 in
            let ho_args =
              List.combine es ty1s |>
              List.filter_map begin function
                | _, Ty1 ([], _) -> None
                | e, _ -> Some e
              end
            in

            let is_local ix = (ix <= local_sz ctx) in
            let lf_vars =
              List.fold_left begin fun vs e ->
                let vs_e = Expr.Collect.fvs e in
                let vs_e = Is.filter is_local vs_e in
                Is.union vs vs_e
              end Is.empty ho_args |>
              Is.elements |>
              List.sort ~cmp:(fun i j -> Pervasives.compare j i)
            in

            let bp =
              { bp_id = new_bp_id ()
              ; bp_orig_ix = n
              ; bp_ctx = ctx
              ; bp_ho_args = ho_args
              ; bp_lf_vars = lf_vars
              }
            in
            let op = assign (Ix n @@ op) bp_prop bp in
            (Some bp, Apply (op, es) @@ oe)
          end
        end

    | Sequent sq when Deque.find sq.context is_sndord_hyp |> Option.is_some ->
        (obp, Sequent sq @@ oe)

    | _ -> super#expr ctx obp oe
end

let find_hoapp gtx e =
  let obp, e = find_hoapp_visitor#expr gtx None e in
  Option.map (fun bp -> bp, e) obp


let mk_flat_declaration bp =
  let h = get_hyp bp.bp_ctx bp.bp_orig_ix in
  let Ty2 (ty1s, ty0) = get_ty2 h in
  let ty0s_1 = List.filter_map safe_downcast_ty0 ty1s in
  let ty0s_2 =
    bp.bp_lf_vars |>
    List.map (get_hyp bp.bp_ctx) |>
    List.map get_ty2 |>
    List.map downcast_ty1 |>
    List.map downcast_ty0
  in
  let ty1 = Ty1 (ty0s_1 @ ty0s_2, ty0) in
  let s = hyp_name h ^ "_flatnd_" ^ string_of_int bp.bp_id in
  let v = assign (s %% []) Props.ty1_prop ty1 in
  let shp =
    (*let n = List.length ty0s_1 + List.length ty0s_2 in
    if n = 0 then Shape_expr
    else Shape_op n*)
    Shape_op 0
  in
  Fresh (v, shp, Constant, Unbounded) %% []


let find_axms bp =
  let ctx = bp.bp_ctx in
  let h = get_hyp ctx bp.bp_orig_ix in
  if not (has h N_smb.smb_prop) then
    []
  else begin
    let smb = get h N_smb.smb_prop in
    let gtx =
      Deque.to_list (snd ctx) |>
      List.rev |>
      List.split_nth (local_sz ctx) |>
      snd
    in
    List.fold_left begin fun (es, i) h ->
      match query h N_smb.smb_prop, h.core with
      | Some smb', Fact (e, Visible, _) when N_smb.equal_smb smb smb' ->
          (subst#expr (Subst.shift i) e :: es, i + 1)
      | _, _ ->
          (es, i + 1)
    end ([], 1) gtx |> fst
  end


let mark_visitor = object (self : 'self)
  inherit [bp] Expr.Visit.map as super

  method expr (bp, cx as scx) oe =
    begin match oe.core with
    | Apply ({ core = Ix n } as op, es)
      when n - Deque.size cx = bp.bp_orig_ix - local_sz bp.bp_ctx ->
        let es = List.map (self#expr scx) es in
        (* Dirty hack: setup the lf_vars field for rewriting.
         * The lf_vars indexes are very different in the axioms compared to
         * the original application. *)
        let m = Deque.size cx in
        let lf_vars' = List.init (List.length bp.bp_lf_vars) (fun i -> m - i) in
        let bp' = { bp with bp_lf_vars = lf_vars' } in
        let op = assign op bp_prop bp' in
        Apply (op, es) @@ oe

    | _ -> super#expr scx oe
    end |>
    map_pats (List.map (self#expr scx))
end

let instantiate bp e =
  let ho_args = bp.bp_ho_args in
  let lf_vars = bp.bp_lf_vars in
  let ctx = bp.bp_ctx in

  (* If the local context has depth 5, but only the vars 2 and 4 occur
   * in the HO argument, then the following mapping is applied to it:
     * 1 |-> X
     * 2 |-> 1
     * 3 |-> X
     * 4 |-> 2
     * 5 |-> X
     * 6 |-> 3
     * 7 |-> 4
     * ...
     * n |-> n-3
   * Where 'X' is a dummy expression
   * Other representation:
     * cons(X, cons(1, cons(X, cons(2, cons(X, cons(3, cons(4, ..)))))))
   *)

  (* NOTE For safety, best to use a dummy that SMT does not support,
   * in case it ends up in the final output *)
  let dummy = Bang (Opaque "IAmError" %% [], []) %% [] in
  let maptos =
    List.init (local_sz ctx) (fun i -> i + 1) |> fun l ->
    (* fold left to iterate left-to-right *)
    List.fold_left begin fun (j, maptos) i ->
      if List.mem i lf_vars then
        let j' = j + 1 in
        let e = Ix j' %% [] in
        (j', e :: maptos)
      else
        let e = dummy in
        (j, e :: maptos)
    end (0, []) l |>
    snd |> List.rev
  in
  let shift = Subst.shift (List.length lf_vars) in
  let squash = List.fold_right Subst.scons maptos shift in
  let ho_args = List.map (subst#expr squash) ho_args in

  let inst = List.fold_right Subst.scons ho_args shift in
  let e =
    match e.core with
    | Sequent { context = hs ; active = g } ->
        let hs =
          List.fold_left begin fun hs _ ->
            match Deque.front hs with
            | Some (_, hs) -> hs
            | None -> error ~at:e "Not enough parameters to instantiate"
          end hs ho_args
        in
        if Deque.null hs then
          g $$ e
        else
          Sequent { context = hs ; active = g } @@ e
    | _ -> error ~at:e "Expected a sequent expression"
  in
  let e = subst#expr inst e in

  (* lf_vars set in decreasing order *)
  let bs =
    List.map begin fun ix ->
      let h = get_hyp ctx ix in
      let v = hyp_hint h in
      (v, Constant, No_domain)
    end lf_vars
  in
  let e =
    match bs, e.core with
    | [], _ -> e
    | _, Quant (Forall, bs', e') ->
        Quant (Forall, bs @ bs', e') @@ e
    | _, Sequent { context = hs ; active = e' } ->
        let bs =
          List.map begin fun (v, k, _) ->
            Fresh (v, Shape_expr, k, Unbounded) %% []
          end bs
        in
        let hs = Deque.prepend_list bs hs in
        Sequent { context = hs ; active = e' } @@ e
    | _, _ ->
        Quant (Forall, bs, e) %% []
  in

  mark_visitor#expr (bp, Deque.empty) e


let test_bp_id bp a =
  match query a bp_prop with
  | None -> false
  | Some bp' -> bp.bp_id = bp'.bp_id

let rewrite_expr_visitor = object (self : 'self)
  inherit [int * bp] Expr.Visit.map as super

  method expr ((s, bp), hx as scx) oe =
    begin match oe.core with
    | Apply (op, es) when test_bp_id bp op ->
        (* size(hx) is the depth of the local context.
         * s is the additionnal shift corresponding to the declaration
         * in the top context. *)
        let op' = Ix (Deque.size hx + s) %% [] in
        let h = get_hyp bp.bp_ctx bp.bp_orig_ix in
        let Ty2 (ty1s, _) = get_ty2 h in
        let es_1' =
          List.combine es ty1s |>
          List.filter_map begin function
            | e, Ty1 ([], _) -> Some e
            | _, _ -> None
          end
        in
        let bp' = get op bp_prop in (* Dirty hack (see mark_visitor above) *)
        let es_2' =
          bp'.bp_lf_vars |>
          List.map (fun i -> Ix i %% [])
        in
        Apply (op', es_1' @ es_2') @@ oe

    | _ -> super#expr scx oe
    end |>
    map_pats (List.map (self#expr scx))
end

let rewrite_expr bp s e =
  let scx = ((s, bp), Deque.empty) in
  rewrite_expr_visitor#expr scx e


(* {3 Main} *)

let compare_expr bp1 bp2 e1 e2 =
  (* Compare e1 and e2 in their respective original contexts bp1 and bp2
   * (field bp_ctx).
   * Global variables must match, but since the contexts are desynchronized,
   * only the names are compared (same for function {!same_app} below.)
   * Variables that are bound locally in bp1 or bp2 do not need to match. *)
  let lsz1 = local_sz bp1.bp_ctx in
  let lsz2 = local_sz bp2.bp_ctx in
  let rec comp s e1 e2 =
    match e1.core, e2.core with
    | Ix m, Ix n ->
        if m <= s && n <= s then
          m = n
        else if m > s && (m - s) <= lsz1
             && n > s && (n - s) <= lsz2 then
          true
        else if m > s && (m - s) > lsz1
             && n > s && (n - s) > lsz2 then
          let h1 = get_hyp bp1.bp_ctx (m - s) in
          let h2 = get_hyp bp2.bp_ctx (n - s) in
          hyp_name h1 = hyp_name h2
        else
          false
    | Opaque s1, Opaque s2 ->
        s1 = s2
    | Apply (op1, es1), Apply (op2, es2) ->
        comp s op1 op2 && List.length es1 = List.length es2 && List.for_all2 (comp s) es1 es2
    | Internal b1, Internal b2 ->
        b1 = b2
    | Lambda (vs1, e1), Lambda (vs2, e2)
      when List.length vs1 = List.length vs2 ->
        comp (s + List.length vs1) e1 e2
    | List (bl1, es1), List (bl2, es2) ->
        bl1 = bl2 && List.length es1 = List.length es2 && List.for_all2 (comp s) es1 es2
    | _, _ ->
        false
  in
  comp 0 e1 e2

let same_app bp' bp =
  let h1 = get_hyp bp'.bp_ctx bp'.bp_orig_ix in
  let h2 = get_hyp bp.bp_ctx bp.bp_orig_ix in
  hyp_name h1 = hyp_name h2
  && List.for_all2 (compare_expr bp' bp) bp'.bp_ho_args bp.bp_ho_args

let rec match_previous_bp bps bp =
  match bps with
  | [] -> None
  | bp' :: bps ->
      if same_app bp' bp then Some bp'
      else match_previous_bp bps bp

let treat_expr bps gtx e =
  let rec spin gtx' bps acc e =
    match find_hoapp gtx' e with
    | None ->
        (gtx, bps, acc, e)
    | Some (bp, e') -> begin
      match match_previous_bp bps bp with
      | Some bp' ->
          (* The declaration from a previous call can be recycled *)
          let n, _ =
            Deque.find ~backwards:true (snd gtx') begin fun h ->
              match query h bp_prop with
              | None -> false
              | Some bp -> bp.bp_id = bp'.bp_id
            end |>
            Option.get
          in
          let e' = rewrite_expr bp (n + 1) e' in
          spin gtx' bps acc e'

      | None ->
          let h = mk_flat_declaration bp in
          let h = assign h bp_prop bp in (* to find this hyp again later *)
          let axms = find_axms bp in
          let instantiate bp e =
            Option.fold begin fun e m ->
              assign e meta_prop { m with name = m.name ^ " " ^ hyp_name h }
            end (instantiate bp e) (query e meta_prop)
          in
          let axms = List.map (instantiate bp) axms in

          (* So far the variables of axms and e' are calibrated for the same
           * context gtx.  We need to shift all of them to setup the new context:
           *    gtx, h, axm1, .., axm2, e'
           * After this step, the blueprint annotations in axms and e' will be
           * partially deprecated. *)
          let n = List.length axms in
          let axms =
            List.mapi (fun i -> subst#expr (Subst.shift (i + 1))) axms
          in
          let e' = subst#expr (Subst.shift (n + 1)) e' in

          let axms =
            List.mapi (fun i -> rewrite_expr bp (i + 1)) axms
          in
          let e' = rewrite_expr bp (n + 1) e' in

          let axms = List.map (fun e -> Fact (e, Visible, NotSet) %% []) axms in
          let hs' = h :: axms in
          let gtx' = List.fold_left global_adj gtx' hs' in
          let acc' = Deque.append_list acc hs' in
          spin gtx' (bp :: bps) acc' e'
    end
  in
  spin gtx bps (Deque.empty) e

let main sq =
  init_bp_count ();
  let rec spin bps gtx hs =
    match Deque.front hs with
    | None ->
        snd gtx
    | Some ({ core = Fact (e, Visible, tm) } as h, hs) ->
        let gtx, bps, hs', e = treat_expr bps gtx e in
        let h = Fact (e, Visible, tm) @@ h in
        let gtx = Deque.fold_left global_adj gtx hs' in
        let gtx = global_adj gtx h in
        let shift = Subst.shift (Deque.size hs') in
        let hs = snd (subst#hyps shift hs) in
        spin bps gtx hs
    | Some (h, hs) ->
        let gtx = global_adj gtx h in
        spin bps gtx hs
  in
  let hs = Deque.snoc sq.context (Fact (sq.active, Visible, NotSet) %% []) in
  let gtx = init_ctx in
  let hs = spin [] gtx hs in
  let hs, e =
    match Deque.rear hs with
    | Some (hs, { core = Fact (e, Visible, NotSet) }) -> (hs, e)
    | _ -> error "Internal error"
  in
  { context = hs ; active = e }

