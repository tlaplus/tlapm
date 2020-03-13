(*
 * reduce/nt_cook.ml
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

open Ext
open Expr.T
open Type.T
open Property
open Util.Coll

module A = R_nt_axioms
module B = Builtin


type hyp_nm = string

let scount = ref 0
let get_scount () =
  scount := !scount + 1;
  !scount

(* FIXME this is not very good *)
let choose_nm _ _ = "cooked_" ^ string_of_int (get_scount ())
let setst_nm _ _ = "cooked_" ^ string_of_int (get_scount ())
let setof_nm _ _ _ = "cooked_" ^ string_of_int (get_scount ())
let fcn_nm _ _ _ = "cooked_" ^ string_of_int (get_scount ())

(* FIXME There is a major flaw in the way reduction is performed.  It cannot
 * handle nested lambdas.  If there is a nested lambda, it will be replaced by
 * an applied first-order operator, but this one will in turn disappear when
 * the upper lambda is treated.  I am giving up on this bug because it requires
 * too much dirty work to be resolved, and I already intend to revise the
 * encoding process. *)
let choose_special_prop = make "Reduce.Cook.choose_special_prop"
let setst_special_prop = make "Reduce.Cook.setst_special_prop"
let setof_special_prop = make "Reduce.Cook.setof_special_prop"
let fcn_special_prop = make "Reduce.Cook.setof_special_prop"


(* {3 Mark Global Variables} *)

let is_global_prop = make "Reduce.Cook.is_global_prop"

let mark_global = object (self : 'self)
  inherit [unit] Expr.Visit.map as super

  method expr _ oe = oe (* Gain some time *)

  method hyp scx h =
    match h.core with
    | Fresh (nm, shp, lc, dom) ->
        let nm = assign nm is_global_prop () in
        let h = Fresh (nm, shp, lc, dom) @@ h in
        (Expr.Visit.adj scx h, h)
    | Flex s ->
        let s = assign s is_global_prop () in
        let h = Flex s @@ h in
        (Expr.Visit.adj scx h, h)
    | Defn (df, wd, vis, ex) ->
        let df =
          match df.core with
          | Recursive (nm, shp) ->
              let nm = assign nm is_global_prop () in
              Recursive (nm, shp) @@ df
          | Operator (nm, e) ->
              let nm = assign nm is_global_prop () in
              Operator (nm, e) @@ df
          | Instance (nm, i) ->
              let nm = assign nm is_global_prop () in
              Instance (nm, i) @@ df
          | Bpragma (nm, e, l) ->
              let nm = assign nm is_global_prop () in
              Bpragma (nm, e, l) @@ df
        in
        let h = Defn (df, wd, vis, ex) @@ h in
        (Expr.Visit.adj scx h, h)
    | Fact (e, vis, tm) ->
        let h = Fact (e, vis, tm) @@ h in
        (Expr.Visit.adj scx h, h)
end


(* {3 Relocalization} *)

(* Assuming [hx] is of the form [hx1 @ hx2] where all hyps in [hx1] are marked
 * global and none in [hx2], this function returns [(hx1, hx2)]. *)
let split_ctx hx =
  let rec spin l r =
    match Deque.rear l with
    | None ->
        (l, r)
    | Some (_, h) when has (hyp_hint h) is_global_prop ->
        (l, r)
    | Some (l, h) ->
        spin l (Deque.cons h r)
  in
  spin hx Deque.empty

let split_set n is =
  Is.partition (fun i -> i > n) is

let dummy = Opaque "error" %% []

(* A context map describes a transformation of a local context.
 * Starting from the bottom (Ix 1), each instruction specifies what to do with
 * a bound variable. *)
type ctx_map = instruction list
and instruction =
  | Keep  (* Keep this variable in the new context *)
  | Skip  (* Do not keep this variable in the new context *)
  | Intro (* Introduce a fresh variable *)

(* Example: the context is [a, x, y], the expression has the form E(a, y).
 * We want to relocalize this expression from the local context [x, y] to the
 * new local context [y, z].  The map for this is:
 *  Intro   to insert the fresh 'z'
 *  Keep    to keep 'y'
 *  Skip    to skip 'x'
 * As for the variable 'a', it is treated as a global variable; a final shift
 * will correct its index. *)

let mk_renaming m =
  (* The result subst. has the form 'cons x1 (cons x2 .. (shift s) ..)'
   * where 'xi' is either a dummy expr. or an int, and the sequence increases.
   * The 's' parameter corrects global vars.  It must be equal to the length of
   * the new local context. *)
  let (n, dq) =
    List.fold_left begin fun (n, dq) -> function
      | Keep ->
          (n + 1, Deque.snoc dq (Some n))
      | Skip ->
          (n, Deque.snoc dq None)
      | Intro ->
          (n + 1, dq)
    end (1, Deque.empty) m
  in
  let s = n - 1 in
  Deque.fold_right begin function
    | None -> Expr.Subst.scons dummy
    | Some k -> Expr.Subst.scons (Ix k %% [])
  end dq (Expr.Subst.shift s)

let relocalize e m =
  let sub = mk_renaming m in
  Expr.Subst.app_expr sub e


(* {3 Main} *)

let hyp_sort hx ix =
  let h = (get_val_from_id hx ix) in
  get_sort (hyp_hint h)

let visitor = object (self : 'self)
  inherit [unit] Expr.Visit.map as super

  method expr (_, hx as scx) oe =
    match oe.core with
    | Choose (h, optdom, e) ->
        let optdom = Option.map (self#expr scx) optdom in
        let hyp = match optdom with
          | None -> Fresh (h, Shape_expr, Constant, Unbounded) @@ h
          | Some dom -> Fresh (h, Shape_expr, Constant, Bounded (dom, Visible)) @@ h
        in
        let (_, hx' as scx') = Expr.Visit.adj scx hyp in
        let e = self#expr scx' e in

        let gx, lx = split_ctx hx' in
        let lsz = Deque.size lx in
        let vs = Expr.Collect.fvs e in
        let gvs, lvs = split_set lsz vs in
        let lvs' = Is.add 1 lvs in

        let m =
          List.init lsz begin fun i ->
            if Is.mem (i + 1) lvs' then Keep
            else Skip
          end
          @ [ Intro ]
        in
        let e = relocalize e m in

        let nm, e =
          if Is.is_empty gvs then begin
            None, e
          end else begin
            let m = Is.min_elt gvs in
            let v = hyp_name (get_val_from_id gx (m - lsz)) in
            let s = lsz - m + 1 in
            let d = 1 + Is.cardinal lvs' in
            let sub = Expr.Subst.bumpn d (Expr.Subst.shift s) in
            let e = Expr.Subst.app_expr sub e in
            Some v, e
          end
        in

        let args = lvs
          |> Is.remove 1
          |> Is.elements
          |> List.map (fun i -> i - 1)
          |> List.rev
        in

        let e =
          match optdom with
          | None -> e
          | Some dom ->
              Apply (Internal B.Conj %% [], [
                Apply (Internal B.Mem %% [], [ Ix 1 %% [] ; dom ]) %% []
              ; e ]) %% []
        in

        let ins = List.map (hyp_sort hx) args in
        let k = mk_fstk_ty (List.map mk_atom_ty ins) ty_u in
        let s = choose_nm k e in
        let op = assign (Opaque s %% []) choose_special_prop (nm, k, e) in
        (* NOTE If the result is Apply(op, []), then a flaw in app_expr will
         * make the properties of op disappear.  The problem is in the function
         * {!Expr.Subst.normalize}. *)
        begin match args with
        | [] -> op $$ oe
        | _ -> Apply (op, List.map (fun i -> Ix i %% []) args) @@ oe
        end

    | SetSt (h, e1, e2) ->
        let e1 = self#expr scx e1 in
        let hyp = Fresh (h, Shape_expr, Constant, Bounded (e1, Visible)) @@ h in
        let (_, hx' as scx') = Expr.Visit.adj scx hyp in
        (* distinct name for hx' bc we need to contextualize the final
         * expression in hx at the end *)
        let e2 = self#expr scx' e2 in

        let gx, lx = split_ctx hx' in
        let lsz = Deque.size lx in
        let vs = Expr.Collect.fvs e2 in
        let gvs, lvs = split_set lsz vs in
        let lvs' = Is.add 1 lvs in (* count the 'x \in ..' even if absent *)

        let m =
          List.init lsz begin fun i ->
            if Is.mem (i + 1) lvs' then Keep
            else Skip
          end
          @ [ Intro ; Intro ]
        in
        let e2 = relocalize e2 m in

        (* shift global variables along skipped global ctx *)
        (* FIXME This part would not be necessary if the hypothesis was
         * simply inserted at the end of the global ctx *)
        let nm, e2 =
          if Is.is_empty gvs then begin
            None, e2
          end else begin
            let m = Is.min_elt gvs in
            let v = hyp_name (get_val_from_id gx (m - lsz)) in
            let s = lsz - m + 1 in
            let d = 1 + Is.cardinal lvs' in
            let sub = Expr.Subst.bumpn d (Expr.Subst.shift s) in
            let e2 = Expr.Subst.app_expr sub e2 in
            Some v, e2
          end
        in

        let args = lvs
          |> Is.remove 1
          |> Is.elements
          |> List.map (fun i -> i - 1)
          |> List.rev
        in

        let ins = List.map (hyp_sort hx) args in
        let k = mk_fstk_ty (ty_u :: List.map mk_atom_ty ins) ty_u in
        let s = setst_nm k e2 in
        let op = assign (Opaque s %% []) setst_special_prop (nm, k, e2) in
        Apply (op, e1 :: List.map (fun i -> Ix i %% []) args) @@ oe

    | SetOf (e, bs) ->
        let ((_, hx' as scx'), bs) = self#bounds scx bs in
        let e = self#expr scx' e in
        let n = List.length bs in

        let gx, lx = split_ctx hx' in
        let lsz = Deque.size lx in
        let vs = Expr.Collect.fvs e in
        let gvs, lvs = split_set lsz vs in

        let m =
          List.init n (fun _ -> Keep)
          @ [ Intro ]
          @ List.init (lsz - n) begin fun i ->
            if Is.mem (n + i + 1) lvs then Keep
            else Skip
          end
          @ List.init n (fun _ -> Intro)
          @ [ Intro ]
        in
        let e = relocalize e m in

        (* FIXME see same remark for setst *)
        let nm, e =
          if Is.is_empty gvs then begin
            None, e
          end else begin
            let m = Is.min_elt gvs in
            let v = hyp_name (get_val_from_id gx (m - lsz)) in
            let s = lsz - m + 1 in
            let lvs' = Is.union lvs (List.init n (fun i -> i+1) |> Is.of_list) in
            let d = 2*n + 1 + Is.cardinal lvs' in
            let sub = Expr.Subst.bumpn d (Expr.Subst.shift s) in
            let e = Expr.Subst.app_expr sub e in
            Some v, e
          end
        in

        let _, bs = List.fold_left begin fun (last, bs) (_, _, dom) ->
          match dom, last with
          | Domain d, _
          | Ditto, Some d -> (Some d, d :: bs)
          | _ -> invalid_arg "Reduce.Cook.cook: missing bound in SetOf"
        end (None, []) bs in
        let bs = List.rev bs in

        let args = lvs
          |> fun s -> Is.diff s (List.init n (fun i -> i+1) |> Is.of_list)
          |> Is.elements
          |> List.map (fun i -> i - n)
          |> List.rev
        in

        let ins = List.map (hyp_sort hx) args in
        let k = mk_fstk_ty (List.init n (fun _ -> ty_u) @ List.map mk_atom_ty ins) ty_u in
        let s = setof_nm n k e in
        let op = assign (Opaque s %% []) setof_special_prop (nm, n, k, e) in
        Apply (op, bs @ List.map (fun i -> Ix i %% []) args) @@ oe

    | Fcn (bs, e) ->
        let ((_, hx' as scx'), bs) = self#bounds scx bs in
        let e = self#expr scx' e in
        let n = List.length bs in

        let gx, lx = split_ctx hx' in
        let lsz = Deque.size lx in
        let vs = Expr.Collect.fvs e in
        let gvs, lvs = split_set lsz vs in

        let m =
          List.init n (fun _ -> Keep)
          @ List.init (lsz - n) begin fun i ->
            if Is.mem (n + i + 1) lvs then Keep
            else Skip
          end
          @ List.init n (fun _ -> Intro)
          @ [ Intro ; Intro ]
        in
        let e = relocalize e m in

        (* FIXME see same remark for setst *)
        let nm, e =
          if Is.is_empty gvs then begin
            None, e
          end else begin
            let m = Is.min_elt gvs in
            let v = hyp_name (get_val_from_id gx (m - lsz)) in
            let s = lsz - m + 1 in
            let lvs' = Is.union lvs (List.init n (fun i -> i+1) |> Is.of_list) in
            let d = 2*n + 1 + Is.cardinal lvs' in
            let sub = Expr.Subst.bumpn d (Expr.Subst.shift s) in
            let e = Expr.Subst.app_expr sub e in
            Some v, e
          end
        in

        let _, bs = List.fold_left begin fun (last, bs) (_, _, dom) ->
          match dom, last with
          | Domain d, _
          | Ditto, Some d -> (Some d, d :: bs)
          | _ -> invalid_arg "Reduce.Cook.cook: missing bound in Fcn"
        end (None, []) bs in
        let bs = List.rev bs in

        let args = lvs
          |> fun s -> Is.diff s (List.init n (fun i -> i+1) |> Is.of_list)
          |> Is.elements
          |> List.map (fun i -> i - n)
          |> List.rev
        in

        let ins = List.map (hyp_sort hx) args in
        let k = mk_fstk_ty (List.init n (fun _ -> ty_u) @ List.map mk_atom_ty ins) ty_u in
        let s = fcn_nm n k e in
        let op = assign (Opaque s %% []) fcn_special_prop (nm, n, k, e) in
        Apply (op, bs @ List.map (fun i -> Ix i %% []) args) @@ oe

    | _ -> super#expr scx oe
end

let cook sq =
  scount := 0;
  let _, sq = mark_global#sequent ((), Deque.empty) sq in
  let _, sq = visitor#sequent ((), Deque.empty) sq in
  sq
