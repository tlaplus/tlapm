(* Substitution within expressions.

Copyright (C) 2008-2019  INRIA and Microsoft Corporation
*)
open Ext
open Property
open E_t

module Dq = Deque
module Fmt = E_fmt


type sub =
  | Shift of int
  | Cons of expr * sub
  | Compose of sub * sub
  | Bump of int * sub

let shift n = Shift n
let scons e s = Cons (e, s)
let ssnoc s e = Cons (e, s)
let compose s t = Compose (s, t)

let bumpn n = function
  | Bump (k, s) -> Bump (k + n, s)
  | s -> Bump (n, s)

let bump s = bumpn 1 s

let rec app_expr s oe = match oe.core with
  | ( Internal _ | Opaque _ | String _ | Num _ | At _ ) ->
      oe
  | Ix n ->
      app_ix s (n @@ oe)
  | Apply (op, fs) ->
      normalize (app_expr s op) (app_exprs s fs) @@ oe
  | Bang (e, sels) ->
      Bang (app_expr s e, List.map (app_sel s) sels) @@ oe
  | Lambda (vs, e) ->
      Lambda (vs, app_expr (bumpn (List.length vs) s) e) @@ oe
  | Let (ds, e) ->
      let (s, ds) = app_defns s ds in
      Let (ds, app_expr s e) @@ oe
  | Sequent sq ->
      Sequent (app_sequent s sq) @@ oe
  | With (e, meth) ->
      With (app_expr s e, meth) @@ oe
  | If (e, f, g) ->
      If (app_expr s e, app_expr s f, app_expr s g) @@ oe
  | List (q, es) ->
      List (q, app_exprs s es) @@ oe
  | Quant (q, bs, e) ->
      let (s, bs) = app_bounds s bs in
      Quant (q, bs, app_expr s e) @@ oe
  | Tquant (q, vs, e) ->
      Tquant (q, vs, app_expr (bumpn (List.length vs) s) e) @@ oe
  | Choose (v, optdom, e) ->
      let optdom = Option.map (app_expr s) optdom in
      Choose (v, optdom, app_expr (bump s) e) @@ oe
  | SetSt (v, dom, e) ->
      SetSt (v, app_expr s dom, app_expr (bump s) e) @@ oe
  | SetOf (e, bs) ->
      let (s, bs) = app_bounds s bs in
      SetOf (app_expr s e, bs) @@ oe
  | SetEnum es ->
      SetEnum (app_exprs s es) @@ oe
  | Arrow (a, b) ->
      Arrow (app_expr s a, app_expr s b) @@ oe
  | Fcn (bs, e) ->
      let (s, bs) = app_bounds s bs in
      Fcn (bs, app_expr s e) @@ oe
  | FcnApp (f, es) ->
      FcnApp (app_expr s f, app_exprs s es) @@ oe
  | Product es ->
      Product (app_exprs s es) @@ oe
  | Tuple es ->
      Tuple (app_exprs s es) @@ oe
  | Rect fs ->
      Rect (List.map (fun (v, e) -> (v, app_expr s e)) fs) @@ oe
  | Record fs ->
      Record (List.map (fun (v, e) -> (v, app_expr s e)) fs) @@ oe
  | Except (e, xs) ->
      Except (app_expr s e, app_xs s xs) @@ oe
  | Dot (e, f) ->
      Dot (app_expr s e, f) @@ oe
  | Sub (m, e, f) ->
      Sub (m, app_expr s e, app_expr s f) @@ oe
  | Tsub (m, e, f) ->
      Tsub (m, app_expr s e, app_expr s f) @@ oe
  | Fair (m, e, f) ->
      Fair (m, app_expr s e, app_expr s f) @@ oe
  | Case (arms, oth) ->
      Case (List.map (fun (e, f) -> (app_expr s e, app_expr s f)) arms,
            Option.map (app_expr s) oth) @@ oe
  | Parens (e, rig) -> Parens (app_expr s e, rig) @@ oe
  | QuantTuply _
  | ChooseTuply _
  | SetStTuply _
  | SetOfTuply _
  | FcnTuply _ -> assert false

and app_exprs s es =
  List.map (fun e -> app_expr s e) es

and normalize ?(cx = Deque.empty) op args = match op.core with
  | Lambda (vs, e) ->
      if List.length vs <> List.length args then begin
        Errors.set op "Arity mismatch";
        Util.eprintf ~at:op
          "@[<v0>Arity mismatch:@,op =@,  %a@,args =@,  @[<v0>%a@]@]@."
          (Fmt.pp_print_expr (cx, Ctx.dot)) op
          (Fmtutil.pp_print_delimited
             (Fmt.pp_print_expr (cx, Ctx.dot))) args ;
        failwith "Expr.Subst.normalize"
      end else begin
        let sub = List.fold_left ssnoc (shift 0) args in
        (app_expr sub e).core
      end
  | Apply (op, oargs) ->
      Apply (op, oargs @ args)
  | _ -> begin
      match args with
        | [] -> op.core
        | _ -> Apply (op, args)
    end

and app_sel s = function
  | Sel_inst args ->
      Sel_inst (app_exprs s args)
  | Sel_lab (l, args) ->
      Sel_lab (l, app_exprs s args)
  | sel -> sel

and app_bdom s = function
  | Domain d -> Domain (app_expr s d)
  | d -> d

and app_bounds s bs =
  let bs = List.map begin
    fun (v, k, dom) -> match dom with
      | Domain d -> (v, k, Domain (app_expr s d))
      | _ -> (v, k, dom)
  end bs in
  let s = bumpn (List.length bs) s in
  (s, bs)

and app_bound s b = match app_bounds s [b] with
  | (s, [b]) -> (s, b)
  | _ -> assert false

and app_xs s xs =
  List.map (fun x -> app_x s x) xs

and app_x s (trail, res) =
  (List.map (function
               | Except_dot s -> Except_dot s
               | Except_apply e -> Except_apply (app_expr s e)) trail,
   app_expr s res)

(* [PERF] this is the hottest function in the PM (ignoring GC) *)
and app_ix s n = match s with
  | Shift m -> Ix (m + n.core) @@ n
  | Cons (op, _) when n.core = 1 -> op.core @@ n  (* app_ix Cons(op, s) (1 @@ oe) = op.core @@ oe *)
  | Cons (_, s) -> app_ix s (n.core - 1 @@ n)  (* app_ix Cons(op, s) (i @@ oe) = app_ix s ((i - 1) @@ oe) *)
  | Compose (ss, tt) -> app_expr ss (app_ix tt n)
    (* `app_ix` returns `Ix` so could call `app_ix` directly,
    instead of `app_expr` *)
  | Bump (k, ss) when n.core <= k -> Ix n.core @@ n
  | Bump (k, ss) -> app_expr (Shift k) (app_ix ss (n.core - k @@ n))
    (* could call `app_ix` directly, instead of `app_expr` *)

and app_defn s d =
  { d with core = app_defn_ s d.core }

and app_defn_ s = function
  | Recursive (nm, shp) -> Recursive (nm, shp)
  | Operator (nm, e) -> Operator (nm, app_expr s e)
  | Instance (nm, inst) -> Instance (nm, app_instance s inst)
  | Bpragma (nm, e, l) -> Bpragma (nm, app_expr s e, l)

and app_defns s = function
  | [] -> (s, [])
  | d :: ds ->
      let d = app_defn s d in
      let (s, ds) = app_defns (bump s) ds in
      (s, d :: ds)

and app_instance s i =
  let s = bumpn (List.length i.inst_args) s in
  { i with inst_sub = List.map (fun (v, e) -> (v, app_expr s e)) i.inst_sub }

and app_sequent s sq =
  let (s, cx) = app_hyps s sq.context in
  { context = cx ; active = app_expr s sq.active }

and app_hyps s cs = match Deque.front cs with
  | None -> (s, Deque.empty)
  | Some (c, cs) ->
      let c = app_hyp s c in
      let (s, cs) = app_hyps (bump s) cs in
      (s, Deque.cons c cs)

and app_hyp s h = match h.core with
  | Fresh (x, shp, lv, b) -> Fresh (x, shp, lv, app_dom s b) @@ h
  | FreshTuply _ -> assert false  (* not implemented *)
  | Flex v -> Flex v @@ h
  | Defn (d, wd, us, ex) -> Defn (app_defn s d, wd, us, ex) @@ h
  | Fact (e, us,tm) -> Fact (app_expr s e, us,tm) @@ h

and app_dom s = function
  | Unbounded -> Unbounded
  | Bounded (dom, vis) -> Bounded (app_expr s dom, vis)

let rec app_spine s = function
  | [] -> []
  | e :: es ->
      app_expr s e :: app_spine (bump s) es

open Format
open E_fmt

let pp_print_sub cx ff =
  let rec handle ff s = match s with
    | Shift n ->
        fprintf ff "^%d" n
    | Cons (op, s) ->
        pp_print_expr cx ff op ;
        pp_print_string ff " ." ;
        pp_print_space ff () ;
        handle ff s
    | Compose (s, t) ->
        fprintf ff "(%a) o (%a)" handle s handle t
    | Bump (n, s) ->
        fprintf ff "%d(%a)" n handle s
  in
  fprintf ff "@[<b1>[%a]@]" handle


let extract sq k =
  let prefix : hyp Deque.dq ref = ref Deque.empty in
  let rec scan n hs = match Deque.front hs with
    | None -> failwith "scan"
    | Some (h, hs) ->
        if n = k then (h, hs) else
          begin
            prefix := Deque.snoc !prefix h ;
            scan (n + 1) hs
          end
  in try begin
    let (h, hs) = scan 0 sq.context in
    let e = match h.core with
      | Fact (e, _, _) -> app_expr (shift (Deque.size hs)) e
      | _ -> failwith "exprtract" in
    let (s, hs) = app_hyps (shift (-1)) hs in
    let sq = {
      context = Deque.append !prefix hs ;
      active = app_expr s sq.active ;
    } in
    Some (sq, e)
  end with _ -> None


let bump s = bumpn 1 s  (* distinguish from `E_fmt.bump` *)


class map = object (self : 'self)
    (* Apply a substitution to an expression.

    This class is equivalent to the recursive functions defined above.
    It allows subclassing to modify methods for those pattern cases needed.
    *)

  method expr (s: sub) (oe: E_t.expr): expr = match oe.core with
    | Ix n ->
        app_ix s (n @@ oe)
    | Internal b ->
        Internal b @@ oe
    | Opaque o ->
        Opaque o @@ oe
    | Bang (e, sels) ->
        Bang (self#expr s e, self#sels s sels) @@ oe
    | Lambda (vs, e) ->
        let s = (bumpn (List.length vs) s) in
        Lambda (vs, self#expr s e) @@ oe
    | String t ->
        String t @@ oe
    | Num (m, n) ->
        Num (m, n) @@ oe
    | Apply (op, es) ->
        self#normalize (self#expr s op) (self#exprs s es) @@ oe
    | Sequent sq ->
        let (_, sq) = self#sequent s sq in
        Sequent sq @@ oe
    | With (e, m) ->
        With (self#expr s e, m) @@ oe
    | Let (ds, e) ->
        let (s, ds) = self#defns s ds in
        Let (ds, self#expr s e) @@ oe
    | If (e, f, g) ->
        If (self#expr s e, self#expr s f, self#expr s g) @@ oe
    | List (q, es) ->
        List (q, self#exprs s es) @@ oe
    | Quant (q, bs, e) ->
        let (s, bs) = self#bounds s bs in
        Quant (q, bs, self#expr s e) @@ oe
    | Tquant (q, vs, e) ->
        let s = bumpn (List.length vs) s in
        Tquant (q, vs, self#expr s e) @@ oe
    | Choose (v, optdom, e) ->
        let optdom = Option.map (self#expr s) optdom in
        let s = bump s in
        let e = self#expr s e in
        Choose (v, optdom, e) @@ oe
    | SetSt (v, dom, expr) ->
        let dom = self#expr s dom in
        let s = bump s in
        let e = self#expr s expr in
        SetSt (v, dom, e) @@ oe
    | SetOf (e, bs) ->
        let (s, bs) = self#bounds s bs in
        SetOf (self#expr s e, bs) @@ oe
    | SetEnum es ->
        SetEnum (self#exprs s es) @@ oe
    | Fcn (bs, e) ->
        let (s, bs) = self#bounds s bs in
        Fcn (bs, self#expr s e) @@ oe
    | FcnApp (f, es) ->
        FcnApp (self#expr s f, self#exprs s es) @@ oe
    | Arrow (a, b) ->
        Arrow (self#expr s a, self#expr s b) @@ oe
    | Product es ->
        Product (self#exprs s es) @@ oe
    | Tuple es ->
        Tuple (self#exprs s es) @@ oe
    | Rect fs ->
        Rect (List.map (fun (v, e) -> (v, self#expr s e)) fs) @@ oe
    | Record fs ->
        Record (List.map (fun (v, e) -> (v, self#expr s e)) fs) @@ oe
    | Except (e, xs) ->
        Except (self#expr s e, List.map (self#exspec s) xs) @@ oe
    | Dot (e, f) ->
        Dot (self#expr s e, f) @@ oe
    | Sub (modal_op, e, f) ->
        Sub (modal_op, self#expr s e, self#expr s f) @@ oe
    | Tsub (modal_op, e, f) ->
        Tsub (modal_op, self#expr s e, self#expr s f) @@ oe
    | Fair (fop, e, f) ->
        Fair (fop, self#expr s e, self#expr s f) @@ oe
    | Case (arms, oth) ->
        Case (List.map (fun (e, f) -> (self#expr s e, self#expr s f)) arms,
              Option.map (self#expr s) oth) @@ oe
    | At b ->
        At b @@ oe
    | Parens (e, pf) ->
        Parens (self#expr s e, self#pform s pf) @@ oe
    | QuantTuply _
    | ChooseTuply _
    | SetStTuply _
    | SetOfTuply _
    | FcnTuply _ -> assert false  (* not implemented *)

  method exprs s es = List.map (self#expr s) es

  method pform s pf = pf

  method sels s sels = List.map (self#sel s) sels

  method sel s sel = match sel with
    | Sel_inst args ->
        Sel_inst (self#exprs s args)
    | Sel_lab (l, args) ->
        Sel_lab (l, self#exprs s args)
    | _ -> sel

  method sequent s sq =
    let (s, hyps) = self#hyps s sq.context in
    (s, { context = hyps;
          active = self#expr s sq.active })

  method defn s df =
    let df = match df.core with
      | Recursive (nm, shp) -> df
      | Operator (nm, e) ->
          { df with core = Operator (nm, self#expr s e) }
      | Instance (nm, i) ->
          { df with core = Instance (nm, self#instance s i) }
      | Bpragma(nm, e, l) ->
          { df with core = Bpragma (nm, self#expr s e, l) }
    in
    (* incremental bumping *)
    (bump s, df)

  method defns s dfs =
    match dfs with
    | [] -> (s, [])
    | df :: dfs ->
        let (s, df) = self#defn s df in
        let (s, dfs) = self#defns s dfs in
        (s, df :: dfs)

  method bounds s bs =
    let bs = List.map (self#bound s) bs in
    let n = List.length bs in
    let s = bumpn n s in
    (s, bs)

  method bound s b =
    let (v, k, dom) = b in
    let dom = match dom with
        | Domain d -> Domain (self#expr s d)
        | _ -> dom
        in
    (v, k, dom)

  method exspec s (trail, res) =
    let do_trail = function
      | Except_dot s -> Except_dot s
      | Except_apply e -> Except_apply (self#expr s e)
    in
    (List.map do_trail trail, self#expr s res)

  method instance s i =
    let s = bumpn (List.length i.inst_args) s in
    { i with inst_sub =
        List.map (fun (v, e) -> (v, self#expr s e))
            i.inst_sub }

  method hyp s h =
    let h = begin match h.core with
    | Fresh (nm, shp, lc, dom) ->
        let dom = match dom with
          | Unbounded -> Unbounded
          | Bounded (r, rvis) -> Bounded (self#expr s r, rvis)
        in
        Fresh (nm, shp, lc, dom) @@ h
    | FreshTuply _ -> assert false  (* not implemented *)
    | Flex v -> Flex v @@ h
    | Defn (df, wd, vis, ex) ->
        let (s', df) = self#defn s df in
        assert (s' = bump s);
        Defn (df, wd, vis, ex) @@ h
    | Fact (e, vis, tm) ->
        Fact (self#expr s e, vis, tm) @@ h
    end in
    (* incremental bumping, as in `self#defn` *)
    (bump s, h)

  method hyps s hs = match Dq.front hs with
    | None -> (s, Dq.empty)
    | Some (h, hs) ->
        let (s, h) = self#hyp s h in
        let (s, hs) = self#hyps s hs in
        (s, Dq.cons h hs)

  method normalize ?(cx = Deque.empty) op args = match op.core with
    | Lambda (vs, e) ->
      if List.length vs <> List.length args then begin
        Errors.set op "Arity mismatch";
        Util.eprintf ~at:op
          "@[<v0>Arity mismatch:@,op =@,  %a@,args =@,  @[<v0>%a@]@]@."
          (Fmt.pp_print_expr (cx, Ctx.dot)) op
          (Fmtutil.pp_print_delimited
             (Fmt.pp_print_expr (cx, Ctx.dot))) args ;
        failwith "Expr.Subst.map#normalize"
      end else begin
        let sub = List.fold_left ssnoc (shift 0) args in
        (self#expr sub e).core
      end
    | Apply (op, oargs) ->
      Apply (op, oargs @ args)
    | _ -> begin
      match args with
        | [] -> op.core
        | _ -> Apply (op, args)
    end

end


class map_visible_hyp = object (self: 'self)
    inherit map as super
    (* Apply a substitution to an expression,
    visiting only visible hypotheses in a sequent's context.
    *)

    method hyp s h =
      begin match h.core with
      | Fresh _ | Flex _ -> super#hyp s h
      | FreshTuply _ -> assert false  (* not implemented *)
      | Defn (_, _, Hidden, _)
      | Fact (_, Hidden, _) -> (bump s, h)
      | Defn _ | Fact _ -> super#hyp s h
      end
end
