(*
 * expr/eq.ml --- expressions (alpha equivalence)
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

open Property

open E_t

module M = Map.Make (String)

let digest l =
  List.fold_right (fun (v, t) m -> M.add v t m) l M.empty

let digestv l =
  List.fold_right (fun (v, t) m -> M.add v.core t m) l M.empty

let rec expr e f = match e.core, f.core with
  | Parens (e, _), _ -> expr e f
  | _, Parens (f, _) -> expr e f
  | Ix m, Ix n ->
      m = n
  | Opaque p, Opaque q ->
      p = q
  | Internal b, Internal c ->
      b = c
  | Lambda (us, e), Lambda (vs, f) ->
      List.length us = List.length vs && expr e f
  | Apply (p, es), Apply (q, fs) ->
      expr p q && exprs es fs
  | Sequent s, Sequent t ->
      sequent s t
	| Bang (e,ss), Bang (f,tt) ->
		  expr e f && List.for_all2 sel ss tt
  | With (e,_), With (f,_) ->
      expr e f
  | Let (xi, a), Let (phi, b) ->
      defns xi phi && expr a b
  | If (c1, t1, e1), If (c2, t2, e2) ->
      expr c1 c2 && expr t1 t2 && expr e1 e2
  | List (q, es), List (r, fs) ->
      q = r && exprs es fs
  | Quant (q, bs, e), Quant (r, cs, f) ->
      q = r && bounds bs cs && expr e f
  | Tquant (q, us, e), Tquant (r, vs, f) ->
      q = r && us = vs && expr e f
  | Choose (_, Some edom, e), Choose (_, Some fdom, f) ->
      expr edom fdom && expr e f
  | Choose (_, None, e), Choose (_, None, f) ->
      expr e f
  | SetSt (_, r, e), SetSt (_, s, f) ->
      expr r s && expr e f
  | SetOf (e, bs), SetOf (f, cs) ->
      expr e f && bounds bs cs
  | SetEnum es, SetEnum fs ->
      exprs es fs
  | Arrow (a, b), Arrow (c, d) ->
      expr a c && expr b d
  | Fcn (bs, e), Fcn (cs, f) ->
      bounds bs cs && expr e f
  | FcnApp (f, es), FcnApp (g, fs) ->
      exprs (f :: es) (g :: fs)
  | Tuple es, Tuple fs ->
      exprs es fs
  | Product es, Product fs ->
      exprs es fs
  | Rect fs, Rect gs ->
      let fmap = digest fs in
      let gmap = digest gs in
        M.equal expr fmap gmap
  | Record fs, Record gs ->
      let fmap = digest fs in
      let gmap = digest gs in
        M.equal expr fmap gmap
  | Except (e, xs), Except (f, ys) ->
      let rec exspecs xs ys = match xs, ys with
        | [], [] -> true
        | x :: xs, y :: ys ->
            exspec x y && exspecs xs ys
        | _ -> false
      and exspec (tr, e) (ur, f) =
        trail tr ur && expr e f
      and trail tr ur = match tr, ur with
        | [], [] -> true
        | Except_dot x :: tr, Except_dot y :: ur ->
            x = y && trail tr ur
        | Except_apply e :: tr, Except_apply f :: ur ->
            expr e f && trail tr ur
        | _ -> false
      in
        expr e f && exspecs xs ys
  | Dot (e, x), Dot (f, y) ->
      expr e f && x = y
  | Sub (m, e, f), Sub (n, g, h) ->
      m = n && expr e g && expr f h
  | Tsub (m, e, f), Tsub (n, g, h) ->
      m = n && expr e g && expr f h
  | Fair (m, e, f), Fair (n, g, h) ->
      m = n && expr e g && expr f h
  | Case (is, o), Case (js, p) ->
      let arms is js = match is, js with
        | [], [] -> true
        | (e, f) :: is, (g, h) :: js ->
            expr e g && expr f h
        | _ -> false
      in
        arms is js && opt_expr o p
  | String x, String y -> x = y
  | Num (i, j), Num (k, l) ->
      i = k && j = l
  | At b, At c -> b = c
  | ec, fc ->
      false

and exprs es fs = match es, fs with
  | [], [] -> true
  | e :: es, f :: fs ->
      expr e f && exprs es fs
  | _ -> false

and bounds bs cs = match bs, cs with
  | [], [] -> true
  | b :: bs, c :: cs ->
      bound b c && bounds bs cs
  | _ -> false

and bound (_, j, jd) (_, k, kd) =
  j = k && bdom jd kd

and bdom d e = match d, e with
  | No_domain, No_domain -> true
  | Domain d, Domain e -> expr d e
  | Ditto, Ditto -> true
  | _ -> false

and opt_expr eo fo = match eo, fo with
  | None, None -> true
  | Some e, Some f -> expr e f
  | _ -> false

and defns ds es = match ds, es with
  | [], [] -> true
  | d :: ds, e :: es ->
      defn d e && defns ds es
  | _ -> false

and defn d e = match d.core, e.core with
  | Operator (_, e), Operator (_, f) ->
      expr e f
  | Instance (_, i), Instance (_, j) ->
      instance i j
  | Bpragma (_, e, _), Bpragma (_, f, _) ->
			expr e f
  | _ -> false

and sequent s t =
  context s.context t.context && expr s.active t.active

and context cx dx = match Deque.front cx, Deque.front dx with
  | None, None -> true
  | Some (h, cx), Some (g, dx) ->
      hyp h g && context cx dx
  | _ -> false

and hyp h g = match h.core, g.core with
  | Fresh (_, hsh, l, b), Fresh (_, gsh, m, c) ->
      l = m && hsh = gsh && begin
        match b, c with
          | Unbounded, Unbounded -> true
          | Bounded (b, _), Bounded (c, _) -> expr b c
          | _ -> false
      end
  | Flex _, Flex _ -> true
  | Defn (d, _, _, dx), Defn (e, _, _, ex) ->
      defn d e && dx = ex
  | Fact (e, _, _), Fact (f, _, _) ->
      expr e f
  | _ -> false

and instance i j =
  i.inst_args = j.inst_args
  && i.inst_mod = j.inst_mod
  && sub i.inst_sub j.inst_sub

and sub ss tt =
  let umap = digestv ss in
  let tmap = digestv tt in
    M.equal expr umap tmap

and sel s t = match s, t with
	| Sel_down, Sel_down -> true
	| Sel_num n, Sel_num m -> n = m
	| Sel_left, Sel_left
	| Sel_right, Sel_right
	| Sel_at, Sel_at -> true
	| Sel_inst es, Sel_inst fs -> exprs es fs
	| Sel_lab (s, es), Sel_lab (t, fs) -> s = t && exprs es fs
	| _ -> false
