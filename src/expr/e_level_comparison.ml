(*
 * expr/level_compare.ml --- expression level comparison
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

open Property
open E_t

module StringMap = Util.Coll.Sm


let digest l =
  List.fold_right (fun (v, t) m -> StringMap.add v t m) l StringMap.empty

let digestv l =
  List.fold_right (fun (v, t) m -> StringMap.add v.core t m) l StringMap.empty

type kind = Kconstant | Kstate | Kaction | Ktemporal | Kunknown |
            Kvariable | Kdefinition


(* The level comparison algorithm works by comparing the sequents and
expressions found in the hypotheses of a proof obligation to the goal of
the proof obligation. Assuming a proof obligation of the form

ASSUME
    declarations1,
    expr1,
    ASSUME declarations2
    PROVE expr2,
    declarations3
PROVE
    goal

the algorithm checks that goal results from expr1 or expr2 by a renaming of
identifiers that does not increase the levels of the identifiers.

If an identifier is renamed, then it is assumed that the identifier before
renaming is declared in declarations2. This ensures correct instantiation
of universal quantifiers, outside of the quantifier scope.

If an identifier is not renamed, then the original identifier can occur in
either declarations1 or declarations2. If the identifier occurs in declarations1
then the identifier is the same declaration in both expr1 and goal or
expr2 and goal. There is no substitution for that identifier in this case.

If the original identifier occurs in declarations2, then the identical
identifier in goal is from declarations3, and the substitution is sound.

*)
class level_comparison = object (self : 'self)

    val mutable ctx1: ctx = Deque.empty
    val mutable ctx2: ctx = Deque.empty
    val mutable op_mapping: string StringMap.t = StringMap.empty

    method compare ctx1_ ctx2_ expr1 expr2 =
        ctx1 <- ctx1_;
        ctx2 <- ctx2_;
        op_mapping <- StringMap.empty;
        let res = self#expr ctx1_ ctx2_ expr1 expr2 in
        let all = ref true in
        let check (key: string) (value: string) =
            if not (key = value) then begin
                let found = ref false in
                Deque.iter begin
                    fun i hyp ->
                        match hyp.core with
                        | Fresh (nm, _, _, _)
                        | Flex nm
                        | Defn ({core=Operator (nm, _)}, _, _, _) ->
                            found := !found || (nm.core = key)
                        | Fact _ -> ()
                        | _ -> assert false
                            (* Defn ( Recursive | Instance | Bpragrama ) *)
                end ctx1;
                all := !all && !found
            end in
        StringMap.iter check op_mapping;
        res && !all

    method expr cx1 cx2 e f =
        (* print_string (E_fmt.string_of_expr cx1 e);
        print_string "\n";
        print_string (E_fmt.string_of_expr cx2 f);
        print_string "\n"; *)
        match e.core, f.core with
        | Parens (e, _), _ -> self#expr cx1 cx2 e f
        | _, Parens (f, _) -> self#expr cx1 cx2 e f
        | Ix m,
          Ix n ->
            let get_hyp cx n = begin
                let hyp = get_val_from_id cx n in
                match hyp.core with
                | Fresh (nm, shp, kind, dom) ->
                    let name = nm.core in
                    begin match kind with
                    | Constant -> (name, Kconstant, 0)
                    | State -> (name, Kstate, 1)
                    | Action -> (name, Kaction, 2)
                    | Temporal -> (name, Ktemporal, 3)
                    | Unknown -> (name, Kunknown, -1)
                    end
                | Flex nm ->
                    (nm.core, Kvariable, 1)
                | Defn ({core=Operator (nm, expr)}, wd, vsb, _) ->
                    let cx_ = E_t.cx_front cx n in
                    let expr = E_levels.compute_level cx_ expr in
                    let level = E_levels.get_level expr in
                    (nm.core, Kdefinition, level)
                | Fact _ -> assert false
                | _ -> assert false
                    (* Defn ( Recursive | Instance | Bpragrama ) *)
                end in
            let (name1, kind1, level1) = get_hyp cx1 m in
            let (name2, kind2, level2) = get_hyp cx2 n in
            begin match kind1 with
            | Kconstant ->
                ((kind2 = Kconstant)
                || (kind2 = Kdefinition &&
                    level2 = 0)) &&
                if StringMap.mem name1 op_mapping then
                    (StringMap.find name1 op_mapping) = name2
                else begin
                    op_mapping <- StringMap.add name1 name2 op_mapping;
                    true end
            | Kstate ->
                ((kind2 = Kconstant)
                || (kind2 = Kstate)
                || (kind2 = Kdefinition &&
                    level2 <= 1)) &&
                if StringMap.mem name1 op_mapping then
                    (StringMap.find name1 op_mapping) = name2
                else begin
                    op_mapping <- StringMap.add name1 name2 op_mapping;
                    true end
            | Kaction ->
                ((kind2 = Kconstant)
                || (kind2 = Kstate)
                || (kind2 = Kaction)
                || (kind2 = Kdefinition &&
                    level2 <= 2)) &&
                if StringMap.mem name1 op_mapping then
                    (StringMap.find name1 op_mapping) = name2
                else begin
                    op_mapping <- StringMap.add name1 name2 op_mapping;
                    true end
            | Ktemporal ->
                ((kind2 = Kconstant)
                || (kind2 = Kstate)
                || (kind2 = Kaction)
                || (kind2 = Ktemporal)
                || (kind2 = Kdefinition &&
                    level2 <= 3)) &&
                if StringMap.mem name1 op_mapping then
                    (StringMap.find name1 op_mapping) = name2
                else begin
                    op_mapping <- StringMap.add name1 name2 op_mapping;
                    true end
            | Kunknown -> n = m
            | Kvariable ->
                name1 = name2
                && kind2 = Kvariable
            | Kdefinition ->
                name1 = name2
                && kind2 = Kdefinition
            end
        | Opaque p,
          Opaque q ->
            p = q
        | Internal b,
          Internal c ->
            b = c
        | Lambda (rs, e),
          Lambda (vs, f) ->
            let mk_param (v, shp) = Fresh (
                v, shp, Unknown, Unbounded) @@ v in
            let cx1_ext = List.map mk_param rs in
            let cx2_ext = List.map mk_param vs in
            let cx1 = Deque.append_list cx1 cx1_ext in
            let cx2 = Deque.append_list cx2 cx2_ext in
            List.length rs = List.length vs &&
                self#expr cx1 cx2 e f
        (*
        | Lambda (vs, e) ->
          let scx = self#adjs scx
              (List.map
                  (fun (v, shp) -> Fresh (v, shp, Unknown, Unbounded) @@ v)
                  vs) in
          Lambda (vs, self#expr scx e) @@ oe
        *)
        | Apply (p, es),
          Apply (q, fs) ->
            self#expr cx1 cx2 p q &&
            self#exprs cx1 cx2 es fs
        (*
        | Apply (op, es) ->
            Apply (self#expr scx op, List.map (self#expr scx) es) @@ oe
        *)
        | Sequent s,
          Sequent t ->
            self#sequent cx1 cx2 s t
        (*
        | Sequent sq ->
            let (_, sq) = self#sequent scx sq in
            Sequent sq @@ oe
        *)
        | Bang (e, ss),
          Bang (f, tt) ->
            self#expr cx1 cx2 e f &&
            List.for_all2 (self#sel cx1 cx2) ss tt
        (*
        | Bang (e, sels) ->
            Bang (self#expr scx e, List.map (self#sel scx) sels) @@ oe
        *)
        | With (e, _),
          With (f, _) ->
            self#expr cx1 cx2 e f
        (*
        | With (e, m) ->
            With (self#expr scx e, m) @@ oe
        *)
        | Let (xi, a),
          Let (phi, b) ->
            let cx1_ = self#defns_cx cx1 xi in
            let cx2_ = self#defns_cx cx2 phi in
            self#defns cx1 cx2 xi phi &&
            self#expr cx1_ cx2_ a b
        (*
        | Let (ds, e) ->
            let (scx, ds) = self#defns scx ds in
            Let (ds, self#expr scx e) @@ oe
        *)
        | If (c1, t1, e1),
          If (c2, t2, e2) ->
            self#expr cx1 cx2 c1 c2
            && self#expr cx1 cx2 t1 t2
            && self#expr cx1 cx2 e1 e2
        (*
        | If (e, f, g) ->
            If (self#expr scx e, self#expr scx f, self#expr scx g) @@ oe
        *)
        | List (q, es),
          List (r, fs) ->
            q = r
            && self#exprs cx1 cx2 es fs
        (*
        | List (q, es) ->
            List (q, List.map (self#expr scx) es) @@ oe
        *)
        | Quant (q, bs, e),
          Quant (r, cs, f) ->
            let cx1_ = self#bounds_cx cx1 bs in
            let cx2_ = self#bounds_cx cx2 bs in
            q = r
            && self#bounds cx1 cx2 bs cs
            && self#expr cx1_ cx2_ e f
        (*
        | Quant (q, bs, e) ->
            let (scx, bs) = self#bounds scx bs in
            Quant (q, bs, self#expr scx e) @@ oe
        *)
        | Tquant (q, rs, e),
          Tquant (r, vs, f) ->
            let g v = Flex v @@ v in
            let cx1_ext = List.map g rs in
            let cx2_ext = List.map g vs in
            let cx1_ = Deque.append_list cx1 cx1_ext in
            let cx2_ = Deque.append_list cx2 cx2_ext in
            q = r
            && rs = vs
            && self#expr cx1_ cx2_ e f
        (*
        | Tquant (q, vs, e) ->
            let scx = self#adjs scx (List.map (fun v -> Flex v @@ v) vs) in
            Tquant (q, vs, self#expr scx e) @@ oe
        *)
        | Choose (ve, Some edom, e),
          Choose (vf, Some fdom, f) ->
            let g v dom = Fresh (v, Shape_expr, Constant,
                                 Bounded (dom, Visible)) @@ v in
            let h1 = g ve edom in
            let h2 = g vf fdom in
            let cx1_ = Deque.snoc cx1 h1 in
            let cx2_ = Deque.snoc cx2 h2 in
            self#expr cx1 cx2 edom fdom
            && self#expr cx1_ cx2_ e f
        | Choose (ve, None, e),
          Choose (vf, None, f) ->
            let g v = Fresh (v, Shape_expr, Constant, Unbounded) @@ v in
            let h1 = g ve in
            let h2 = g vf in
            let cx1_ = Deque.snoc cx1 h1 in
            let cx2_ = Deque.snoc cx2 h2 in
            self#expr cx1_ cx2_ e f
        (*
        | Choose (v, optdom, e) ->
            let optdom = Option.map (self#expr scx) optdom in
            let h = match optdom with
              | None -> Fresh (v, Shape_expr, Constant, Unbounded) @@ v
              | Some dom -> Fresh (v, Shape_expr, Constant,
                                    Bounded (dom, Visible)) @@ v
            in
            let scx = self#adj scx h in
            let e = self#expr scx e in
            Choose (v, optdom, e) @@ oe
        *)
        | SetSt (ve, edom, e),
          SetSt (vf, fdom, f) ->
            let g v dom = Fresh (v, Shape_expr, Constant,
                            Bounded (dom, Visible)) @@ v in
            let h1 = g ve edom in
            let h2 = g vf fdom in
            let cx1_ = Deque.snoc cx1 h1 in
            let cx2_ = Deque.snoc cx2 h2 in
            self#expr cx1 cx2 edom fdom
            && self#expr cx1_ cx2_ e f
        (*
        | SetSt (v, dom, e) ->
            let dom = self#expr scx dom in
            let scx = self#adj scx
                  (Fresh (v, Shape_expr, Constant,
                          Bounded (dom, Visible)) @@ v) in
            let e = self#expr scx e in
            SetSt (v, dom, e) @@ oe
        *)
        | SetOf (e, bs),
          SetOf (f, cs) ->
            let cx1_ = self#bounds_cx cx1 bs in
            let cx2_ = self#bounds_cx cx2 cs in
            self#expr cx1_ cx2_ e f
            && self#bounds cx1 cx2 bs cs
        (*
        | SetOf (e, bs) ->
            let (scx, bs) = self#bounds scx bs in
            SetOf (self#expr scx e, bs) @@ oe
        *)
        | SetEnum es,
          SetEnum fs ->
            self#exprs cx1 cx2 es fs
        (*
        | SetEnum es ->
            SetEnum (List.map (self#expr scx) es) @@ oe
        *)
        | Arrow (a, b),
          Arrow (c, d) ->
            self#expr cx1 cx2 a c
            && self#expr cx1 cx2 b d
        (*
        | Arrow (a, b) ->
            Arrow (self#expr scx a, self#expr scx b) @@ oe
        *)
        | Fcn (bs, e),
          Fcn (cs, f) ->
            let cx1_ = self#bounds_cx cx1 bs in
            let cx2_ = self#bounds_cx cx2 cs in
            self#bounds cx1 cx2 bs cs
            && self#expr cx1_ cx2_ e f
        (*
        | Fcn (bs, e) ->
            let (scx, bs) = self#bounds scx bs in
            Fcn (bs, self#expr scx e) @@ oe
        *)
        | FcnApp (f, es),
          FcnApp (g, fs) ->
            self#exprs cx1 cx2 (f :: es) (g :: fs)
        (*
        | FcnApp (f, es) ->
            FcnApp (self#expr scx f, List.map (self#expr scx) es) @@ oe
        *)
        | Tuple es,
          Tuple fs ->
            self#exprs cx1 cx2 es fs
        (*
        | Tuple es ->
            Tuple (List.map (self#expr scx) es) @@ oe
        *)
        | Product es,
          Product fs ->
            self#exprs cx1 cx2 es fs
        (*
        | Product es ->
            Product (List.map (self#expr scx) es) @@ oe
        *)
        | Rect fs,
          Rect gs ->
            let fmap = digest fs in
            let gmap = digest gs in
              StringMap.equal (self#expr cx1 cx2) fmap gmap
        (*
        | Rect fs ->
            Rect (List.map (fun (s, e) -> (s, self#expr scx e)) fs) @@ oe
        *)
        | Record fs,
          Record gs ->
            let fmap = digest fs in
            let gmap = digest gs in
              StringMap.equal (self#expr cx1 cx2) fmap gmap
        (*
        | Record fs ->
            Record (List.map (fun (s, e) -> (s, self#expr scx e)) fs) @@ oe
        *)
        | Except (e, xs),
          Except (f, ys) ->
            let rec exspecs cx1 cx2 xs ys = match xs, ys with
              | [], [] -> true
              | x :: xs, y :: ys ->
                  exspec cx1 cx2 x y
                  && exspecs cx1 cx2 xs ys
              | _ -> false
            and exspec cx1 cx2 (tr, e) (ur, f) =
              trail cx1 cx2 tr ur
              && self#expr cx1 cx2 e f
            and trail cx1 cx2 tr ur = match tr, ur with
              | [], [] -> true
              | Except_dot x :: tr, Except_dot y :: ur ->
                  x = y
                  && trail cx1 cx2 tr ur
              | Except_apply e :: tr, Except_apply f :: ur ->
                  self#expr cx1 cx2 e f
                  && trail cx1 cx2 tr ur
              | _ -> false
            in
              self#expr cx1 cx2 e f
              && exspecs cx1 cx2 xs ys
        (*
        | Except (e, xs) ->
            Except (self#expr scx e, List.map (self#exspec scx) xs) @@ oe
        *)
        | Dot (e, x),
          Dot (f, y) ->
            self#expr cx1 cx2 e f
            && x = y
        (*
        | Dot (e, f) ->
            Dot (self#expr scx e, f) @@ oe
        *)
        | Sub (m, e, f),
          Sub (n, g, h) ->
            m = n
            && self#expr cx1 cx2 e g
            && self#expr cx1 cx2 f h
        (*
        | Sub (s, e, f) ->
            Sub (s, self#expr scx e, self#expr scx f) @@ oe
        *)
        | Tsub (m, e, f),
          Tsub (n, g, h) ->
            m = n
            && self#expr cx1 cx2 e g
            && self#expr cx1 cx2 f h
        (*
        | Tsub (s, e, f) ->
            Tsub (s, self#expr scx e, self#expr scx f) @@ oe
        *)
        | Fair (m, e, f),
          Fair (n, g, h) ->
            m = n
            && self#expr cx1 cx2 e g
            && self#expr cx1 cx2 f h
        (*
        | Fair (fop, e, f) ->
            Fair (fop, self#expr scx e, self#expr scx f) @@ oe
        *)
        | Case (is, o), Case (js, p) ->
            let arms cx1 cx2 is js = match is, js with
              | [], [] -> true
              | (e, f) :: is, (g, h) :: js ->
                  self#expr cx1 cx2 e g
                  && self#expr cx1 cx2 f h
              | _ -> false
            in
              arms cx1 cx2 is js
              && self#opt_expr cx1 cx2 o p
        (*
        | Case (arms, oth) ->
            Case (List.map (fun (e, f) -> (self#expr scx e, self#expr scx f)) arms,
                  Option.map (self#expr scx) oth) @@ oe
        *)
        | String x,
          String y -> x = y
        | Num (i, j),
          Num (k, l) ->
            i = k
            && j = l
        | At b,
          At c -> b = c
        | _, _ -> false

    method exprs cx1 cx2 es fs = match es, fs with
      | [], [] -> true
      | e :: es, f :: fs ->
          self#expr cx1 cx2 e f
          && self#exprs cx1 cx2 es fs
      | _ -> false

    method bounds_cx cx bs =
        let f (v, k, _) = Fresh (v, Shape_expr, k, Unbounded) @@ v in
        let hs = List.map f bs in
        let cx_ = Deque.append_list cx hs in
        cx_
    (*
    method bounds scx bs =
      let bs = List.map begin
        fun (v, k, dom) -> match dom with
          | Domain d -> (v, k, Domain (self#expr scx d))
          | _ -> (v, k, dom)
      end bs in
      let hs = List.map begin
        fun (v, k, _) -> Fresh (v, Shape_expr, k, Unbounded) @@ v
      end bs in
      let scx = self#adjs scx hs in
      (scx, bs)

    method bound scx b =
      match self#bounds scx [b] with
        | (scx, [b]) -> (scx, b)
        | _ -> assert false
    *)

    method bounds cx1 cx2 bs cs = match bs, cs with
      | [], [] -> true
      | b :: bs, c :: cs ->
          self#bound cx1 cx2 b c
          && self#bounds cx1 cx2 bs cs
      | _ -> false

    method bound cx1 cx2 (_, j, jd) (_, k, kd) =
    j = k
    && self#bdom cx1 cx2 jd kd

    method bdom cx1 cx2 d e = match d, e with
      | No_domain, No_domain -> true
      | Domain d, Domain e -> self#expr cx1 cx2 d e
      | Ditto, Ditto -> true
      | _ -> false

    method opt_expr cx1 cx2 eo fo = match eo, fo with
      | None, None -> true
      | Some e, Some f -> self#expr cx1 cx2 e f
      | _ -> false

    (*
    method defns scx = function
      | [] -> (scx, [])
      | df :: dfs ->
          let df = self#defn scx df in
          let scx = self#adj scx (Defn (df, User, Visible, Local) @@ df) in
          let (scx, dfs) = self#defns scx dfs in
          (scx, df :: dfs)
    *)

    method defns_cx cx ds = (* TODO *)
        match ds with
        | [] -> cx
        | df :: dfs ->
            (* TODO: Hidden ? if called after visible definitions
            have been expanded.
            *)
            let hyp = Defn (df, User, Visible, Local) @@ df in
            let cx = Deque.snoc cx hyp in
            let cx = self#defns_cx cx dfs in
            cx

    method defns cx1 cx2 ds es = match ds, es with
      | [], [] -> true
      | d :: ds, e :: es ->
          self#defn cx1 cx2 d e
          && self#defns cx1 cx2 ds es
      | _ -> false

    method defn cx1 cx2 d e = match d.core, e.core with
      | Operator (_, e), Operator (_, f) ->
          self#expr cx1 cx2 e f
      | Instance (_, i), Instance (_, j) ->
          self#instance cx1 cx2 i j
      | Bpragma (_, e, _), Bpragma (_, f, _) ->
          self#expr cx1 cx2 e f
      | _ -> false

    (*
    method defn scx df =
      let df = match df.core with
        | Recursive (nm, shp) -> df
        | Operator (nm, e) ->
            { df with core = Operator (nm, self#expr scx e) }
        | Instance (nm, i) ->
            { df with core = Instance (nm, self#instance scx i) }
        | Bpragma(nm,e,l) ->
            { df with core = Bpragma (nm, self#expr scx e, l) }
      in
      df
    *)

    method sequent cx1 cx2 s t =
        let cx1_ = self#hyps_cx cx1 s.context in
        let cx2_ = self#hyps_cx cx2 t.context in
        self#context cx1 cx2 s.context t.context
        && self#expr cx1_ cx2_ s.active t.active
    (*
    method sequent scx sq =
      let (scx, hyps) = self#hyps scx sq.context in
      (scx, { context = hyps ; active = self#expr scx sq.active })
    *)

    method context cx1 cx2 cx dx =
        match Deque.front cx, Deque.front dx with
        | None, None -> true
        | Some (h, cx), Some (g, dx) ->
            let cx1_ = self#hyp_cx cx1 h in
            let cx2_ = self#hyp_cx cx2 g in
            self#hyp cx1 cx2 h g
            && self#context cx1_ cx2_ cx dx
        | _ -> false

    method hyps_cx cx hyps =
        match Deque.front hyps with
        | None -> cx
        | Some (h, hs) ->
            let cx = Deque.snoc cx h in
            let cx = self#hyps_cx cx hs in
            cx

    (*
    method hyps scx hs = match Dq.front hs with
      | None -> (scx, Dq.empty)
      | Some (h, hs) ->
          let (scx, h) = self#hyp scx h in
          let (scx, hs) = self#hyps scx hs in
          (scx, Dq.cons h hs)
    *)

    method hyp cx1 cx2 h g = match h.core, g.core with
      | Fresh (_, hsh, l, b), Fresh (_, gsh, m, c) ->
          l = m
          && hsh = gsh
          && begin
            match b, c with
              | Unbounded, Unbounded -> true
              | Bounded (b, _), Bounded (c, _) -> self#expr cx1 cx2 b c
              | _ -> false
          end
      | Flex _, Flex _ -> true
      | Defn (d, _, _, dx), Defn (e, _, _, ex) ->
          self#defn cx1 cx2 d e
          && dx = ex
      | Fact (e, _, _), Fact (f, _, _) ->
          self#expr cx1 cx2 e f
      | _ -> false

    method hyp_cx cx h =
        Deque.snoc cx h

    (*
    method hyp scx h = match h.core with
      | Fresh (nm, shp, lc, dom) ->
          let dom = match dom with
            | Unbounded -> Unbounded
            | Bounded (r, rvis) -> Bounded (self#expr scx r, rvis)
          in
          let h = Fresh (nm, shp, lc, dom) @@ h in
          (self#adj scx h, h)
      | Flex s ->
          let h = Flex s @@ h in
          (self#adj scx h, h)
      | Defn (df, wd, vis, ex) ->
          let df = self#defn scx df in
          let h = Defn (df, wd, vis, ex) @@ h in
          (self#adj scx h, h)
      | Fact (e, vis, tm) ->
          let h = Fact (self#expr scx e, vis, tm) @@ h in
          (self#adj scx h, h)
    *)

    method instance cx1 cx2 i j =
        let f cx v = Deque.snoc cx (
            Fresh (v, Shape_expr, Unknown, Unbounded) @@ v) in
        let cx1_ = List.fold_left f cx1 i.inst_args in
        let cx2_ = List.fold_left f cx2 j.inst_args in
        i.inst_args = j.inst_args
        && i.inst_mod = j.inst_mod
        && self#sub cx1_ cx2_ i.inst_sub j.inst_sub

    (*
    method instance scx i =
      let scx = List.fold_left begin
        fun scx v ->
          self#adj scx (Fresh (v, Shape_expr, Unknown, Unbounded) @@ v)
      end scx i.inst_args in
      { i with inst_sub = List.map
        (fun (v, e) -> (v, self#expr scx e))
        i.inst_sub }
    *)

    method sub cx1 cx2 ss tt =
      let umap = digestv ss in
      let tmap = digestv tt in
        StringMap.equal (self#expr cx1 cx2) umap tmap

    method sel cx1 cx2 s t = match s, t with
        | Sel_down, Sel_down -> true
        | Sel_num n, Sel_num m -> n = m
        | Sel_left, Sel_left
        | Sel_right, Sel_right
        | Sel_at, Sel_at -> true
        | Sel_inst es, Sel_inst fs ->
            self#exprs cx1 cx2 es fs
        | Sel_lab (s, es), Sel_lab (t, fs) ->
            s = t
            && self#exprs cx1 cx2 es fs
        | _ -> false
    (*
    method sel scx sel = match sel with
      | Sel_inst args ->
          Sel_inst (List.map (self#expr scx) args)
      | Sel_lab (l, args) ->
          Sel_lab (l, List.map (self#expr scx) args)
      | _ -> sel
      *)
end


(*
method pform scx pf = pf

method exspec scx (trail, res) =
  let do_trail = function
    | Except_dot s -> Except_dot s
    | Except_apply e -> Except_apply (self#expr scx e)
  in
  (List.map do_trail trail, self#expr scx res)
*)


let check_level_change cx expr =
    let expr = E_levels.compute_level cx expr in
    let found = ref false in
    let check_context checker hyps =
        (* f cx_hyps hyp *)
        let visitor = object (self: 'self)
            inherit [unit] E_visit.iter_visible_hyp

            method hyp (((), cx2) as scx) h =
                begin match h.core with
                    | Fact (expr, Visible, _) ->
                        begin match expr.core with
                        | Sequent sq ->
                            let hyps = sq.context in
                            let active = sq.active in
                            let visitor = object (self: 'self)
                                inherit [unit] E_visit.iter_visible_hyp
                            end in
                            let (_, cx_goal) = visitor#hyps ((), cx2) hyps in
                            found := !found || (checker cx_goal active)
                        | _ ->
                            found := !found || (checker cx2 expr)
                        end
                    | _ -> ()
                end;
                E_visit.adj scx h
        end in
        let (_, cx3) = visitor#hyps ((), cx) hyps in
        ignore cx3
        (*
        print_string (E_fmt.string_of_expr cx3 a);
        print_string (E_fmt.string_of_expr cx3 b);
        *)
        in
    match expr.core with
    | Sequent sq -> begin
        let hyps = sq.context in
        let active = sq.active in
        let visitor = object (self: 'self)
            inherit [unit] E_visit.iter_visible_hyp
        end in
        let (_, cx_goal) = visitor#hyps ((), cx) hyps in
        let visitor = new level_comparison in
        let f cx_hyps hyp = visitor#compare cx_hyps cx_goal hyp active in
        check_context f hyps;
        let proved = !found in
        begin if proved then begin
            if !Params.verbose then
            Util.printf ~at:expr ~prefix:"[INFO]" "%s"
                ("Proved level comparison\n")
            end
        else
            failwith "LevelComparison proof directive did not succeed.\n" end;
        let core = (if proved then Internal TRUE else expr.core) in
        let active = noprops core in
        let sq = {sq with active=active} in
        noprops (Sequent sq)
        end
    | _ -> assert false
