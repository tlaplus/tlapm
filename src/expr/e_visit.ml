(*
 * expr/visit.ml --- default visitor for expressions
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

(** default visitors *)

Revision.f "$Rev$";;

open Ext
open Property

open E_t

module Dq = Deque

let hyp_rename v h = begin match h.core with
  | Fresh (_, shp, k, dom) ->
      Fresh (v, shp, k, dom)
  | Flex _ ->
      Flex v
  | Defn (df, wd, vis, ex) ->
      Defn ({ df with core = match df.core with
                | Recursive (_, shp) -> Recursive (v, shp)
                | Operator (_, e) -> Operator (v, e)
                | Instance (_, i) -> Instance (v, i)
                | Bpragma (_, e, l) -> Bpragma (v, e, l)},
            wd, vis, ex)
  | Fact (e, vis, tm) ->
      Fact (e, vis, tm)
end @@ h

type 's scx = 's * hyp Deque.dq

let adj (s, cx) h =
  (s, Dq.snoc cx h)

let rec adjs scx = function
  | [] -> scx
  | h :: hs ->
      adjs (adj scx h) hs

class virtual ['s] map = object (self : 'self)

  method expr (scx : 's scx) oe = match oe.core with
    | Ix n ->
        Ix n @@ oe
    | Internal b ->
        Internal b @@ oe
    | Opaque o ->
        Opaque o @@ oe
    | Bang (e, sels) ->
        Bang (self#expr scx e, List.map (self#sel scx) sels) @@ oe
    | Lambda (vs, e) ->
        let scx = adjs scx (List.map (fun (v, shp) -> Fresh (v, shp, Unknown, Unbounded) @@ v) vs) in
        Lambda (vs, self#expr scx e) @@ oe
    | String s ->
        String s @@ oe
    | Num (m, n) ->
        Num (m, n) @@ oe
    | Apply (op, es) ->
        Apply (self#expr scx op, List.map (self#expr scx) es) @@ oe
    | Sequent sq ->
        let (_, sq) = self#sequent scx sq in
        Sequent sq @@ oe
    | With (e, m) ->
        With (self#expr scx e, m) @@ oe
    | Let (ds, e) ->
        let (scx, ds) = self#defns scx ds in
        Let (ds, self#expr scx e) @@ oe
    | If (e, f, g) ->
        If (self#expr scx e, self#expr scx f, self#expr scx g) @@ oe
    | List (q, es) ->
        List (q, List.map (self#expr scx) es) @@ oe
    | Quant (q, bs, e) ->
        let (scx, bs) = self#bounds scx bs in
        Quant (q, bs, self#expr scx e) @@ oe
    | Tquant (q, vs, e) ->
        let scx = adjs scx (List.map (fun v -> Flex v @@ v) vs) in
        Tquant (q, vs, self#expr scx e) @@ oe
    | Choose (v, optdom, e) ->
        let optdom = Option.map (self#expr scx) optdom in
        let h = match optdom with
          | None -> Fresh (v, Shape_expr, Constant, Unbounded) @@ v
          | Some dom -> Fresh (v, Shape_expr, Constant, Bounded (dom, Visible)) @@ v
        in
        let scx = adj scx h in
        let e = self#expr scx e in
        Choose (v, optdom, e) @@ oe
    | SetSt (v, dom, e) ->
        let dom = self#expr scx dom in
        let scx = adj scx (Fresh (v, Shape_expr, Constant, Bounded (dom, Visible)) @@ v) in
        let e = self#expr scx e in
        SetSt (v, dom, e) @@ oe
    | SetOf (e, bs) ->
        let (scx, bs) = self#bounds scx bs in
        SetOf (self#expr scx e, bs) @@ oe
    | SetEnum es ->
        SetEnum (List.map (self#expr scx) es) @@ oe
    | Fcn (bs, e) ->
        let (scx, bs) = self#bounds scx bs in
        Fcn (bs, self#expr scx e) @@ oe
    | FcnApp (f, es) ->
        FcnApp (self#expr scx f, List.map (self#expr scx) es) @@ oe
    | Arrow (a, b) ->
        Arrow (self#expr scx a, self#expr scx b) @@ oe
    | Product es ->
        Product (List.map (self#expr scx) es) @@ oe
    | Tuple es ->
        Tuple (List.map (self#expr scx) es) @@ oe
    | Rect fs ->
        Rect (List.map (fun (s, e) -> (s, self#expr scx e)) fs) @@ oe
    | Record fs ->
        Record (List.map (fun (s, e) -> (s, self#expr scx e)) fs) @@ oe
    | Except (e, xs) ->
        Except (self#expr scx e, List.map (self#exspec scx) xs) @@ oe
    | Dot (e, f) ->
        Dot (self#expr scx e, f) @@ oe
    | Sub (s, e, f) ->
        Sub (s, self#expr scx e, self#expr scx f) @@ oe
    | Tsub (s, e, f) ->
        Tsub (s, self#expr scx e, self#expr scx f) @@ oe
    | Fair (fop, e, f) ->
        Fair (fop, self#expr scx e, self#expr scx f) @@ oe
    | Case (arms, oth) ->
        Case (List.map (fun (e, f) -> (self#expr scx e, self#expr scx f)) arms,
              Option.map (self#expr scx) oth) @@ oe
    | At b ->
        At b @@ oe
    | Parens (e, pf) ->
        Parens (self#expr scx e, self#pform scx pf) @@ oe

  method pform scx pf = pf

  method sel scx sel = match sel with
    | Sel_inst args ->
        Sel_inst (List.map (self#expr scx) args)
    | Sel_lab (l, args) ->
        Sel_lab (l, List.map (self#expr scx) args)
    | _ -> sel

  method sequent scx sq =
    let (scx, hyps) = self#hyps scx sq.context in
    (scx, { context = hyps ; active = self#expr scx sq.active })

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

  method defns scx = function
    | [] -> (scx, [])
    | df :: dfs ->
        let df = self#defn scx df in
        let scx = adj scx (Defn (df, User, Visible, Local) @@ df) in
        let (scx, dfs) = self#defns scx dfs in
        (scx, df :: dfs)

  method bounds scx bs =
    let bs = List.map begin
      fun (v, k, dom) -> match dom with
        | Domain d -> (v, k, Domain (self#expr scx d))
        | _ -> (v, k, dom)
    end bs in
    let hs = List.map begin
      fun (v, k, _) -> Fresh (v, Shape_expr, k, Unbounded) @@ v
    end bs in
    let scx = adjs scx hs in
    (scx, bs)

  method bound scx b =
    match self#bounds scx [b] with
      | (scx, [b]) -> (scx, b)
      | _ -> assert false

  method exspec scx (trail, res) =
    let do_trail = function
      | Except_dot s -> Except_dot s
      | Except_apply e -> Except_apply (self#expr scx e)
    in
    (List.map do_trail trail, self#expr scx res)

  method instance scx i =
    let scx = List.fold_left begin
      fun scx v ->
        adj scx (Fresh (v, Shape_expr, Unknown, Unbounded) @@ v)
    end scx i.inst_args in
    { i with inst_sub = List.map (fun (v, e) -> (v, self#expr scx e)) i.inst_sub }

  method hyp scx h = match h.core with
    | Fresh (nm, shp, lc, dom) ->
        let dom = match dom with
          | Unbounded -> Unbounded
          | Bounded (r, rvis) -> Bounded (self#expr scx r, rvis)
        in
        let h = Fresh (nm, shp, lc, dom) @@ h in
        (adj scx h, h)
    | Flex s ->
        let h = Flex s @@ h in
        (adj scx h, h)
    | Defn (df, wd, vis, ex) ->
        let df = self#defn scx df in
        let h = Defn (df, wd, vis, ex) @@ h in
        (adj scx h, h)
    | Fact (e, vis, tm) ->
        let h = Fact (self#expr scx e, vis, tm) @@ h in
        (adj scx h, h)

  method hyps scx hs = match Dq.front hs with
    | None -> (scx, Dq.empty)
    | Some (h, hs) ->
        let (scx, h) = self#hyp scx h in
        let (scx, hs) = self#hyps scx hs in
        (scx, Dq.cons h hs)

end

class virtual ['s] iter = object (self : 'self)

  method expr (scx : 's scx) oe = match oe.core with
    | ( Ix _
      | Internal _
      | Opaque _
      | String _
      | Num _
      | At _
      ) -> ()
    | Bang (e, sels) ->
        self#expr scx e ;
        List.iter (self#sel scx) sels
    | Lambda (vs, e) ->
        let scx = adjs scx (List.map (fun (v, shp) -> Fresh (v, shp, Unknown, Unbounded) @@ v) vs) in
        self#expr scx e
    | Apply (op, es) ->
        self#expr scx op ;
        List.iter (self#expr scx) es
    | Sequent sq ->
        ignore (self#sequent scx sq)
    | With (e, m) ->
        self#expr scx e
    | Let (ds, e) ->
        let scx = self#defns scx ds in
        self#expr scx e
    | If (a, b, c) ->
        self#expr scx a ;
        self#expr scx b ;
        self#expr scx c
    | List (q, es) ->
        List.iter (self#expr scx) es
    | Quant (q, bs, e) ->
        let scx = self#bounds scx bs in
        self#expr scx e
    | Tquant (q, vs, e) ->
        let scx = adjs scx (List.map (fun v -> Flex v @@ v) vs) in
        self#expr scx e
    | Choose (v, optdom, e) ->
        let h = match optdom with
          | None -> Fresh (v, Shape_expr, Constant, Unbounded) @@ v
          | Some dom ->
              self#expr scx dom ;
              Fresh (v, Shape_expr, Constant, Bounded (dom, Visible)) @@ v
        in
        let scx = adj scx h in
        self#expr scx e
    | SetSt (v, dom, e) ->
        self#expr scx dom ;
        let scx = adj scx (Fresh (v, Shape_expr, Constant, Bounded (dom, Visible)) @@ v) in
        self#expr scx e
    | SetOf (e, bs) ->
        let scx = self#bounds scx bs in
        self#expr scx e
    | SetEnum es ->
        List.iter (self#expr scx) es
    | Fcn (bs, e) ->
        let scx = self#bounds scx bs in
        self#expr scx e
    | FcnApp (f, es) ->
        List.iter (self#expr scx) (f :: es)
    | Arrow (a, b) ->
        self#expr scx a ;
        self#expr scx b
    | ( Product es | Tuple es ) ->
        List.iter (self#expr scx) es
    | Rect fs ->
        List.iter (fun (_, e) -> self#expr scx e) fs
    | Record fs ->
        List.iter (fun (_, e) -> self#expr scx e) fs
    | Except (e, xs) ->
        self#expr scx e ;
        List.iter (self#exspec scx) xs
    | Dot (e, f) ->
        self#expr scx e
    | Sub (s, e, f) ->
        self#expr scx e ;
        self#expr scx f
    | Tsub (s, e, f) ->
        self#expr scx e ;
        self#expr scx f
    | Fair (fop, e, f) ->
        self#expr scx e ;
        self#expr scx f
    | Case (arms, oth) ->
        List.iter (fun (e, f) -> self#expr scx e ; self#expr scx f) arms ;
        ignore (Option.map (self#expr scx) oth)
    | Parens (e, pf) ->
        self#expr scx e ;
        self#pform scx pf

  method pform scx pf = ()

  method sel scx sel = match sel with
    | Sel_inst args | Sel_lab (_, args) ->
        List.iter (self#expr scx) args
    | _ -> ()

  method sequent scx sq =
    let scx = self#hyps scx sq.context in
    self#expr scx sq.active ;
    scx

  method defn scx df =
    let () = match df.core with
      | Recursive (nm, shp) -> ()
      | Operator (nm, e) ->
          self#expr scx e
      | Instance (nm, i) ->
          self#instance scx i
      | Bpragma (nm,e,l) ->
          self#expr scx e
    in
    let scx = adj scx (Defn (df, Builtin, Visible, Local) @@ df) in
    scx

  method defns scx = function
    | [] -> scx
    | d :: ds ->
        let scx = self#defn scx d in
        let scx = self#defns scx ds in
        scx

  method bounds scx bs =
    List.iter begin
      fun (v, k, dom) -> match dom with
        | Domain d -> self#expr scx d
        | _ -> ()
    end bs ;
    let hs = List.map begin
      fun (v, k, _) -> Fresh (v, Shape_expr, k, Unbounded) @@ v
    end bs in
    adjs scx hs

  method bound scx b =
    self#bounds scx [b]

  method exspec scx (trail, res) =
    let do_trail = function
      | Except_dot s -> ()
      | Except_apply e -> self#expr scx e
    in
    List.iter do_trail trail ;
    self#expr scx res

  method instance scx i =
    let scx = List.fold_left begin
      fun scx v ->
        adj scx (Fresh (v, Shape_expr, Unknown, Unbounded) @@ v)
    end scx i.inst_args in
    List.iter (fun (_, e) -> self#expr scx e) i.inst_sub

  method hyp scx h =
    begin
      match h.core with
        | Fresh (nm, _, lc, e) -> begin
            match e with
              | Bounded (dom, _) -> self#expr scx dom
              | Unbounded -> ()
          end
        | Flex s ->
            ()
        | Defn (df, _, _, _) ->
            ignore (self#defn scx df)
        | Fact (e, _, _) ->
            self#expr scx e
    end ; adj scx h

  method hyps scx hs = match Dq.front hs with
    | None -> scx
    | Some (h, hs) ->
        let scx = self#hyp scx h in
        let scx = self#hyps scx hs in
        scx

end

class virtual ['s, 'a] foldmap = object (self : 'self)

  method expr (scx : 's scx) a oe =
    match oe.core with
    | Ix n ->
        a, Ix n @@ oe
    | Internal b ->
        a, Internal b @@ oe
    | Opaque o ->
        a, Opaque o @@ oe
    | Bang (e, sels) ->
        let a, e = self#expr scx a e in
        let a, sels = List.fold_left begin fun (a, sels) sel ->
          let a, sel = self#sel scx a sel in
          a, sel :: sels
        end (a, []) sels in
        let sels = List.rev sels in
        a, Bang (e, sels) @@ oe
    | Lambda (vs, e) ->
        let scx = adjs scx (List.map begin fun (v, shp) ->
          Fresh (v, shp, Unknown, Unbounded) @@ v
        end vs) in
        let a, e = self#expr scx a e in
        a, Lambda (vs, e) @@ oe
    | String s ->
        a, String s @@ oe
    | Num (m, n) ->
        a, Num (m, n) @@ oe
    | Apply (op, es) ->
        let a, op = self#expr scx a op in
        let a, es = List.fold_left begin fun (a, es) e ->
          let a, e = self#expr scx a e in
          a, e :: es
        end (a, []) es in
        let es = List.rev es in
        a, Apply (op, es) @@ oe
    | Sequent sq ->
        let _, a, sq = self#sequent scx a sq in
        a, Sequent sq @@ oe
    | With (e, m) ->
        let a, e = self#expr scx a e in
        a, With (e, m) @@ oe
    | Let (ds, e) ->
        let scx, a, ds = self#defns scx a ds in
        let a, e = self#expr scx a e in
        a, Let (ds, e) @@ oe
    | If (e, f, g) ->
        let a, e = self#expr scx a e in
        let a, f = self#expr scx a f in
        let a, g = self#expr scx a g in
        a, If (e, f, g) @@ oe
    | List (q, es) ->
        let a, es = List.fold_left begin fun (a, es) e ->
          let a, e = self#expr scx a e in
          a, e :: es
        end (a, []) es in
        let es = List.rev es in
        a, List (q, es) @@ oe
    | Quant (q, bs, e) ->
        let scx, a, bs = self#bounds scx a bs in
        let a, e = self#expr scx a e in
        a, Quant (q, bs, e) @@ oe
    | Tquant (q, vs, e) ->
        let scx = adjs scx (List.map begin fun v ->
          Flex v @@ v
        end vs) in
        let a, e = self#expr scx a e in
        a, Tquant (q, vs, e) @@ oe
    | Choose (v, optdom, e) ->
        let a, optdom, h =
          match optdom with
          | None ->
              a, None, Fresh (v, Shape_expr, Constant, Unbounded) @@ v
          | Some dom ->
              let a, dom = self#expr scx a dom in
              a, Some dom, Fresh (v, Shape_expr, Constant, Bounded (dom, Visible)) @@ v
        in
        let scx = adj scx h in
        let a, e = self#expr scx a e in
        a, Choose (v, optdom, e) @@ oe
    | SetSt (v, dom, e) ->
        let a, dom = self#expr scx a dom in
        let scx = adj scx (Fresh (v, Shape_expr, Constant, Bounded (dom, Visible)) @@ v) in
        let a, e = self#expr scx a e in
        a, SetSt (v, dom, e) @@ oe
    | SetOf (e, bs) ->
        let scx, a, bs = self#bounds scx a bs in
        let a, e = self#expr scx a e in
        a, SetOf (e, bs) @@ oe
    | SetEnum es ->
        let a, es = List.fold_left begin fun (a, es) e ->
          let a, e = self#expr scx a e in
          a, e :: es
        end (a, []) es in
        let es = List.rev es in
        a, SetEnum es @@ oe
    | Fcn (bs, e) ->
        let scx, a, bs = self#bounds scx a bs in
        let a, e = self#expr scx a e in
        a, Fcn (bs, e) @@ oe
    | FcnApp (f, es) ->
        let a, f = self#expr scx a f in
        let a, es = List.fold_left begin fun (a, es) e ->
          let a, e = self#expr scx a e in
          a, e :: es
        end (a, []) es in
        let es = List.rev es in
        a, FcnApp (f, es) @@ oe
    | Arrow (e, f) ->
        let a, e = self#expr scx a e in
        let a, f = self#expr scx a f in
        a, Arrow (e, f) @@ oe
    | Product es ->
        let a, es = List.fold_left begin fun (a, es) e ->
          let a, e = self#expr scx a e in
          a, e :: es
        end (a, []) es in
        let es = List.rev es in
        a, Product es @@ oe
    | Tuple es ->
        let a, es = List.fold_left begin fun (a, es) e ->
          let a, e = self#expr scx a e in
          a, e :: es
        end (a, []) es in
        let es = List.rev es in
        a, Tuple es @@ oe
    | Rect fs ->
        let a, fs = List.fold_left begin fun (a, fs) (s, e) ->
          let a, e = self#expr scx a e in
          a, (s, e) :: fs
        end (a, []) fs in
        let fs = List.rev fs in
        a, Rect fs @@ oe
    | Record fs ->
        let a, fs = List.fold_left begin fun (a, fs) (s, e) ->
          let a, e = self#expr scx a e in
          a, (s, e) :: fs
        end (a, []) fs in
        let fs = List.rev fs in
        a, Record fs @@ oe
    | Except (e, xs) ->
        let a, e = self#expr scx a e in
        let a, xs = List.fold_left begin fun (a, xs) x ->
          let a, x = self#exspec scx a x in
          a, x :: xs
        end (a, []) xs in
        let xs = List.rev xs in
        a, Except (e, xs) @@ oe
    | Dot (e, f) ->
        let a, e = self#expr scx a e in
        a, Dot (e, f) @@ oe
    | Sub (s, e, f) ->
        let a, e = self#expr scx a e in
        let a, f = self#expr scx a f in
        a, Sub (s, e, f) @@ oe
    | Tsub (s, e, f) ->
        let a, e = self#expr scx a e in
        let a, f = self#expr scx a f in
        a, Tsub (s, e, f) @@ oe
    | Fair (fop, e, f) ->
        let a, e = self#expr scx a e in
        let a, f = self#expr scx a f in
        a, Fair (fop, e, f) @@ oe
    | Case (arms, oth) ->
        let a, arms = List.fold_left begin fun (a, arms) (e, f) ->
          let a, e = self#expr scx a e in
          let a, f = self#expr scx a f in
          a, (e, f) :: arms
        end (a, []) arms in
        let arms = List.rev arms in
        let a, oth =
          match oth with
          | None ->
              a, None
          | Some o ->
              let a, o = self#expr scx a o in
              a, Some o
        in
        a, Case (arms, oth) @@ oe
    | At b ->
        a, At b @@ oe
    | Parens (e, pf) ->
        let a, e = self#expr scx a e in
        let a, pf = self#pform scx a pf in
        a, Parens (e, pf) @@ oe

  method pform scx a pf = a, pf

  method sel scx a sel =
    match sel with
    | Sel_inst args ->
        let a, e = List.fold_left begin fun (a, args) e ->
          let a, e = self#expr scx a e in
          a, e :: args
        end (a, []) args in
        let args = List.rev args in
        a, Sel_inst args
    | Sel_lab (l, args) ->
        let a, e = List.fold_left begin fun (a, args) e ->
          let a, e = self#expr scx a e in
          a, e :: args
        end (a, []) args in
        let args = List.rev args in
        a, Sel_lab (l, args)
    | _ ->
        a, sel

  method sequent scx a sq =
    let scx, a, hyps = self#hyps scx a sq.context in
    let a, act = self#expr scx a sq.active in
    scx, a, { context = hyps ; active = act }

  method defn scx a df =
    match df.core with
      | Recursive (nm, shp) ->
          a, Recursive (nm, shp) @@ df
      | Operator (nm, e) ->
          let a, e = self#expr scx a e in
          a, Operator (nm, e) @@ df
      | Instance (nm, i) ->
          let a, i = self#instance scx a i in
          a, Instance (nm, i) @@ df
      | Bpragma(nm, e, l) ->
          let a, e = self#expr scx a e in
          a, Bpragma (nm, e, l) @@ df

  method defns scx a ds =
    match ds with
    | [] -> scx, a, []
    | df :: dfs ->
        let a, df = self#defn scx a df in
        let scx = adj scx (Defn (df, User, Visible, Local) @@ df) in
        let scx, a, dfs = self#defns scx a dfs in
        scx, a, df :: dfs

  method bounds scx a bs =
    let a, bs = List.fold_left begin fun (a, bs) (v, k, dom) ->
      match dom with
      | Domain d ->
          let a, d = self#expr scx a d in
          a, (v, k, Domain d) :: bs
      | _ ->
          a, (v, k, dom) :: bs
    end (a, []) bs in
    let bs = List.rev bs in
    let hs = List.map begin
      fun (v, k, _) -> Fresh (v, Shape_expr, k, Unbounded) @@ v
    end bs in
    let scx = adjs scx hs in
    scx, a, bs

  method bound scx (a : 'a) b =
    match self#bounds scx a [b] with
      | scx, a, [b] -> scx, a, b
      | _ -> assert false

  method exspec scx a (trail, res) =
    let a, trail = List.fold_left begin fun (a, trail) x ->
      match x with
      | Except_dot s ->
          a, (Except_dot s) :: trail
      | Except_apply e ->
          let a, e = self#expr scx a e in
          a, (Except_apply e) :: trail
    end (a, []) trail in
    let trail = List.rev trail in
    let a, res = self#expr scx a res in
    a, (trail, res)

  method instance scx a i =
    let scx = List.fold_left begin fun scx v ->
      adj scx (Fresh (v, Shape_expr, Unknown, Unbounded) @@ v)
    end scx i.inst_args in
    let a, sub = List.fold_left begin fun (a, sub) (v, e) ->
      let a, e = self#expr scx a e in
      a, (v, e) :: sub
    end (a, []) i.inst_sub in
    let sub = List.rev sub in
    a, { i with inst_sub = sub }

  method hyp scx a h =
    match h.core with
    | Fresh (nm, shp, lc, dom) ->
        let a, dom =
          match dom with
          | Unbounded ->
              a, Unbounded
          | Bounded (r, rvis) ->
              let a, r = self#expr scx a r in
              a, Bounded (r, rvis)
        in
        let h = Fresh (nm, shp, lc, dom) @@ h in
        let scx = adj scx h in
        scx, a, h
    | Flex s ->
        let h = Flex s @@ h in
        let scx = adj scx h in
        scx, a, h
    | Defn (df, wd, vis, ex) ->
        let a, df = self#defn scx a df in
        let h = Defn (df, wd, vis, ex) @@ h in
        let scx = adj scx h in
        scx, a, h
    | Fact (e, vis, tm) ->
        let a, e = self#expr scx a e in
        let h = Fact (e, vis, tm) @@ h in
        let scx = adj scx h in
        scx, a, h

  method hyps scx a hs =
    match Dq.front hs with
    | None -> scx, a, Dq.empty
    | Some (h, hs) ->
        let scx, a, h = self#hyp scx a h in
        let scx, a, hs = self#hyps scx a hs in
        scx, a, Dq.cons h hs

end
