(* Visitor for expressions.

Copyright (C) 2008-2010  INRIA and Microsoft Corporation
*)
open Ext
open Property

open E_t
open E_t.From_hint

module Dq = Deque


let hyp_rename v h = begin
    match h.core with
    | Fresh (_, shp, k, dom) ->
        Fresh (v, shp, k, dom)
    | FreshTuply _ -> assert false  (* renaming
        is undefined for this case *)
    | Flex _ ->
        Flex v
    | Defn (df, wd, vis, ex) ->
        let core = match df.core with
            | Recursive (_, shp) -> Recursive (v, shp)
            | Operator (_, e) -> Operator (v, e)
            | Instance (_, i) -> Instance (v, i)
            | Bpragma (_, e, l) -> Bpragma (v, e, l) in
        Defn ({df with core}, wd, vis, ex)
    | Fact (e, vis, tm) ->
        Fact (e, vis, tm)
    end @@ h


let hyp_of_bound_full
        ((name, kind, dom): bound):
            hyp =
    (* Return declaration for single bound.

    There are 3 cases of domain:
    - domain present ->
        bounded hypothesis with
        visible domain bound
    - no domain ->
        unbounded hypothesis
    - ditto ->
        raise error

    Related functions:
    - `hyps_of_bounds_full`
    - `hyps_of_bounds_unditto`
    *)
    match dom with
    | Domain d ->
        make_bounded_fresh name d
    | No_domain ->
        make_fresh name kind
    | Ditto -> Errors.bug "\
        E_visit.hyp_of_bound_full: \
        Ditto not expected"


let hyps_of_bounds
        (bs: bounds): hyp list =
    (* Return declarations made from bounds.

    These declarations introduce nullary operators.
    The signatures of these operators are represented
    using the constructor `Shape_expr`.

    WARNING: This function is incorrect,
    because domain-bounds are ignored,
    and instead `Unbounded` is used.
    This function is called only from
    code that worked in this way
    before the refactoring.

    Related function:
        `hyps_of_bounds_as_arity_0`
    *)
    let f (name, kind, dom) =
        make_fresh name kind in
    List.map f bs


let hyps_of_bounds_full
        (bs: bounds): hyp list =
    (* Map bounds to hypotheses.

    Domain-bounds are copied to hypotheses.
    Bounds are **not** shifted,
    so the resulting list of hypotheses
    cannot be inserted directly into
    a context.

    Use the function `hyps_of_bounds_unditto`
    to remove dittos, and shift bounds.

    Dittos raise an exception.

    Read also the function `hyp_of_bound_full`.
    *)
    List.map hyp_of_bound_full bs


let shifter n d =
    E_subst.app_expr (E_subst.shift n) d


let hyps_of_bounds_unditto
        (bs: bounds): hyp list =
    (* Return hypotheses from bounds.

    The hypotheses are created by
    repeating all dittos (for domain
    bounds), and shifting any
    De Bruijn indices that appear
    in expressions of domain bounds.

    Related function:
        `Expr.T.unditto`
    *)
    let bs = unditto bs in
    let mapper n (v, k, dom) =
        match dom with
        | Domain d ->
            let d = shifter n d in
            let bound = (
                v, k, Domain d) in
            hyp_of_bound_full bound
        | No_domain ->
            let bound = (v, k, dom) in
            hyp_of_bound_full bound
        | Ditto -> assert false
        in
    List.mapi mapper bs


let hyps_of_bounds_as_arity_0
    (* Return declarations made from bounds.

    These declarations introduce nullary operators.
    The signatures of these operators are represented
    as `Shape_op 0`, using the constructor `Shape_op`.
    This is the only difference of this function
    from the function `hyps_of_bounds`.

    WARNING: This function is incorrect,
    because domain-bounds are ignored,
    and instead `Unbounded` is used.
    This function is called only from
    code that worked in this way
    before the refactoring.
    *)
        (bs: bounds): hyp list =
    let make_fresh (id, kind, dom) =
        let name = id in
        let fresh = Fresh (
            name, Shape_op 0,
            kind, Unbounded) in
        fresh @@ name in
    List.map make_fresh bs


let hyp_of_tuply_bound
        (names: Util.hints)
        (dom: bound_domain):
            hyp =
    match dom with
    | Domain d ->
        make_bounded_tuply_fresh names d
    | No_domain ->
        make_tuply_fresh names
    | Ditto -> Errors.bug "\
        E_visit.hyp_of_tuply_bound: \
        Ditto not expected"


let hyps_of_tuply_bounds_unditto
        (bs: tuply_bounds): hyp list =
    let bs = unditto_tuply bs in
    let mapper n (v, dom) =
        let dom =
            match dom with
            | Domain d ->
                let d = shifter n d in
                Domain d
            | No_domain -> dom
            | Ditto -> assert false in
        match v with
        | Bound_name name ->
            hyp_of_bound_full (
                name, Constant, dom)
        | Bound_names names ->
            hyp_of_tuply_bound names dom
        in
    List.mapi mapper bs


let map_bound_domains
        (mapper: expr -> expr)
        (bs: bounds):
            bounds =
    let step (v, k, dom) =
        match dom with
        | Domain d ->
            let d = mapper d in
            (v, k, Domain d)
        | _ -> (v, k, dom)
        in
    List.map step bs


let map_bounds
        (name_mapper: Util.hint -> Util.hint)
        (domain_mapper: expr -> expr)
        (bs: bounds):
            bounds =
    let mapper (v, k, dom) =
        let v = name_mapper v in
        match dom with
        | Domain d ->
            let d =
                domain_mapper d in
            (v, k, Domain d)
        | _ -> (v, k, dom)
        in
    List.map mapper bs


let rename_bound
        (b: bound)
        (new_name: Util.hint):
            bound =
    let (name, k, dom) = b in
    (new_name, k, dom)


let rename_bounds
        (bs: bounds)
        (new_names: Util.hints):
            bounds =
    List.map2 rename_bound
        bs new_names


type 's scx = 's * hyp Deque.dq

let empty s = (s, Dq.empty)

let adj (s, cx) h =
  (s, Dq.snoc cx h)

let rec adjs scx = function
  | [] -> scx
  | h :: hs ->
      adjs (adj scx h) hs


let adj_unboundeds_unchecked scx bounds =
    (* Declare `bounds` in context of `scx`.

    WARNING: The declarations added to the
    context do **not** have domain-bounds.
    This function does **not** check whether
    any domain-bounds are present in `bounds`
    (hence the "unchecked" in
    the function's name).
    *)
    let step scx (name, kind, dom) =
        let fresh = make_fresh name kind in
        adj scx fresh in
    List.fold_left step scx bounds


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
        let scx = self#adjs scx
            (List.map
                (fun (v, shp) -> Fresh (v, shp, Unknown, Unbounded) @@ v)
                vs) in
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
        let scx = self#adjs scx (List.map (fun v -> Flex v @@ v) vs) in
        Tquant (q, vs, self#expr scx e) @@ oe
    | Choose (v, optdom, e) ->
        let optdom = Option.map (self#expr scx) optdom in
        let h = match optdom with
          | None -> make_fresh v Constant
          | Some dom -> make_bounded_fresh v dom
        in
        let scx = self#adj scx h in
        let e = self#expr scx e in
        Choose (v, optdom, e) @@ oe
    | SetSt (v, dom, e) ->
        let dom = self#expr scx dom in
        let fresh = make_bounded_fresh v dom in
        let scx = self#adj scx fresh in
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
    | QuantTuply _
    | ChooseTuply _
    | SetStTuply _
    | SetOfTuply _
    | FcnTuply _ ->
        failwith "use instead the class \
            `E_visit.map_concrete`"

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
        let scx = self#adj scx (Defn (df, User, Visible, Local) @@ df) in
        let (scx, dfs) = self#defns scx dfs in
        (scx, df :: dfs)

  method bounds scx bs =
    let bs = List.map begin
      fun (v, k, dom) -> match dom with
        | Domain d -> (v, k, Domain (self#expr scx d))
        | _ -> (v, k, dom)
    end bs in
    let hs = hyps_of_bounds bs in
    let scx = self#adjs scx hs in
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
        let fresh = make_fresh v Unknown in
        self#adj scx fresh
    end scx i.inst_args in
    { i with inst_sub = List.map (fun (v, e) -> (v, self#expr scx e)) i.inst_sub }

  method hyp scx h = match h.core with
    | Fresh (nm, shp, lc, dom) ->
        let dom = match dom with
          | Unbounded -> Unbounded
          | Bounded (r, rvis) -> Bounded (self#expr scx r, rvis)
        in
        let h = Fresh (nm, shp, lc, dom) @@ h in
        (self#adj scx h, h)
    | FreshTuply (names, dom) ->
        failwith "use instead the class \
            `E_visit.map_concrete`"
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

  method hyps scx hs = match Dq.front hs with
    | None -> (scx, Dq.empty)
    | Some (h, hs) ->
        let (scx, h) = self#hyp scx h in
        let (scx, hs) = self#hyps scx hs in
        (scx, Dq.cons h hs)

  method adj (s, cx) h =
    (s, Dq.snoc cx h)

  method adjs scx = function
    | [] -> scx
    | h :: hs ->
        self#adjs (self#adj scx h) hs

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
        let scx = adjs scx (List.map (fun (v, shp) ->
            Fresh (v, shp, Unknown, Unbounded) @@ v) vs) in
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
    | List (_, es) ->
        List.iter (self#expr scx) es
    | Quant (_, bs, e) ->
        let scx = self#bounds scx bs in
        self#expr scx e
    | Tquant (_, vs, e) ->
        let scx = adjs scx (List.map (fun v -> Flex v @@ v) vs) in
        self#expr scx e
    | Choose (v, optdom, e) ->
        let h = match optdom with
          | None -> make_fresh v Constant
          | Some dom ->
              self#expr scx dom;
              make_bounded_fresh v dom
        in
        let scx = adj scx h in
        self#expr scx e
    | SetSt (v, dom, e) ->
        self#expr scx dom;
        let fresh = make_bounded_fresh v dom in
        let scx = adj scx fresh in
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
    | QuantTuply _
    | ChooseTuply _
    | SetStTuply _
    | SetOfTuply _
    | FcnTuply _ ->
        failwith "use instead the class\
            `E_visit.iter_concrete`"

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
    let hs = hyps_of_bounds bs in
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
        let fresh = make_fresh v Unknown in
        adj scx fresh
    end scx i.inst_args in
    List.iter (fun (_, e) -> self#expr scx e) i.inst_sub

  method hyp scx h =
    begin
      match h.core with
        | Fresh (_, _, _, Bounded (dom, _)) ->
            self#expr scx dom
        | Fresh (_, _, _, Unbounded)
        | Flex _ ->
            ()
        | Defn (df, _, _, _) ->
            ignore (self#defn scx df)
        | Fact (e, _, _) ->
            self#expr scx e
        | FreshTuply _ ->
            failwith "use instead the class\
                `E_visit.iter_concrete`"
    end ; adj scx h

  method hyps scx hs = match Dq.front hs with
    | None -> scx
    | Some (h, hs) ->
        let scx = self#hyp scx h in
        let scx = self#hyps scx hs in
        scx

end


class virtual ['s] map_concrete =
    (* Mapping of a concrete syntax tree.

    Code related to use of `FreshTuply`
    from the context is untested,
    but implemented for completeness.
    *)
    object (self: 'self)
    inherit ['s] map as super

    method expr scx oe =
        match oe.core with
        | QuantTuply (qfr, bs, pred) ->
            let (scx, bs) = self#tuply_bounds scx bs in
            let pred = self#expr scx pred in
            QuantTuply (qfr, bs, pred) @@ oe
        | ChooseTuply (names, optdom, pred) ->
            let optdom = Option.map
                (self#expr scx) optdom in
            let h = match optdom with
                | None -> make_tuply_fresh names
                | Some dom ->
                    make_bounded_tuply_fresh
                        names dom in
            let scx = self#adj scx h in
            let pred = self#expr scx pred in
            ChooseTuply (names, optdom, pred) @@ oe
        | SetStTuply (names, dom, pred) ->
            let dom = self#expr scx dom in
            let fresh = make_bounded_tuply_fresh
                names dom in
            let scx = self#adj scx fresh in
            let pred = self#expr scx pred in
            SetStTuply (names, dom, pred) @@ oe
        | SetOfTuply (elem, bs) ->
            let (scx, bs) = self#tuply_bounds scx bs in
            let elem = self#expr scx elem in
            SetOfTuply (elem, bs) @@ oe
        | FcnTuply (bs, value) ->
            let (scx, bs) = self#tuply_bounds scx bs in
            let value = self#expr scx value in
            FcnTuply (bs, value) @@ oe
        | _ -> super#expr scx oe

    method tuply_bounds scx bs =
        let bs = List.map (self#tuply_bound scx) bs in
        let hs = hyps_of_tuply_bounds_unditto bs in
        let scx = self#adjs scx hs in
        (scx, bs)

    method tuply_bound scx (tuply_name, dom) =
        let dom = match dom with
            | Domain d ->
                let d = self#expr scx d in
                Domain d
            | _ -> dom in
        (tuply_name, dom)

    method hyp scx h =
        match h.core with
        | FreshTuply (names, dom) ->
            let dom = match dom with
                | Unbounded -> Unbounded
                | Bounded (r, rvis) ->
                    Bounded (self#expr scx r, rvis) in
            let h = FreshTuply (names, dom) @@ h in
            (self#adj scx h, h)
        | _ -> super#hyp scx h
end


class virtual ['s] iter_concrete =
    (* Iteration over a concrete syntax tree.

    Code related to use of `FreshTuply`
    from the context is untested,
    but implemented for completeness.
    *)
    object (self: 'self)
    inherit ['s] iter as super

    method expr scx oe =
        match oe.core with
        | QuantTuply (_, bs, pred) ->
            let scx = self#tuply_bounds scx bs in
            self#expr scx pred
        | ChooseTuply (names, optdom, pred) ->
            let h = match optdom with
              | None -> make_tuply_fresh names
              | Some dom ->
                  self#expr scx dom;
                  make_bounded_tuply_fresh
                    names dom in
            let scx = adj scx h in
            self#expr scx pred
        | SetStTuply (names, dom, pred) ->
            self#expr scx dom;
            let fresh = make_bounded_tuply_fresh
                names dom in
            let scx = adj scx fresh in
            self#expr scx pred
        | SetOfTuply (elem, bs) ->
            let scx = self#tuply_bounds scx bs in
            self#expr scx elem
        | FcnTuply (bs, value) ->
            let scx = self#tuply_bounds scx bs in
            self#expr scx value
        | _ -> super#expr scx oe

    method tuply_bounds scx bs =
        List.iter (self#tuply_bound scx) bs;
        let hs = hyps_of_tuply_bounds_unditto bs in
        adjs scx hs

    method tuply_bound scx (_, dom) =
        match dom with
        | Domain d -> self#expr scx d
        | _ -> ()

    method hyp scx h =
        match h.core with
        | FreshTuply (_, Bounded (dom, _)) ->
            self#expr scx dom;
            adj scx h
        | _ -> super#hyp scx h
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
    | QuantTuply (_, _, _)
    | ChooseTuply (_, _, _)
    | SetStTuply (_, _, _)
    | SetOfTuply (_, _)
    | FcnTuply (_, _) -> assert false

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
    | FreshTuply (names, dom) ->
        let a, dom =
            match dom with
            | Unbounded ->
                a, Unbounded
            | Bounded (r, rvis) ->
                let a, r = self#expr scx a r in
                a, Bounded (r, rvis)
            in
        let h = FreshTuply (names, dom) @@ h in
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

class virtual ['s, 'a] fold = object (self : 'self)

  method expr (scx : 's scx) a oe =
    match oe.core with
    | Ix _
    | Internal _
    | Opaque _ -> a
    | Bang (e, sels) ->
        let a = self#expr scx a e in
        List.fold_left (self#sel scx) a sels
    | Lambda (vs, e) ->
        let scx = adjs scx (List.map begin fun (v, shp) ->
          Fresh (v, shp, Unknown, Unbounded) @@ v
        end vs) in
        self#expr scx a e
    | Apply (op, es) ->
        List.fold_left (self#expr scx) a (op :: es)
    | Sequent sq ->
        snd (self#sequent scx a sq)
    | With (e, _) ->
        self#expr scx a e
    | Let (ds, e) ->
        let scx, a = self#defns scx a ds in
        self#expr scx a e
    | If (e, f, g) ->
        let a = self#expr scx a e in
        let a = self#expr scx a f in
        self#expr scx a g
    | List (_, es) ->
        List.fold_left (self#expr scx) a es
    | Quant (_, bs, e) ->
        let scx, a = self#bounds scx a bs in
        self#expr scx a e
    | Tquant (_, vs, e) ->
        let scx = adjs scx (List.map begin fun v ->
          Flex v @@ v
        end vs) in
        self#expr scx a e
    | Choose (v, optdom, e) ->
        let a, h =
          match optdom with
          | None ->
              a, Fresh (v, Shape_expr, Constant, Unbounded) @@ v
          | Some dom ->
              let a = self#expr scx a dom in
              a, Fresh (v, Shape_expr, Constant, Bounded (dom, Visible)) @@ v
        in
        let scx = adj scx h in
        self#expr scx a e
    | SetSt (v, dom, e) ->
        let a = self#expr scx a dom in
        let scx = adj scx (Fresh (v, Shape_expr, Constant, Bounded (dom, Visible)) @@ v) in
        self#expr scx a e
    | SetOf (e, bs) ->
        let scx, a = self#bounds scx a bs in
        self#expr scx a e
    | SetEnum es ->
        List.fold_left (self#expr scx) a es
    | Fcn (bs, e) ->
        let scx, a = self#bounds scx a bs in
        self#expr scx a e
    | FcnApp (f, es) ->
        List.fold_left (self#expr scx) a (f :: es)
    | Arrow (e, f) ->
        let a = self#expr scx a e in
        self#expr scx a f
    | Product es
    | Tuple es ->
        List.fold_left (self#expr scx) a es
    | Rect fs
    | Record fs ->
        List.fold_left (fun a (_, e) -> self#expr scx a e) a fs
    | Except (e, xs) ->
        let a = self#expr scx a e in
        List.fold_left (self#exspec scx) a xs
    | Dot (e, _) ->
        self#expr scx a e
    | Sub (_, e, f)
    | Tsub (_, e, f)
    | Fair (_, e, f) ->
        let a = self#expr scx a e in
        self#expr scx a f
    | Case (arms, oth) ->
        let a = List.fold_left begin fun a (e, f) ->
          let a = self#expr scx a e in
          self#expr scx a f
        end a arms in
        begin match oth with
        | None -> a
        | Some o -> self#expr scx a o
        end
    | Parens (e, pf) ->
        let a = self#expr scx a e in
        self#pform scx a pf
    | String _
    | Num _
    | At _ -> a
    | QuantTuply (_, _, _)
    | ChooseTuply (_, _, _)
    | SetStTuply (_, _, _)
    | SetOfTuply (_, _)
    | FcnTuply (_, _) -> assert false

  method pform scx a pf = a

  method sel scx a sel =
    match sel with
    | Sel_inst args
    | Sel_lab (_, args) -> List.fold_left (self#expr scx) a args
    | _ -> a

  method sequent scx a sq =
    let scx, a = self#hyps scx a sq.context in
    let a = self#expr scx a sq.active in
    scx, a

  method defn scx a df =
    match df.core with
      | Recursive _ -> a
      | Operator (_, e)
      | Bpragma(_, e, _) -> self#expr scx a e
      | Instance (_, i) -> self#instance scx a i

  method defns scx a ds =
    match ds with
    | [] -> scx, a
    | df :: dfs ->
        let a = self#defn scx a df in
        let scx = adj scx (Defn (df, User, Visible, Local) @@ df) in
        self#defns scx a dfs

  method bounds scx a bs =
    let a = List.fold_left begin fun a (v, k, dom) ->
      match dom with
      | Domain d -> self#expr scx a d
      | _ -> a
    end a bs in
    let hs = List.map begin
      fun (v, k, _) -> Fresh (v, Shape_expr, k, Unbounded) @@ v
    end bs in
    let scx = adjs scx hs in
    scx, a

  method bound scx (a : 'a) b =
    self#bounds scx a [b]

  method exspec scx a (trail, res) =
    let a = List.fold_left begin fun a x ->
      match x with
      | Except_dot s -> a
      | Except_apply e -> self#expr scx a e
    end a trail in
    self#expr scx a res

  method instance scx a i =
    let scx = List.fold_left begin fun scx v ->
      adj scx (Fresh (v, Shape_expr, Unknown, Unbounded) @@ v)
    end scx i.inst_args in
    List.fold_left (fun a (_, e) -> self#expr scx a e) a i.inst_sub

  method hyp scx a h =
    match h.core with
    | Fresh (nm, shp, lc, dom) ->
        let a =
          match dom with
          | Unbounded -> a
          | Bounded (r, rvis) -> self#expr scx a r
        in
        let h = Fresh (nm, shp, lc, dom) @@ h in
        let scx = adj scx h in
        scx, a
    | Flex s ->
        let h = Flex s @@ h in
        let scx = adj scx h in
        scx, a
    | Defn (df, wd, vis, ex) ->
        let a = self#defn scx a df in
        let h = Defn (df, wd, vis, ex) @@ h in
        let scx = adj scx h in
        scx, a
    | Fact (e, vis, tm) ->
        let a = self#expr scx a e in
        let h = Fact (e, vis, tm) @@ h in
        let scx = adj scx h in
        scx, a
    | FreshTuply (names, dom) ->
        let a =
            match dom with
            | Unbounded -> a
            | Bounded (r, rvis) -> self#expr scx a r
            in
        let h = FreshTuply (names, dom) @@ h in
        let scx = adj scx h in
        scx, a

  method hyps scx a hs =
    match Dq.front hs with
    | None -> scx, a
    | Some (h, hs) ->
        let scx, a = self#hyp scx a h in
        self#hyps scx a hs

end


class virtual ['s] map_visible_hyp = object (self : 'self)
    (* Map expressions, visiting only visible hypotheses. *)
    inherit ['s] map as super

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
      | Defn (_, _, Hidden, _)
      | Fact (_, Hidden, _) ->
        (* TODO: what about mutable properties of `h` ? *)
        (adj scx h, h)
      | Defn (df, wd, Visible, ex) ->
          let h = Defn (self#defn scx df, wd, Visible, ex) @@ h in
          (adj scx h, h)
      | Fact (e, Visible, tm) ->
          let h = Fact (self#expr scx e, Visible, tm) @@ h in
          (adj scx h, h)
      | FreshTuply _ ->
          failwith "use instead the class \
              `E_visit.map_concrete`"
end

class virtual ['s] iter_visible_hyp = object (self : 'self)
    (* Iterate on expressions, visiting only visible hypotheses. *)
    inherit ['s] iter as super

    method hyp scx h =
      begin
        match h.core with
          | Fresh (_, _, _, Bounded (dom, _)) ->
              self#expr scx dom
          | Fresh (_, _, _, Unbounded)
          | Flex _ ->
              ()
          | Defn (_, _, Hidden, _)
          | Fact (_, Hidden, _) ->
              ()
          | Defn (df, _, Visible, _) ->
              ignore (self#defn scx df)
          | Fact (e, Visible, _) ->
              self#expr scx e
          | FreshTuply _ ->
              failwith "use instead the class \
                  `E_visit.iter_concrete`"
      end ; adj scx h
end

class virtual ['s, 'a] foldmap_visible_hyp = object (self : 'self)
    (* Foldmap expressions, visiting only visible hypotheses. *)
    inherit ['s, 'a] foldmap as super

    method hyp scx a h = match h.core with
      | Fresh (nm, shp, lc, dom) ->
          let a, dom = match dom with
            | Unbounded -> a, Unbounded
            | Bounded (r, rvis) ->
                let a, e = self#expr scx a r in
                a, Bounded (e, rvis)
          in
          let h = Fresh (nm, shp, lc, dom) @@ h in
          (adj scx h, a, h)
      | Flex s ->
          let h = Flex s @@ h in
          (adj scx h, a, h)
      | Defn (_, _, Hidden, _)
      | Fact (_, Hidden, _) ->
        (* TODO: what about mutable properties of `h` ? *)
        (adj scx h, a, h)
      | Defn (df, wd, Visible, ex) ->
          let a, df = self#defn scx a df in
          let h = Defn (df, wd, Visible, ex) @@ h in
          (adj scx h, a, h)
      | Fact (e, Visible, tm) ->
          let a, e = self#expr scx a e in
          let h = Fact (e, Visible, tm) @@ h in
          (adj scx h, a, h)
      | FreshTuply (names, dom) ->
          let a, dom =
              match dom with
              | Unbounded ->
                  a, Unbounded
              | Bounded (r, rvis) ->
                  let a, r = self#expr scx a r in
                  a, Bounded (r, rvis)
              in
          let h = FreshTuply (names, dom) @@ h in
          let scx = adj scx h in
          scx, a, h
end

class virtual ['s, 'a] fold_visible_hyp = object (self : 'self)
    (* Fold expressions, visiting only visible hypotheses. *)
    inherit ['s, 'a] fold as super

    method hyp scx a h = match h.core with
      | Fresh (nm, shp, lc, dom) ->
          let a = match dom with
            | Unbounded -> a
            | Bounded (r, rvis) -> self#expr scx a r
          in
          let h = Fresh (nm, shp, lc, dom) @@ h in
          (adj scx h, a)
      | Flex s ->
          let h = Flex s @@ h in
          (adj scx h, a)
      | Defn (_, _, Hidden, _)
      | Fact (_, Hidden, _) ->
        (* TODO: what about mutable properties of `h` ? *)
        (adj scx h, a)
      | Defn (df, wd, Visible, ex) ->
          let a = self#defn scx a df in
          let h = Defn (df, wd, Visible, ex) @@ h in
          (adj scx h, a)
      | Fact (e, Visible, tm) ->
          let a = self#expr scx a e in
          let h = Fact (e, Visible, tm) @@ h in
          (adj scx h, a)
      | FreshTuply (names, dom) ->
          let a =
              match dom with
              | Unbounded -> a
              | Bounded (r, rvis) -> self#expr scx a r
              in
          let h = FreshTuply (names, dom) @@ h in
          let scx = adj scx h in
          scx, a
end


let set_to_list table =
        (* `Hashtbl` keys to `List`. *)
    let seq = Hashtbl.to_seq_keys table in
    Stdlib.List.of_seq seq


let collect_unprimed_vars cx e =
    let unprimed_vars = Hashtbl.create 16 in
    let visitor =
        object (self: 'self)
        inherit [bool] iter_visible_hyp as super

        method expr (((prime_scope: bool), cx) as scx) e =
            match e.core with
            | Apply ({core=Internal Prime}, _) ->
                assert (not prime_scope)
            | Ix n ->
                assert (n >= 1);
                assert (not prime_scope);
                let hyp = E_t.get_val_from_id cx n in
                begin match hyp.core with
                    | Flex name ->
                        let var_name = name.core in
                        Hashtbl.replace unprimed_vars var_name ()
                    | _ -> ()
                end
            | Apply ({core=Internal ENABLED}, _) ->
                if (not prime_scope) then
                    self#expr scx e
            | Apply ({core=Internal Cdot}, [arg1; _]) ->
                assert (not prime_scope);
                self#expr scx arg1
            | Apply ({core=Internal UNCHANGED}, [arg]) ->
                assert (not prime_scope);
                self#expr scx arg
            | Sub (_, action, subscript) ->
                assert (not prime_scope);
                self#expr scx action;
                self#expr scx subscript
            | _ -> super#expr scx e
    end
    in
    let prime_scope = false in
    let scx = (prime_scope, cx) in
    visitor#expr scx e;
    set_to_list unprimed_vars


let collect_primed_vars cx e =
    let primed_vars = Hashtbl.create 16 in
    let visitor =
        object (self: 'self)
        inherit [bool] iter_visible_hyp as super

        method expr (((prime_scope: bool), cx) as scx) e =
            match e.core with
            | Apply ({core=Internal Prime}, [arg]) ->
                assert (not prime_scope);
                self#expr (true, cx) arg
            | Ix n ->
                begin
                assert (n >= 1);
                let hyp = E_t.get_val_from_id cx n in
                match hyp.core with
                    | Flex name ->
                        let var_name = name.core in
                        if (prime_scope &&
                                not (Hashtbl.mem primed_vars var_name)) then
                            Hashtbl.add primed_vars var_name ()
                    | _ -> ()
                end
            | Apply ({core=Internal ENABLED}, _) ->
                assert (not prime_scope)
            | Apply ({core=Internal Cdot}, [_; arg2]) ->
                assert (not prime_scope);
                self#expr scx arg2
            | Apply ({core=Internal UNCHANGED}, [arg]) ->
                assert (not prime_scope);
                let prime_scope_ = true in
                let scx_ = (prime_scope_, cx) in
                self#expr scx_ arg
            | Sub (_, action, subscript) ->
                assert (not prime_scope);
                self#expr scx action;
                let prime_scope_ = true in
                let scx_ = (prime_scope_, cx) in
                self#expr scx_ subscript
            | _ -> super#expr scx e
    end
    in
    let prime_scope = false in
    let scx = (prime_scope, cx) in
    visitor#expr scx e;
    set_to_list primed_vars


class virtual ['s] map_rename = object (self : 'self)
  (* Rename hypotheses. The renaming of identifiers is implemented in the
  method `rename`.
  *)
  inherit ['s] map as super

  method expr (scx : 's scx) oe =
    let cx = snd scx in
    match oe.core with
    | Lambda (signature, e) ->
        let hyps = (List.map
            (fun (v, shp) -> Fresh (v, shp, Unknown, Unbounded) @@ v)
            signature) in
        let names = List.map (fun (v, _) -> v) signature in
        let (hyps, names) = self#renames cx hyps names in
        let signature = List.map2
            (fun (_, shp) name -> (name, shp))
            signature names in
        let scx = self#adjs scx hyps in
        Lambda (signature, self#expr scx e) @@ oe
    | Tquant (q, names, e) ->
        let hyps = List.map (fun v -> Flex v @@ v) names in
        let (hyps, names) = self#renames cx hyps names in
        let scx = self#adjs scx hyps in
        Tquant (q, names, self#expr scx e) @@ oe
    | Choose (v, optdom, e) ->
        let optdom = Option.map (self#expr scx) optdom in
        let h = match optdom with
          | None -> make_fresh v Constant
          | Some dom -> make_bounded_fresh v dom
        in
        let (h, v) = self#rename cx h v in
        let scx = self#adj scx h in
        let e = self#expr scx e in
        Choose (v, optdom, e) @@ oe
    | SetSt (v, dom, e) ->
        let dom = self#expr scx dom in
        let hyp = make_bounded_fresh v dom in
        let (hyp, v) = self#rename cx hyp v in
        let scx = self#adj scx hyp in
        let e = self#expr scx e in
        SetSt (v, dom, e) @@ oe
    | QuantTuply _
    | ChooseTuply _
    | SetStTuply _
    | SetOfTuply _
    | FcnTuply _ ->
        assert false
    | _ -> super#expr scx oe

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
        let hyp = Defn (df, User, Visible, Local) @@ df in
        let (hyp, _) = self#rename (snd scx) hyp (noprops "") in
        let df = match hyp.core with
            | Defn (df, _, _, _) -> df
            | _ -> assert false in
        let scx = self#adj scx hyp in
        let (scx, dfs) = self#defns scx dfs in
        (scx, df :: dfs)

  method bounds scx bs =
    let cx = snd scx in
    let bs = List.map begin
      fun (v, k, dom) -> match dom with
        | Domain d -> (v, k, Domain (self#expr scx d))
        | _ -> (v, k, dom)
    end bs in
    let hs = hyps_of_bounds bs in
    let names = names_of_bounds bs in
    let (hs, names) = self#renames cx hs names in
    let bs = rename_bounds bs names in
    let scx = self#adjs scx hs in
    (scx, bs)

  method instance scx i =
    assert false  (* `INSTANCE` statements assumed to have been expanded *)
    (* TODO: call `self#rename` *)
    (*
    let scx = List.fold_left begin
      fun scx v ->
        let fresh = make_fresh v Unknown in
        self#adj scx fresh
    end scx i.inst_args in
    { i with inst_sub = List.map (fun (v, e) -> (v, self#expr scx e)) i.inst_sub }
    *)

  method hyp scx h =
    let cx = snd scx in
    match h.core with
    | Fresh (nm, shp, lc, dom) ->
        let dom = match dom with
          | Unbounded -> Unbounded
          | Bounded (r, rvis) -> Bounded (self#expr scx r, rvis)
        in
        let h = Fresh (nm, shp, lc, dom) @@ h in
        let (h, _) = self#rename cx h nm in
        (self#adj scx h, h)
    | FreshTuply _ ->
        assert false
    | Flex s ->
        let h = Flex s @@ h in
        let (h, _) = self#rename cx h s in
        (self#adj scx h, h)
    | Defn (df, wd, vis, ex) ->
            (* call `self#defns` to ensure calling `self#rename` *)
        let (_, dfs) = self#defns scx [df] in
        assert ((List.length dfs) = 1);
        let df = List.hd dfs in
        let h = Defn (df, wd, vis, ex) @@ h in
        (self#adj scx h, h)
    | Fact (e, vis, tm) ->
        let h = Fact (self#expr scx e, vis, tm) @@ h in
        (self#adj scx h, h)

  method renames cx hyps names =
    List.split (List.map2 (self#rename cx) hyps names)

  method rename cx hyp name = (hyp, name)

end


class virtual ['s] opnamer =
    (* Convert De Bruijn indices to named.

    This class is placed in `E_visit`
    to be near the root of the
    module-dependency graph.
    *)
    object (self: 'self)
    inherit ['s] map as super

    method expr (scx: 's scx) oe =
        let cx = snd scx in
        match oe.core with
        | Ix n ->
            let name = name_of_ix n cx in
            make_opaque name
        | _ -> super#expr scx oe
end


let name_operators cx expr =
    (* Convert De Bruijn indices to named.

    Replaces occurrences of
    `Ix` with `Opaque`.
    *)
    let visitor = object
        inherit [unit] opnamer
        end in
    let scx = ((), cx) in
    visitor#expr scx expr
