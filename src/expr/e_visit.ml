(*
 * expr/visit.ml --- default visitor for expressions
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

(** default visitors *)

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
          | None -> Fresh (v, Shape_expr, Constant, Unbounded) @@ v
          | Some dom -> Fresh (v, Shape_expr, Constant, Bounded (dom, Visible)) @@ v
        in
        let scx = self#adj scx h in
        let e = self#expr scx e in
        Choose (v, optdom, e) @@ oe
    | SetSt (v, dom, e) ->
        let dom = self#expr scx dom in
        let scx = self#adj scx (Fresh (v, Shape_expr, Constant, Bounded (dom, Visible)) @@ v) in
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
        let scx = self#adj scx (Defn (df, User, Visible, Local) @@ df) in
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
        self#adj scx (Fresh (v, Shape_expr, Unknown, Unbounded) @@ v)
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
end

class virtual ['s] iter_visible_hyp = object (self : 'self)
    (* Iterate on expressions, visiting only visible hypotheses. *)
    inherit ['s] iter as super

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
          | Defn (_, _, Hidden, _)
          | Fact (_, Hidden, _) ->
              ()
          | Defn (df, _, Visible, _) ->
              ignore (self#defn scx df)
          | Fact (e, Visible, _) ->
              self#expr scx e
      end ; adj scx h
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
          | None -> Fresh (v, Shape_expr, Constant, Unbounded) @@ v
          | Some dom -> Fresh (v, Shape_expr, Constant, Bounded (dom, Visible)) @@ v
        in
        let (h, v) = self#rename cx h v in
        let scx = self#adj scx h in
        let e = self#expr scx e in
        Choose (v, optdom, e) @@ oe
    | SetSt (v, dom, e) ->
        let dom = self#expr scx dom in
        let hyp = Fresh (v, Shape_expr, Constant, Bounded (dom, Visible)) @@ v in
        let (hyp, v) = self#rename cx hyp v in
        let scx = self#adj scx hyp in
        let e = self#expr scx e in
        SetSt (v, dom, e) @@ oe
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
    let hs = List.map begin
      fun (v, k, _) -> Fresh (v, Shape_expr, k, Unbounded) @@ v
    end bs in
    let names = List.map (fun (v, _, _) -> v) bs in
    let (hs, names) = self#renames cx hs names in
    let bs = List.map2 (fun (v, k, dom) name -> (name, k, dom))
        bs names in
    let scx = self#adjs scx hs in
    (scx, bs)

  method instance scx i =
    assert false  (* `INSTANCE` statements assumed to have been expanded *)
    (* TODO: call `self#rename` *)
    (*
    let scx = List.fold_left begin
      fun scx v ->
        self#adj scx (Fresh (v, Shape_expr, Unknown, Unbounded) @@ v)
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


let hyps_of_bounds bounds =
    let make_fresh (name, kind, dom) =
        Fresh (
                name, Shape_expr,
                kind, Unbounded)
            @@ name in
    List.map make_fresh bounds


let arity_of_shape shape =
    match shape with
    | Shape_expr -> 0
    | Shape_op arity ->
        assert (arity > 0);
        arity


let format_parameter (name, shape) =
    let arity = shape
        |> arity_of_shape
        |> string_of_int in
    ("{" ^
        "\"Name\": \"" ^ name.core ^
            "\", " ^
        "\"Arity\": " ^ arity ^
    "}")


let format_modal_op modal_op =
    match modal_op with
    | Box -> "[]"
    | Dia -> "<>"


class virtual ['s] json_map =
    object (self: 'self)

    method expr (scx: 's scx) oe =
        match oe.core with
        | Ix n ->
            (* Ix n @@ oe *)
            let cx = snd scx in
            let hyp = E_t.get_val_from_id cx n in
            let opaque = begin match hyp.core with
                | Flex name -> name.core
                | Fresh (name, _, _, _) -> name.core
                | Defn (defn, _, _, _) ->
                    begin match defn.core with
                    | Recursive (name, _)
                    | Operator (name, _)
                    | Instance (name, _)
                    | Bpragma (name, _, _) ->
                        name.core
                    end
                | Fact (expr, _, _) ->
                    assert false
                end in
            "{\"OpRef\": \"" ^ opaque ^ "\"}"
        | Internal Conj ->
            "{\"OpRef\": \"/\\\\\"}"
        | Internal Disj ->
            "{\"OpRef\": \"\\\\/\"}"
        | Internal builtin ->
            (* Internal b @@ oe *)
            let form = Optable.standard_form builtin in
            let opname = form.name in
            "{\"OpRef\": \"" ^ opname ^ "\"}"
        | Opaque name ->
            "{\"OpRef\": \"" ^ name ^ "\"}"
        | Bang (expr, sels) ->
            let expr = self#expr scx expr in
            let sels = List.map (self#sel scx) sels in
            let sels = Fmtutil.comma sels in
            ("{\"!\": {" ^
                "\"Expr\": " ^ expr ^
                    ", " ^
                "\"Selectors\": [" ^ sels ^
            "]}}")
        | Lambda (names, expr) ->
            let scx = self#adjs scx
                (List.map
                    (fun (v, shp) ->
                        Fresh (
                            v, shp, Unknown,
                            Unbounded) @@ v)
                    names) in
            let expr = self#expr scx expr in
            let names = names
                |> List.map format_parameter
                |> Fmtutil.comma in
            ("{\"Lambda\": " ^
                "\"Parameters\": [" ^ names ^
                    "], " ^
                "\"Expr\": " ^ expr ^
            "}}")
        | String value ->
            "{\"String\": \"" ^ value ^ "\"}"
        | Num (m, n) ->
            "{\"Number\": [\"" ^ m ^ "\", \"" ^ n ^ "\"]}"
        | Apply (op, exprs) ->
            let operator = self#expr scx op in
            let args = exprs
                |> List.map (self#expr scx)
                |> Fmtutil.comma
                in
            ("{\"Apply\": {" ^
                "\"Operator\": " ^ operator ^
                    ", " ^
                "\"Operands\": [" ^ args ^
            "]}}")
        | Sequent sq ->
            let sq = self#sequent scx sq in
            "{\"Sequent\": " ^ sq ^ "}"
        | With (expr, meth) ->
            let expr = self#expr scx expr in
            (* TODO: convert `meth` to string *)
            "{\"WithMethod\": " ^ expr ^ "}"
        | Let (defs, expr) ->
            let (scx, defs) = self#defns scx defs in
            let expr = self#expr scx expr in
            ("{\"LET\": {" ^
                "\"Definitions\": " ^ defs ^
                    ", " ^
                "\"Expr\": " ^ expr ^
            "}}")
        | If (e, f, g) ->
            let if_ = self#expr scx e in
            let then_ = self#expr scx f in
            let else_ = self#expr scx g in
            ("{\"IF\": {" ^
                "\"If\": " ^ if_ ^
                    ", " ^
                "\"THEN\": " ^ then_ ^
                    ", " ^
                "\"ELSE\": " ^ else_ ^
            "}}")
        | List (op, exprs) ->
            let operator = match op with
                | And -> "And"
                | Or -> "Or"
                | Refs -> "Refs" in
            let exprs = List.map (self#expr scx) exprs in
            let exprs = Fmtutil.comma exprs in
            ("{\"Junction\": {" ^
                "\"Operator\": \"" ^ operator ^
                    "\", " ^
                "\"Expressions\": [" ^ exprs ^
            "]}}")
        | Quant (qtf, bounds, expr) ->
            let (scx, bounds) = self#bounds scx bounds in
            let expr = self#expr scx expr in
            let quantifier = match qtf with
                | Forall -> "\\A"
                | Exists -> "\\E" in
            ("{\"" ^ quantifier ^ "\": {" ^
                "\"Bounds\": " ^ bounds ^
                    ", " ^
                "\"Expr\": " ^ expr ^
            "}}")
        | Tquant (qtf, vars, expr) ->
            let mapper v = Flex v @@ v in
            let hyps = List.map mapper vars in
            let scx = self#adjs scx hyps in
            let expr = self#expr scx expr in
            let vars = List.map
                (fun nm -> nm.core) vars in
            let vars = Fmtutil.comma vars in
            let quantifier = match qtf with
                | Forall -> "\\AA"
                | Exists -> "\\EE" in
            ("{\"" ^ quantifier ^ "\": {" ^
                "\"Variables\": " ^ vars ^
                    ", " ^
                "\"Expr\": " ^ expr ^
            "}}")
        | Choose (name, optdom, expr) ->
            let optdom = Option.map
                (self#expr scx) optdom in
            (* no need for the domain to be
            in the context *)
            let hyp = Fresh (
                name, Shape_expr,
                Constant, Unbounded) @@ name in
            let dom = match optdom with
                | None -> ""
                | Some dom -> dom in
            let scx = self#adj scx hyp in
            let expr = self#expr scx expr in
            ("{\"CHOOSE\": {" ^
                "\"Name\": " ^ name.core ^
                    ", " ^
                "\"Domain\": " ^ dom ^
                    ", " ^
                "\"Expr\": " ^ expr ^
            "}}")
        | SetSt (name, dom, expr) ->
            let dom = self#expr scx dom in
            (* no need for the domain to be
            in the context *)
            let fresh = Fresh (
                name, Shape_expr,
                Constant, Unbounded) @@ name in
            let scx = self#adj scx fresh in
            let expr = self#expr scx expr in
            ("{\"SetSt\": {" ^
                "\"Name\": \"" ^ name.core ^
                    "\", " ^
                "\"Domain\": " ^ dom ^
                    ", " ^
                "\"Expr\": " ^ expr ^
            "}}")
        | SetOf (expr, bounds) ->
            let (scx, bounds) = self#bounds scx bounds in
            let expr = self#expr scx expr in
            ("{\"SetOf\": {" ^
                "\"Bounds\": " ^ bounds ^
                    ", " ^
                "\"Expr\": " ^ expr ^
            "}}")
        | SetEnum exprs ->
            let exprs = exprs
                |> List.map (self#expr scx)
                |> Fmtutil.comma in
            "{\"SetEnum\": [" ^ exprs ^ "]}"
        | Fcn (bounds, expr) ->
            let (scx, bounds) = self#bounds scx bounds in
            let expr = self#expr scx expr in
            ("{\"Function\": {" ^
                "\"Bounds\": " ^ bounds ^
                    ", " ^
                "\"Expr\": " ^ expr ^
            "}}")
        | FcnApp (fcn, exprs) ->
            let fcn = self#expr scx fcn in
            let exprs = exprs
                |> List.map (self#expr scx)
                |> Fmtutil.comma in
            ("{\"FunctionApplication\": {" ^
                "\"Function\": " ^ fcn ^
                    ", " ^
                "\"Expressions\": [" ^ exprs ^
            "]}}")
        | Arrow (a, b) ->
            let a = self#expr scx a in
            let b = self#expr scx b in
            ("{\"->\": {" ^
                "\"Domain\": " ^ a ^
                    ", " ^
                "\"Codomain\": " ^ b ^
            "}}")
        | Product exprs ->
            let exprs = exprs
                |> List.map (self#expr scx)
                |> Fmtutil.comma in
            "{\"\\X\": [" ^ exprs ^ "]}"
        | Tuple exprs ->
            let exprs = exprs
                |> List.map (self#expr scx)
                |> Fmtutil.comma in
            "{\"<<\": [" ^ exprs ^ "]}"
        | Rect fields ->
            let mapper (s, e) = (s, self#expr scx e) in
            let fields = fields
                |> List.map mapper
                |> List.map (fun (a, b) -> a ^ b)
                |> Fmtutil.comma
                in
            "{\"SetOfRecords\": [" ^ fields ^ "]}"
        | Record fields ->
            let mapper (s, e) = (s, self#expr scx e) in
            let fields = fields
                |> List.map mapper
                |> List.map (fun (a, b) -> a ^ b)
                |> Fmtutil.comma
                in
            "{\"Record\": [" ^ fields ^ "]}"
        | Except (expr, xs) ->
            let expr = self#expr scx expr in
            let xs = xs
                |> List.map (self#exspec scx)
                |> Fmtutil.comma in
            ("{\"EXCEPT\": {" ^
                "\"Expr\": " ^ expr ^
                    ", " ^
                "\"Changes\": " ^ xs ^
            "}}")
        | Dot (expr, field) ->
            let expr = self#expr scx expr in
            ("{\"Dot\": {" ^
                "\"Expr\": " ^ expr ^
                    ", " ^
                "\"Field\": \"" ^ field ^
            "\"}}")
        | Sub (modal_op, action, subscript) ->
            let operator = format_modal_op modal_op in
            let action = self#expr scx action in
            let subscript = self#expr scx subscript in
            ("{\"Subscripted\": {" ^
                "\"Operator\": \"" ^ operator ^
                    "\", " ^
                "\"Action\": " ^ action ^
                    ", " ^
                "\"Subscript\": " ^ subscript ^
            "}}")
        | Tsub (modal_op, action, subscript) ->
            let operator = format_modal_op modal_op in
            let action = self#expr scx action in
            let subscript = self#expr scx subscript in
            ("{\"TemporalSubscripted\": {" ^
                "\"Operator\": \"" ^ operator ^
                    "\", " ^
                "\"Action\": " ^ action ^
                    ", " ^
                "\"Subscript\": " ^ subscript ^
            "}}")
        | Fair (fop, expr, subscript) ->
            let operator = match fop with
                | Weak -> "WF_"
                | Strong -> "SF_" in
            let expr = self#expr scx expr in
            let subscript = self#expr scx subscript in
            ("{\"Fairness\": {" ^
                "\"Operator\": \"" ^ operator ^
                    "\", " ^
                "\"Action\": " ^ expr ^
                    ", " ^
                "\"Subscript\": " ^ subscript ^
            "}}")
        | Case (arms, other) ->
            let mapper (e, f) = (
                self#expr scx e, self#expr scx f) in
            let arms = arms
                |> List.map mapper
                |> List.map (fun (a, b) -> a ^ b)
                |> Fmtutil.comma
                in
            let other = Option.map
                (self#expr scx) other in
            let other = match other with
                | Some other -> other
                | None -> "" in
            ("{\"CASE\": {" ^
                "\"Arms\": [" ^ arms ^
                    "], " ^
                "\"Other\": " ^ other ^
            "}}")
        | At b ->
            "\"@\""
        | Parens (expr, pf) ->
            let expr = self#expr scx expr in
            begin match pf.core with
            | Syntax ->
                "{\"(\": " ^ expr ^ "}"
            | Nlabel (name, args) ->
                let args = args
                    |> List.map (fun x -> x.core)
                    |> Fmtutil.comma
                    in
                ("{\"::\": " ^
                    "\"Expr\": " ^ expr ^
                        ", " ^
                    "\"Label\": " ^ name ^
                        ", " ^
                    "\"Args\": " ^ args ^
                "}")
            | Xlabel (name, []) ->
                ("{\"::\": " ^
                    "\"Expr\": " ^ expr ^
                    "\"Label\": " ^ name ^
                "}")
            | Xlabel _ ->
                failwith "the parser does not \
                    give this case as output"
            end

    method sel scx selector =
        match selector with
        | Sel_inst args ->
            let args = List.map
                (self#expr scx) args in
            "[" ^ Fmtutil.comma args ^ "]"
        | Sel_lab (label, args) ->
            let args = List.map
                (self#expr scx) args in
            ("{\"Label\": \"" ^
                label ^ "\", " ^
            "\"Arguments\": [" ^
                (Fmtutil.comma args) ^
            "]}")
        | _ -> failwith "unimplemented"

    method sequent scx sq =
        let (scx, hyps) = self#hyps
            scx sq.context in
        let active = self#expr
            scx sq.active in
        ("{\"Sequent\": {" ^
            "\"Hypotheses\": [" ^ hyps ^
                "], " ^
            "\"Goal\": " ^ active ^
        "}}")

    method defn scx df =
        match df.core with
        | Recursive (name, shape) ->
            ("{\"Recursive\": \"" ^
                (format_parameter (name, shape)) ^ "}")
        | Operator (name, expr) ->
            let expr = self#expr scx expr in
            ("{\"==\": {" ^
                "\"Name\": \"" ^ name.core ^
                    "\", " ^
                "\"Expr\": " ^ expr ^
            "}}")
        | Instance (name, inst) ->
            let inst = self#instance scx inst in
            ("{\"==\": {" ^
                "\"Name\": \"" ^ name.core ^
                    "\", " ^
                "\"Expr\": " ^ inst ^
            "}}")
        | Bpragma(name, expr, pragma) ->
            (* TODO: pragma info *)
            let expr = self#expr scx expr in
            ("{\"==\": {\"" ^
                "\"Name\": " ^ name.core ^
                    "\", " ^
                "\"Expr\": " ^ expr ^
            "}}")

    method defns scx = function
        | [] -> (scx, "")
        | df :: dfs ->
            let def = self#defn scx df in
            let defn = Defn (
                df, User, Visible, Local) @@ df in
            let scx = self#adj scx defn in
            let (scx, defs) = self#defns scx dfs in
            let defstr = def ^ ", " ^ defs in
            (scx, defstr)

    method bounds scx bounds =
        let hyps = hyps_of_bounds bounds in
        let scx = self#adjs scx hyps in
        let mapper (name, kind, dom) =
            match dom with
            | Domain expr ->
                let expr = self#expr scx expr in
                ("{\"Bound\": {" ^
                    "\"Name\": \"" ^ name.core ^
                        "\", " ^
                    "\"Expr\": " ^ expr ^
                "}}")
            | Ditto ->
                ("{\"Bound\": {" ^
                    "\"Name\": \"" ^ name.core ^
                        "\", " ^
                    "\"Ditto\": \"true\"}")
            | No_domain ->
                ("{\"Bound\": {" ^
                    "\"Name\": \"" ^ name.core ^
                "\"}}") in
        let bounds =
            bounds
            |> List.map mapper
            |> Fmtutil.comma in
        (scx, bounds)

    method bound scx b =
        self#bounds scx [b]

    method exspec scx (trail, res) =
        let do_trail = function
            | Except_dot name ->
                "{\".\": \"" ^ name ^ "\"}"
            | Except_apply expr ->
                let expr = self#expr scx expr in
                "{\"[\": " ^ expr ^ "}"
            in
        let trail = List.map do_trail trail in
        let trail = Fmtutil.join ", " trail in
        let expr = self#expr scx res in
        ("{\"Change\": {" ^
            "\"Trail\": [" ^ trail ^
                "], " ^
            "\"Expr\": " ^ expr ^
        "}}")

    method instance scx inst =
        let step scx name =
            let fresh = Fresh (
                name, Shape_expr,
                Unknown, Unbounded) @@ name in
            self#adj scx fresh in
        let scx = List.fold_left
            step scx inst.inst_args in
        let mapper (name, expr) =
            let expr = self#expr scx expr in
            name.core ^ " <- " ^ expr in
        let inst_sub = List.map
            mapper inst.inst_sub in
        let inst_sub = Fmtutil.comma inst_sub in
        ("{\"INSTANCE\": {" ^
            "\"ModuleName\": \"" ^ inst.inst_mod ^
                "\", " ^
            "\"WITH\": " ^ inst_sub ^
        "}}")

    method hyp scx h =
        match h.core with
        | Fresh (name, shape, loc, dom) ->
            let dom = match dom with
                | Unbounded -> ""
                | Bounded (r, rvis) ->
                    self#expr scx r
                in
            let hstr = (
                "{\"Hypothesis\": {" ^
                    "\"Name\": \"" ^ name.core ^
                        "\", " ^
                    "\"Domain\": " ^ dom ^
                "}}") in
            (self#adj scx h, hstr)
        | Flex name ->
            let hstr = (
                "{\"VARIABLE\": \"" ^
                name.core ^ "\"}") in
            (self#adj scx h, hstr)
        | Defn (df, wd, vis, ex) ->
            let df = self#defn scx df in
            let hstr = (
                "{\"Hypothesis\": " ^
                df ^ "}") in
            (self#adj scx h, hstr)
        | Fact (e, vis, tm) ->
            let fact = self#expr scx e in
            let hstr = (
                "{\"Hypothesis\": " ^
                fact ^ "}") in
            (self#adj scx h, hstr)

    method hyps scx hs =
        match Dq.front hs with
        | None -> (scx, "")
        | Some (h, hs) ->
            let (scx, h) = self#hyp scx h in
            let (scx, hs) = self#hyps scx hs in
            match hs with
            | "" -> (scx, h)
            | _ -> (scx, h ^ ", " ^ hs)

    method adj (s, cx) h =
        (s, Dq.snoc cx h)

    method adjs scx = function
        | [] -> scx
        | h :: hs ->
            self#adjs (self#adj scx h) hs
end


let json_of_ast cx expr =
    let visitor =
        object (self: 'self)
        inherit [unit] json_map
        end in
    let scx = ((), cx) in
    visitor#expr scx expr
