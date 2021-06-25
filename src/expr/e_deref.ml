(*
 * expr/deref.ml --- dereferencing subexpression references
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

open Ext
open Property

open E_t
open E_subst
open E_fmt

module Visit = E_visit


let atomic : unit pfuncs = Property.make "Expr.Deref.atom"

let clean =
  let cleaner = object (self : 'self)
    inherit [unit] Visit.map as super
    method expr scx e =
      let e = match e.core with
        | Parens (e, _) -> self#expr scx e
        | _ -> super#expr scx e
      in
      remove e atomic
  end in
  fun e -> cleaner#expr ((), Deque.empty) e

let paren_clean =
  let cleaner = object (self : 'self)
    inherit [unit] Visit.map as super
    method expr scx e = match e.core with
      | Let (ds, e) -> Let (ds, self#expr scx e) @@ e
      | Parens (e, _) -> self#expr scx e
      | _ -> super#expr scx e
  end in
  fun e -> cleaner#expr ((), Deque.empty) e

let badexp = Opaque "$Bad" @@ nowhere
let is_badexp e = match e.core with
  | Opaque "$Bad" -> true
  | _ -> false

exception Negix
let has_negix =
  let vtor = object (self : 'self)
    inherit [unit] Visit.iter as super

    method expr scx e = match e.core with
      | Ix n when n <= 0 -> raise Negix
      | _ -> super#expr scx e
  end in
  fun e ->
    try vtor#expr ((), Deque.empty) e ; false
    with Negix -> true

exception Label_found of hyp Deque.dq * expr * (Util.hint * int) list
exception No_such_label
let find_label =
  let scanner = object (self : 'self)
    inherit [string] Visit.iter as super
    method expr (l, cx as scx) e = match e.core with
      | Parens (e, {core = Xlabel (ll, llargs)}) ->
          if l = ll then
            raise (Label_found (cx, e, llargs))
          else ()
      | _ ->
          super#expr scx e
    method sequent (l, cx as scx) sq = match Deque.front (sq.context) with
      | None ->
          self#expr scx sq.active ;
          scx
      | Some ({core = Fact (e, _, _)} as h, sqcx) ->
          self#expr scx e ;
          let cx = Deque.snoc cx h in
          self#sequent (l, cx) { sq with context = sqcx }
      | Some _ ->
          (* no visible labels underneath declarations or definitions *)
          scx
  end in
  fun e l ->
    scanner#expr (l, Deque.empty) e ;
    raise No_such_label

let recx cx ds fmt =
  let hs = List.map begin
    fun df -> Defn (df, User, Visible, Export) @@ df
  end ds in
  let cx = Deque.append_list cx hs in
  fmt (cx, Ctx.dot)

exception Bad_index

let rec deref ~islab cx (vss, ds, e) sels =
  let orig_e = e in
  match sels with
    | [] ->
        let e = match ds with
          | [] -> e
          | _ -> Let (ds, e) @@ e
        in
        let e = match vss with
          | [] -> e
          | _ -> Lambda (vss, e) @@ e
        in
        assign (clean e) atomic ()
    | _ when has e atomic ->
        Errors.warning := true;
        Errors.set orig_e ("Expression has no subexpressions");
        Util.eprintf ~at:orig_e "Expression has no subexpressions" ;
        badexp
    | sel :: sels ->
        let e = if islab then e else paren_clean e in
        let (nvss, nds, e, sels, islab) = match sel with
          | Sel_down -> begin match e.core, sels with
              | Let _, (Sel_lab (opname, opargs) :: sels) when islab ->
                  let (nvss, nds, e) = deref_letop cx (List.length ds, e) opname opargs in
                  (nvss, nds, e, sels, true)
              | _ when islab ->
                  (* e is the body of an opdef *)
                  ([], [], e, sels, false)
              | _ ->
                  recx cx ds begin fun cx ->
                    Errors.warning := true;
                    Errors.set e ("!: is forbidden for this expression.\n");
                     (* ((pp_print_expr cx ????? e)));*)
                    Util.eprintf ~at:orig_e
                      "!: is forbidden for this expression:@\n%a"
                      (pp_print_expr cx) e ;
                    failwith "Expr.Deref.deref: !:"
                  end
            end
          | Sel_num n ->
              let (nds, e) = try deref_num cx ([], e) n
              with Bad_index ->
                Errors.warning := true;
                Errors.set orig_e (Printf.sprintf "Cannot resolve !%d" n);
                Util.eprintf ~at:orig_e "Cannot resolve !%d" n ;
                failwith "Expr.Deref.deref_num"
              in
              ([], nds, e, sels, false)
          | Sel_left ->
              let (nds, e) = try deref_num cx ([], e) 1
              with Bad_index ->
                Errors.warning := true;
                Errors.set orig_e "Cannot resolve !<<";
                Util.eprintf ~at:orig_e "Cannot resolve !<<" ;
                failwith "Expr.Deref.deref_num"
              in
              ([], nds, e, sels, false)
          | Sel_right ->
              let (nds, e) = try deref_num cx ([], e) 2
              with Bad_index ->
                Errors.warning := true;
                Errors.set orig_e "Cannot resolve !>>";
                Util.eprintf ~at:orig_e "Cannot resolve !>>" ;
                  failwith "Expr.Deref.deref_num"
              in
              ([], nds, e, sels, false)
          | Sel_inst args ->
              let e = deref_inst cx e args in
              ([], [], e, sels, false)
          | Sel_lab (l, args) -> begin
              match e.core with
                | Let _ when not islab ->
                    let (nvss, nds, e) = deref_letop cx (List.length ds, e) l args in
                    (nvss, nds, e, sels, true)
                | _ ->
                    let (nvss, nds, e) = deref_label cx (List.length ds, e) l args in
                    (nvss, nds, e, sels, true)
            end
          | Sel_at ->
              let (nvss, e) = deref_at cx (List.length ds, e) in
              (nvss, [], e, sels, false)
        in
        let sels = List.map (app_sel (shift (List.length nds))) sels in
        deref ~islab:islab cx (vss @ nvss, ds @ nds, e) sels

and deref_letop cx (dslen, e) l args = match e.core with
  | Let (lds, _) ->
      let rec find_def prefix = function
        | [] ->
            Errors.warning := true;
            Errors.set e (Printf.sprintf "no definition of operator %s" l);
            Util.eprintf ~at:e "no definition of operator %s" l ;
            failwith "Expr.Deref.deref_letop"
        | ld :: lds -> begin match ld.core with
            | Operator (nm, op) when nm.core = l -> begin
                let op = match op.core with
                  | Lambda (vss, e) ->
                      let vsslen = List.length vss in
                      let largs = List.mapi (fun n (v, _) -> (v, vsslen - n)) vss in
                      let e = Parens (e, Xlabel (l, largs) @@ nm) @@ e in
                      Lambda (vss, e) @@ op
                  | _ ->
                      Parens (op, Xlabel (l, []) @@ nm) @@ op
                in
                Let (List.rev prefix, op) @@ op
              end
            | _ ->
                find_def (ld :: prefix) lds
          end
      in
      let se = find_def [] lds in
      deref_label cx (dslen, se) l args
  | _ ->
      Errors.warning := true;
      Errors.set e  "not a LET expression";
      Util.eprintf ~at:e "not a LET expression" ;
      failwith "Expr.Deref.deref_letop"

and deref_num cx (ds, e) n =
  assert (n > 0) ;
  let check_lteq k = if n > k then raise Bad_index in
  let (ds, se) = match e.core with
    | Sequent sq -> begin
        check_lteq (Deque.size sq.context + 1) ;
        let rec spin k hs = begin
          match Deque.front hs with
            | None ->
                app_expr (shift (- k)) sq.active
            | Some (h, hs) -> begin
                match h.core with
                  | Fact (f, _, _) ->
                      if k + 1 = n then
                        app_expr (shift (- k)) f
                      else
                        spin (k + 1) hs
                  | _ ->
                      if k + 1 = n then begin
                        Errors.warning := true;
                        Errors.set e  "subexpression reference does not resolve to an expression";
                        Util.eprintf ~at:e "subexpression reference does not resolve to an expression" ;
                        failwith "Expr.Deref.deref_num"
                      end else
                        spin (k + 1) hs
              end
        end in
        let se = spin 0 sq.context in
        if has_negix se then begin
          Errors.warning := true;
          Errors.set e (
            "Subexpression of ASSUME/PROVE uses identifiers declared " ^
            "therein\n\nTlapm does not handle yet such subexpression namings.");
          Util.eprintf ~at:e "%s" (
            "subexpression of ASSUME/PROVE uses identifiers declared therein" ^
            "\nTlapm does not handle yet such subexpression namings.");
          failwith "Expr.Deref.deref_num"
        end else (ds, se)
      end
    | Apply (op, args) ->
        check_lteq (List.length args) ;
        (ds, List.nth args (n - 1))
    | With (e, t) ->
        deref_num cx (ds, e) n
    | If (e, f, g) ->
        check_lteq 3 ;
        (ds, if n = 1 then e else if n = 2 then f else g)
    | List (_, es) | SetEnum es | Product es | Tuple es ->
        check_lteq (List.length es) ;
        (ds, List.nth es (n - 1))
    | Let (lds, e) ->
        check_lteq 1 ;
        (ds @ lds, e)
    | Quant (_, bs, _) | SetOf (_, bs) | Fcn (bs, _) ->
        let doms = List.filter_map begin function
          | (_, _, Domain d) -> Some d
          | _ -> None
        end bs in
        check_lteq (List.length doms) ;
        (ds, List.nth doms (n - 1))
    | Choose (_, Some dom, _) | SetSt (_, dom, _) ->
        check_lteq 1 ;
        (ds, dom)
    | Arrow (e, f) ->
        check_lteq 2 ;
        (ds, if n = 1 then e else f)
    | FcnApp (f, args) ->
        check_lteq 2 ;
        let se = if n = 1 then f else match args with
          | [arg] -> arg
          | _ -> Tuple args @@ e
        in
        (ds, se)
    | Rect fs | Record fs ->
        check_lteq (List.length fs) ;
        (ds, snd (List.nth fs (n - 1)))
    | Dot (e, f) ->
        check_lteq 2 ;
        (ds, if n = 1 then e else String f @@ e)
    | Except (e, xs) ->
        check_lteq (List.length xs + 1) ;
        (ds, if n = 1 then e else snd (List.nth xs (n - 2)))
    | Sub (_, e, f) | Tsub (_, e, f) | Fair (_, e, f) ->
        check_lteq 2 ;
        (ds, if n = 1 then e else f)
    | Case (arms, oth) ->
        let pairs = List.fold_right begin
          fun (p, e) es ->
            (Tuple [p ; e] @@ e) :: es
        end arms begin match oth with
          | None -> []
          | Some e -> [Tuple [badexp ; e] @@ e]
        end in
        check_lteq (List.length pairs) ;
        (ds, List.nth pairs (n - 1))
    | _ ->
        Errors.warning := true;
        Errors.set e  "Expression has no subexpressions";
        Util.eprintf ~at:e "Expression has no subexpressions" ;
        failwith "Expr.Deref.deref_num"
  in
  if is_badexp se then begin
    Errors.warning := true;
    Errors.set e  (Printf.sprintf "Cannot resolve subexpression reference !%d" n);
    Util.eprintf ~at:e "Cannot resolve subexpression reference !%d" n ;
    failwith "Expr.Deref.deref_num"
  end ;
  (ds, se)

and deref_inst cx e args =  match e.core with
  | ( Quant (_, bs, e)
    | Fcn (bs, e)
    | SetOf (e, bs)
    ) when List.length bs = List.length args ->
      let sub = List.fold_left begin
        fun sub arg -> scons (assign arg atomic ()) sub
      end (shift 0) args in
      app_expr sub e
  | ( Fcn (bs, _)
    | Quant (_, bs, _)
    | SetOf (_, bs)
    ) ->
      let bl = List.length bs in
      let al = List.length args in
     Errors.warning := true;
     Errors.set e  (Printf.sprintf "Arity mismatch in subexpression instance.@\nExpected %d argument%s, but found%s %d."
                      bl (if bl = 1 then "" else "s")
                      (if al < bl then " only" else "") al);
        Util.eprintf ~at:e
        "Arity mismatch in subexpression instance.@\nExpected %d argument%s, but found%s %d."
        bl (if bl = 1 then "" else "s")
        (if al < bl then " only" else "") al ;
      failwith "Expr.Deref.deref_inst"
  | Tquant (q, vs, qe) ->
      let bs = List.map (fun v -> (v, State, No_domain)) vs in
      let e = Quant (q, bs, qe) @@ e in
      deref_inst cx e args
  | Lambda (vss, le) ->
      let bs = List.map (fun (v, sh) -> (v, Unknown, No_domain)) vss in
      let e = Quant (Forall, bs, le) @@ e in
      deref_inst cx e args
  | ( SetSt (_, _, bod)
    | Choose (_, _, bod) ) -> begin match args with
      | [arg] -> app_expr (scons (assign arg atomic ()) (shift 0)) bod
                        (* was shift 1 -> resolves tlapm bug 18 Oct 2010 #1 *)
      | _ ->
          Errors.warning := true;
          Errors.set e  (Printf.sprintf  "Arity mismatch in subexpression instance.@\nExpected 1 argument, but found %d."
                           (List.length args));
          Util.eprintf ~at:e
            "Arity mismatch in subexpression instance.@\nExpected 1 argument, but found %d."
            (List.length args) ;
          failwith "Expr.Deref.deref_inst"
    end
  | _ ->
      Errors.warning := true;
      Errors.set e  "Cannot instantiate non-binding expression";
      Util.eprintf ~at:e "Cannot instantiate non-binding expression" ;
      failwith "Expr.Deref.deref_inst"

and deref_at cx (dslen, e) =
  let vss = match e.core with
    | ( Quant (_, bs, qe)
      | Fcn (bs, qe)
      | SetOf (qe, bs)
      ) ->
        List.map (fun (v, _, _) -> (v, Shape_expr)) bs
    | Tquant (_, vs, _) ->
        List.map (fun v -> (v, Shape_expr)) vs
    | Lambda (vss, _) ->
        vss
    | ( SetSt (h, _, qe)
      | Choose (h, _, qe)
      ) ->
        [(h, Shape_expr)]
    | _ ->
       Errors.warning := true;
        Errors.set e  "Cannot abstract over bound variables in a non-binding expression";
       Util.eprintf ~at:e "Cannot abstract over bound variables in a non-binding expression" ;
        failwith "Expr.Deref.deref_at"
  in
  let vsslen = List.length vss in
  let vssub = List.init dslen (fun k -> Ix (k + 1) @@ e) in
  let vssub = List.fold_left ssnoc (shift (dslen + vsslen)) vssub in
  let e = app_expr vssub e in
  let iargs = List.rev (List.init vsslen (fun n -> Ix (n + 1) @@ e)) in
  let e = deref_inst cx e iargs in
  (vss, e)

and deref_label cx (dslen, e) l largs =
  try find_label e l with
    | No_such_label ->
        Util.eprintf ~at:e
          "Could not find label %s" l ;
        ([], [], badexp)
    | Label_found (lcx, e, lpi) ->
        if List.length lpi <> List.length largs && largs <> [] then begin
          Errors.warning := true;
          Errors.set e  (Printf.sprintf "Expected %d argument%s for labelled reference !%s, but found %d"
                            (List.length lpi) (if lpi = [] then "s" else if List.tl lpi = [] then "" else "s") l
                            (List.length largs));
          Util.eprintf ~at:e "Expected %d argument%s for labelled reference !%s, but found %d"
            (List.length lpi) (if lpi = [] then "s" else if List.tl lpi = [] then "" else "s") l
            (List.length largs) ;
          failwith "Expr.Deref.deref_lsub"
        end ;
        let (vss, largs) = match lpi, largs with
          | _, [] ->
              let vss = List.mapi (fun n (v, _) -> (v, Shape_expr)) lpi in
              let largs = List.rev (List.mapi (fun n _ -> Ix (n + 1) @@ e) lpi) in
              (vss, largs)
          | _ ->
              ([], largs)
        in
        let vsslen = List.length vss in
        let vssub = List.init dslen (fun k -> Ix (k + 1) @@ e) in
        let vssub = List.fold_left ssnoc (shift (dslen + vsslen)) vssub in
        let rec reify_cx cx e = match Deque.rear cx with
          | Some (cx, {core = Defn (df, _, _, _)}) ->
              let e = Let ([df], e) @@ e in
              reify_cx cx e
          | Some (cx, {core = Fresh (v, _, _, _)}) ->
              let e = Quant (Forall, [v, Constant, No_domain], e) @@ e in
              reify_cx cx e
          | Some (cx, _) ->
              let e = app_expr (shift (-1)) e in
              reify_cx cx e
          | None ->
              e
        in
        let e = reify_cx lcx e in
        let e = app_expr vssub e in
        let perm xs es =
          let xs = List.map snd xs in
          let xsl = List.length xs in
          let rec spin xs = function
            | n when n < 0 -> xs
            | n when List.exists ((=) (xsl - n)) xs ->
                spin xs (n - 1)
            | n ->
                let xs = List.map (fun k -> if k + n < xsl then k else k - 1) xs in
                spin xs (n - 1)
          in
          let xs = spin xs (xsl - 1) in
          let xs = List.map (fun k -> xsl - k + 1) xs in
          List.map (fun k -> List.nth es (k - 1)) xs
        in
        let largs = perm lpi largs in
        let rec apply_largs e largs = match largs with
          | [] -> ([], e)
          | larg :: largs -> begin match e.core with
              | Let ([df], e) ->
                  let largs = List.map (app_expr (shift 1)) (larg :: largs) in
                  let (dfs, e) = apply_largs e largs in
                  (df :: dfs, e)
              | Quant (q, [b], e) ->
                  let e = app_expr (scons (assign larg atomic ()) (shift 0)) e in
                  apply_largs e largs
              | _ -> assert false
            end
        in
        let (ds, e) = apply_largs e largs in
        (vss, ds, e)

let resolve_bang cx op opargs sels = match opargs with
  | [] -> begin match op.core with
      | Lambda _ ->
          let (vss, e) = deref_at cx (0, op) in
          deref ~islab:true cx (vss, [], e) sels
      | _ ->
          deref ~islab:true cx ([], [], op) sels
    end
  | _ ->
      let e = deref_inst cx op opargs in
      deref ~islab:true cx ([], [], e) sels
