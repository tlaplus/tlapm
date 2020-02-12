(*
 * backend/smtlib.ml --- direct translation to SMT-LIB
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

Revision.f "$Rev$";;

open Format

open Ext
open Property
open Fmtutil
open Expr.T
open Proof.T
open Type.T
open Tla_parser

open Util.Coll
open Smttable

module A = Axiom
module B = Builtin

exception Unsupported of string
let unsupp o = raise (Unsupported o)

let get_ty_atom ty =
  match ty with
  | TAtom a -> a
  | _ ->
      let mssg =
        fprintf str_formatter "non-atomic type: %a@."
        pp_print_type ty;
        flush_str_formatter ()
      in
      unsupp mssg

(* All anotations required to be atomic *)
let get_annot h =
  let ty = get_type_annot h in
  get_ty_atom ty

let primed s = s ^ "__prime"


(* {3 Context} *)

let adj cx nm =
  let cx = Ctx.push cx nm.core in
  (cx, Ctx.string_of_ident (Ctx.front cx))

let bump cx =
  fst (adj cx ("" %% []))

let lookup_id cx n =
  Ctx.string_of_ident (fst (Ctx.index cx n))


(* {3 Expression Formatting} *)

(* TODO: support higher-order expressions *)

let pp_print_sort ff (a : ty_atom) =
  let s =
    match a with
    | TBool -> "Bool"
    | TU -> "set"
    | TInt -> "Int"
    | TReal -> "real"
    | TStr -> "string"
  in
  pp_print_string ff s

let rec pp_apply cx ff op args =
  match op.core with
  | Ix n ->
      let id = lookup_id cx n in
      begin match args with
      | [] ->
          pp_print_string ff id
      | _ ->
          fprintf ff "@[<hov 2>(@,%s@ %a@]@,)" id
          (pp_print_delimited ~sep:pp_print_space (pp_print_expr cx))
          args
      end
  | Opaque s ->
      begin match args with
      | [] ->
          pp_print_string ff s
      | _ ->
          fprintf ff "@[<hov 2>(@,%s@ %a@]@,)" s
          (pp_print_delimited ~sep:pp_print_space (pp_print_expr cx))
          args
      end
  | Internal b ->
      let atomic op =
        pp_print_string ff op
      in
      let nonatomic op args =
        fprintf ff "@[<hov 2>(@,%s@ %a@]@,)" op
          (pp_print_delimited ~sep:pp_print_space (pp_print_expr cx))
          args
      in
      let negate f =
        fprintf ff "@[<hov 2>(@,not@ ";
        f ();
        fprintf ff "@]@,)"
      in
      begin match b, args with
      | B.TRUE,     []      -> atomic "true"
      | B.FALSE,    []      -> atomic "false"
      | B.Implies,  [e ; f] -> nonatomic "=>" [e ; f]
      | B.Equiv,    [e ; f] -> nonatomic "=" [e ; f]
      | B.Conj,     [e ; f] -> nonatomic "and" [e ; f]
      | B.Disj,     [e ; f] -> nonatomic "or" [e ; f]
      | B.Neg,      [e]     -> nonatomic "not" [e]
      | B.Eq,       [e ; f] -> nonatomic "=" [e ; f]
      | B.Neq,      [e ; f] -> nonatomic "distinct" [e ; f]

      | B.STRING,   []      -> atomic "TLA__STRING"
      | B.BOOLEAN,  []      -> atomic "TLA__BOOLEAN"
      | B.SUBSET,   [e]     -> nonatomic "TLA__SUBSET" [e]
      | B.UNION,    [e]     -> nonatomic "TLA__UNION" [e]
      | B.DOMAIN,   [e]     -> nonatomic "TLA__DOMAIN" [e]
      | B.Subseteq, [e ; f] -> nonatomic "TLA__subseteq" [e ; f]
      | B.Mem,      [e ; f] -> nonatomic "TLA__in" [e ; f]
      | B.Notmem,   [e ; f] -> negate (fun () -> nonatomic "TLA__in" [e ; f])
      | B.Setminus, [e ; f] -> nonatomic "TLA__setminus" [e ; f]
      | B.Cap,      [e ; f] -> nonatomic "TLA__cap" [e ; f]
      | B.Cup,      [e ; f] -> nonatomic "TLA__cup" [e ; f]

      | B.Leadsto,  [e ; f] -> unsupp "~>"
      | B.ENABLED,  [e]     -> unsupp "ENABLED"
      | B.Cdot,     [e ; f] -> unsupp "\\cdot"
      | B.Actplus,  [e ; f] -> unsupp "-+->"
      | B.Box _,    [e]     -> unsupp "[]"
      | B.Diamond,  [e]     -> unsupp "<>"

      | B.Nat,        []      -> atomic "arith__N"
      | B.Int,        []      -> atomic "arith__Z"
      | B.Real,       []      -> atomic "arith__R"
      | B.Plus,       [e ; f] -> nonatomic "+" [e ; f]
      | B.Minus,      [e ; f] -> nonatomic "-" [e ; f]
      | B.Uminus,     [e]     -> nonatomic "-" [e]
      | B.Times,      [e ; f] -> nonatomic "*" [e ; f]
      | B.Ratio,      [e ; f] -> nonatomic "/" [e ; f]
      | B.Quotient,   [e ; f] -> nonatomic "div" [e ; f]
      | B.Remainder,  [e ; f] -> nonatomic "mod" [e ; f]
      | B.Exp,        [e ; f] -> nonatomic "arith__intexp" [e ; f]
      | B.Infinity,   []      -> atomic "arith__Infinity"
      | B.Lteq,       [e ; f] -> nonatomic "<=" [e ; f]
      | B.Lt,         [e ; f] -> nonatomic "<" [e ; f]
      | B.Gteq,       [e ; f] -> nonatomic ">=" [f ; e]
      | B.Gt,         [e ; f] -> nonatomic ">" [f ; e]
      | B.Range,      [e ; f] -> nonatomic "arith__intrange" [e ; f]

      | B.Seq,        [e]         -> nonatomic "TLA__Seq" [e]
      | B.Len,        [e]         -> nonatomic "TLA__Len" [e]
      | B.BSeq,       [e]         -> nonatomic "TLA__BSeq" [e]
      | B.Cat,        [e ; f]     -> nonatomic "TLA__concat" [e ; f]
      | B.Append,     [e ; f]     -> nonatomic "TLA__Append" [e ; f]
      | B.Head,       [e]         -> nonatomic "TLA__Head" [e]
      | B.Tail,       [e]         -> nonatomic "TLA__Tail" [e]
      | B.SubSeq,     [e ; m ; n] -> nonatomic "TLA__SubSeq" [e ; m ; n]
      | B.SelectSeq,  [e ; f]     -> nonatomic "TLA__SelectSeq" [e ; f]

      | B.OneArg,         [e ; f] -> nonatomic "TLA__oneArg" [e ; f]
      | B.Extend,         [e ; f] -> nonatomic "TLA__extend" [e ; f]
      | B.Print,          [e ; v] -> nonatomic "TLA__Print" [e ; v]
      | B.PrintT,         [e]     -> nonatomic "TLA__PrintT" [e]
      | B.Assert,         [e ; o] -> nonatomic "TLA__Assert" [e ; o]
      | B.JavaTime,       []      -> nonatomic "TLA__JavaTime" []
      | B.TLCGet,         [i]     -> nonatomic "TLA__TLCGet" [i]
      | B.TLCSet,         [i ; v] -> nonatomic "TLA__TLCSet" [i ; v]
      | B.Permutations,   [s]     -> nonatomic "TLA__Permutations" [s]
      | B.SortSeq,        [s ; o] -> nonatomic "TLA__SortSeq" [s ; o]
      | B.RandomElement,  [s]     -> nonatomic "TLA__RandomElement" [s]
      | B.Any,            []      -> atomic "TLA__Any"
      | B.ToString,       [v]     -> nonatomic "TLA__ToString" [v]

      | B.Unprimable, [e] -> pp_print_expr cx ff e

      | _ -> Errors.bug ~at:op "Backend.Smtlib.pp_apply"
      end
  | _ -> Errors.bug ~at:op "Backend.Smtlib.pp_apply"

and fmt_expr cx oe =
  match oe.core with
  | Ix _ | Opaque _ | Internal _ ->
      Fu.Atm (fun ff -> pp_apply cx ff oe [])
  | Lambda _ ->
      Errors.bug ~at:oe "Backend.Smtlib.fmt_expr"
  | Apply (op, args) ->
      Fu.Atm (fun ff -> pp_apply cx ff op args)
  | Sequent sq ->
      begin match Deque.front sq.context with
      | None -> fmt_expr cx sq.active
      | Some ({ core = Fact (e, Visible, _)}, hs) ->
          let ncx = bump cx in
          Fu.Atm begin fun ff ->
            fprintf ff "@[<hov 2>(@,=>@ %a@ %a@]@,)"
            (pp_print_expr cx) e
            (pp_print_expr ncx) (Sequent { sq with context = hs } @@ oe)
          end
      | Some ({ core = Fact (e, Hidden, _)}, hs) ->
          let ncx = bump cx in
          fmt_expr ncx (Sequent { sq with context = hs } @@ oe)
      | Some ({ core = Flex nm }, hs) ->
          let srt = get_annot nm in
          let ncx, nm = adj cx nm in
          Fu.Atm begin fun ff ->
            fprintf ff "@[<hov 2>(@,forall @[<hov 2>(@,(%s %a)@ (%s %a)@]@,)@ %a@]@,)"
            nm pp_print_sort srt
            (primed nm) pp_print_sort srt
            (pp_print_expr ncx) (Sequent { sq with context = hs } @@ oe)
          end
      | Some ({ core = Fresh (nm, _, _, Bounded (b, Visible)) }, hs) ->
          let srt = get_annot nm in
          let ncx, nm = adj cx nm in
          Fu.Atm begin fun ff ->
            fprintf ff "@[<hov 2>(@,forall @[<hov 2>(@,(%s %a)@]@,)@ @[<hov 2>(@,=> @[<hov 2>(@,TLA__in@ %s@ %a@]@,)@ %a@]@,)@]@,)"
            nm pp_print_sort srt
            nm (pp_print_expr cx) b
            (pp_print_expr ncx) (Sequent { sq with context = hs } @@ oe)
          end
      | Some ({ core = Fresh (nm, _, _, _) }, hs) ->
          let srt = get_annot nm in
          let ncx, nm = adj cx nm in
          Fu.Atm begin fun ff ->
            fprintf ff "@[<hov 2>(@,forall @[<hov 2>(@,(%s %a)@]@,)@ %a@]@,)"
            nm pp_print_sort srt
            (pp_print_expr ncx) (Sequent { sq with context = hs } @@ oe)
          end
      | _ -> Errors.bug ~at:oe "Backend.Smtlib.fmt_expr"
      end
  | Bang _ ->
      Errors.bug ~at:oe "Backend.Smtlib.fmt_expr"
  | With (e, _) ->
      fmt_expr cx e
  | If (e, f, g) ->
      Fu.Atm begin fun ff ->
        fprintf ff "@[<hov 2>(@,ite@ %a@ %a@ %a@]@,)"
        (pp_print_expr cx) e
        (pp_print_expr cx) f
        (pp_print_expr cx) g
      end
  | List (Refs, []) ->
      Errors.bug ~at:oe "Backend.Smtlib.fmt_expr"
  | List (Refs, [e]) ->
      fmt_expr cx e
  | List (q, es) ->
      let rep =
        match q with
        | And | Refs -> "and"
        | Or -> "or"
      in
      Fu.Atm begin fun ff ->
        fprintf ff "@[<hov 2>(@,%s@ %a@]@,)" rep
        (pp_print_delimited ~sep:pp_print_space (pp_print_expr cx)) es
      end
  | Let ([], _) ->
      Errors.bug ~at:oe "Backend.Smtlib.fmt_expr"
  | Let (ds, e) ->
      let ncx, vs =
        let rec f acc_cx acc_vs ds =
          match ds with
          | [] -> (acc_cx, acc_vs)
          | { core = Operator (_, { core = Lambda _ }) } :: _ ->
              Errors.bug ~at:oe "Backend.Smtlib.fmt_expr"
          | { core = Operator (nm, e) } :: ds ->
              let acc_cx, nm = adj acc_cx nm in
              let acc_vs = (nm, e) :: acc_vs in
              f acc_cx acc_vs ds
          | _ ->
              Errors.bug ~at:oe "Backend.Smtlib.fmt_expr"
        in
        f cx [] ds
      in
      let pp_print_vbind cx ff (nm, e) =
        fprintf ff "@[<hov 2>(@,%s@ %a@]@,)" nm
        (pp_print_expr cx) e
      in
      Fu.Atm begin fun ff ->
        fprintf ff "@[<hov 2>(@,let @[<hov 2>(@,%a@]@,)@ %a@]@,)"
        (pp_print_delimited ~sep:pp_print_space (pp_print_vbind cx)) vs
        (pp_print_expr ncx) e
      end
  | Quant (_, [], e) ->
      fmt_expr cx e
  | Quant (q, bs, e) ->
      let ncx, bs, ds =
        let rec f (d : expr option) acc_cx acc_bs acc_ds bs =
          match bs with
          | [] -> (acc_cx, acc_bs, acc_ds)
          | (nm, _, No_domain) :: bs ->
              let srt = get_annot nm in
              let acc_cx, nm = adj acc_cx nm in
              let acc_bs = (nm, srt) :: acc_bs in
              f None acc_cx acc_bs acc_ds bs
          | (nm, _, Domain b) :: bs ->
              let srt = get_annot nm in
              let acc_cx, nm = adj acc_cx nm in
              let acc_bs = (nm, srt) :: acc_bs in
              let acc_ds = (nm, b) :: acc_ds in
              f (Some b) acc_cx acc_bs acc_ds bs
          | (nm, _, Ditto) :: bs ->
              let srt = get_annot nm in
              let acc_cx, nm = adj acc_cx nm in
              let acc_bs = (nm, srt) :: acc_bs in
              let acc_ds = (nm, Option.get d) :: acc_ds in
              f d acc_cx acc_bs acc_ds bs
        in
        f None cx [] [] bs
      in
      let bs = List.rev bs in
      let qrep =
        match q with
        | Forall -> "forall"
        | Exists -> "exists"
      in
      let pp_print_bound cx ff (nm, b) =
        fprintf ff "@[<hov 2>(@,TLA__in@ %s@ %a@]@,)"
        nm (pp_print_expr cx) b
      in
      Fu.Atm begin fun ff ->
        fprintf ff "@[<hov 2>(@,%s @[<hov 2>(@,%a@]@,) " qrep
        (pp_print_delimited ~sep:pp_print_space begin fun ff (nm, srt) ->
          fprintf ff "(%s %a)" nm pp_print_sort srt
        end) bs;
        begin match ds with
        | [] ->
            pp_print_expr ncx ff e
        | [b] ->
            fprintf ff "@[<hov 2>@,(=>@ %a@ %a@]@,)"
            (pp_print_bound cx) b
            (pp_print_expr ncx) e
        | _ ->
            fprintf ff "@[<hov 2>(@,=> @[<hov 2>(@,and %a@]@,)@ %a@]@,)"
            (pp_print_delimited ~sep:pp_print_space (pp_print_bound cx)) ds
            (pp_print_expr ncx) e
        end;
        fprintf ff "@]@,)"
      end
  | Tquant (Forall, _, _) -> unsupp "\\AA"
  | Tquant (Exists, _, _) -> unsupp "\\EE"
  | Choose _ -> unsupp "CHOOSE"
  | SetSt _ -> unsupp "{ x \\in _ : _ }"
  | SetOf _ -> unsupp "{ _ : x \\in _ }"
  | SetEnum [] ->
      Fu.Atm begin fun ff ->
        fprintf ff "TLA__Empty"
      end
  | SetEnum es ->
      let n = List.length es in
      Fu.Atm begin fun ff ->
        fprintf ff "@[<hov 2>(@,TLA__Enum_%d@ %a@]@,)" n
        (pp_print_delimited ~sep:pp_print_space (pp_print_expr cx)) es
      end
  | Product [] ->
      Fu.Atm begin fun ff ->
        fprintf ff "TLA__Unit"
      end
  | Product [e] ->
      fmt_expr cx e
  | Product es ->
      let n = List.length es in
      Fu.Atm begin fun ff ->
        fprintf ff "@[<hov 2>(@,TLA__Prod_%d@ %a@]@,)" n
        (pp_print_delimited ~sep:pp_print_space (pp_print_expr cx)) es
      end
  | Tuple [] ->
      Fu.Atm begin fun ff ->
        fprintf ff "TLA__unit"
      end
  | Tuple [e] ->
      fmt_expr cx e
  | Tuple es ->
      let n = List.length es in
      Fu.Atm begin fun ff ->
        fprintf ff "@[<hov 2>(@,TLA__tuple_%d@ %a@]@,)" n
        (pp_print_delimited ~sep:pp_print_space (pp_print_expr cx)) es
      end
  | Fcn _ -> unsupp "[ x \\in _ |-> _ ]"
  | FcnApp (_, []) ->
      Errors.bug ~at:oe "Backend.Smtlib.fmt_expr"
  | FcnApp (e, [e1]) ->
      Fu.Atm begin fun ff ->
        fprintf ff "@[<hov 2>(TLA__fcnapp@ %a@ %a@]@,)"
        (pp_print_expr cx) e
        (pp_print_expr cx) e1
      end
  | FcnApp (e, es) ->
      let n = List.length es in
      Fu.Atm begin fun ff ->
        fprintf ff "@[<hov 2>(@,TLA__fcnapp@ %a@ @[<hov 2>(@,TLA__tuple_%d@ %a@]@,)@]@,)"
        (pp_print_expr cx) e n
        (pp_print_delimited ~sep:pp_print_space (pp_print_expr cx)) es
      end
  | Arrow (e1, e2) ->
      Fu.Atm begin fun ff ->
        fprintf ff "@[<hov 2>(@,TLA__Arrow@ %a@ %a@]@,)"
        (pp_print_expr cx) e1
        (pp_print_expr cx) e2
      end
  | Rect fs ->
      let n = List.length fs in
      let pp_print_field cx ff (f, e) =
        fprintf ff "%s %a" f (pp_print_expr cx) e
      in
      Fu.Atm begin fun ff ->
        fprintf ff "@[<hov 2>(@,TLA__Rect_%d@ %a@]@,)" n
        (pp_print_delimited ~sep:pp_print_space (pp_print_field cx)) fs
      end
  | Record fs ->
      let n = List.length fs in
      let pp_print_field cx ff (f, e) =
        fprintf ff "%s %a" f (pp_print_expr cx) e
      in
      Fu.Atm begin fun ff ->
        fprintf ff "@[<hov 2>(@,TLA__record_%d@ %a@]@,)" n
        (pp_print_delimited ~sep:pp_print_space (pp_print_field cx)) fs
      end
  | Except (e1, [[Except_dot f], e2]) ->
      Errors.bug ~at:oe "Backend.Smtlib.fmt_expr"
  | Except (e1, [[Except_apply e2], e3]) ->
      Fu.Atm begin fun ff ->
        fprintf ff "@[<hov 2>(@,TLA__except@ %a@ %a@ %a@]@,)"
        (pp_print_expr cx) e1
        (pp_print_expr cx) e2
        (pp_print_expr cx) e3
      end
  | Except _ -> unsupp "complex EXCEPT"
  | Dot _ -> unsupp "Dot"
  | Sub _ -> unsupp "Sub"
  | Tsub _ -> unsupp "Tsub"
  | Fair (Weak, _, _) -> unsupp "WF_"
  | Fair (Strong, _, _) -> unsupp "SF_"
  | Case (_, None) -> unsupp "incomplete CASE"
  | Case ([], _) ->
      Errors.bug ~at:oe "Backend.Smtlib.fmt_expr"
  | Case ([e1, e2], Some e3) ->
      fmt_expr cx (If (e1, e2, e3) @@ oe)
  | Case ((e1, e2) :: ps, Some o) ->
      fmt_expr cx (If (e1, e2, Case (ps, Some o) %% []) @@ oe)
  | String _ -> unsupp "String literals"
  | Num (m, "") ->
      Fu.Atm begin fun ff ->
        fprintf ff "%s" m
      end
  | Num (m, n) ->
      Fu.Atm begin fun ff ->
        fprintf ff "%s.%s" m n
      end
  | At _ ->
      Errors.bug ~at:oe "Backend.Smtlib.fmt_expr"
  | Parens (e, _) ->
      fmt_expr cx e

and pp_print_expr cx ff e =
  Fu.pp_print_minimal ff (fmt_expr cx e)


(* {3 Obligation Formatting} *)

let pp_print_obligation ?(solver="CVC4") ff ob =
  let sq = Type.MinRecon.min_reconstruct ob.obl.core in

  (* Collect symbols *)
  let module C = NT_Collector in
  let smbs = C.collect sq in
  let decls = Sm.map C.get_decl smbs in

  let srts, decls = Sm.partition begin fun id decl ->
    match decl.content with Srt _ -> true | _ -> false
  end decls in
  let funs, axms = Sm.partition begin fun id decl ->
    match decl.content with Fun _ -> true | _ -> false
  end decls in

  let srts = Sm.bindings srts |> List.map snd in
  let funs = Sm.bindings funs |> List.map snd in
  let axms = Sm.bindings axms in

  (* Print preample *)
  pp_print_newline ff ();
  fprintf ff ";; TLA+ Proof Manager %s@." (Params.rawversion ());
  fprintf ff ";; Proof obligation #%d@." (Option.get ob.id);
  fprintf ff ";; Generated from %s@." (Util.location ~cap:false ob.obl);
  pp_print_newline ff ();

  fprintf ff "(set-logic UFNIA)@.";
  pp_print_newline ff ();

  let rec pp_print_cmds ?(skip=false) fmt ff al =
    match al with
    | [] -> ()
    | a :: [] ->
        fmt ff a;
        pp_print_newline ff ()
    | a :: al ->
        fmt ff a;
        pp_print_newline ff ();
        if skip then pp_print_newline ff ()
        else ();
        pp_print_cmds ~skip fmt ff al
  in

  (* Print sort declarations *)
  fprintf ff ";; Sort Declarations@.";
  (*pp_print_delimited ~sep:pp_print_newline pp_print_decl ff srts;*)
  pp_print_cmds pp_print_decl ff srts;
  pp_print_newline ff ();

  (* Print fun declarations *)
  fprintf ff ";; Operator Declarations@.";
  (*pp_print_delimited ~sep:pp_print_newline pp_print_decl ff funs;*)
  pp_print_cmds pp_print_decl ff funs;
  pp_print_newline ff ();

  (* Print axioms *)
  fprintf ff ";; Axioms@.";
  let pp_print_axm ff (id, d) =
    fprintf ff "; %s@." id;
    pp_print_decl ff d;
    pp_print_newline ff ()
  in
  pp_print_delimited ~sep:pp_print_newline pp_print_axm ff axms;
  pp_print_newline ff ();

  (* Print hypotheses *)
  let pp_print_assert cx ff e =
    fprintf ff "@[<hov 2>(assert@ %a@]@,)@."
    (pp_print_expr cx) e
  in
  let rec spin cx hs =
    match Deque.front hs with
    | None ->
        cx
    | Some ({ core = Fact (e, vis, _) }, hs) ->
        let ncx = bump cx in
        begin if vis = Visible then
          pp_print_assert cx ff e
        else
          fprintf ff "; hidden fact@."
        end;
        pp_print_newline ff ();
        spin ncx hs
    | Some ({ core = Flex nm }, hs) ->
        let srt = get_annot nm in
        let ncx, nm = adj cx nm in
        let decl1 = mk_fdecl nm [] (TAtom srt) in
        let decl2 = mk_fdecl (primed nm) [] (TAtom srt) in
        pp_print_decl ff decl1;
        pp_print_decl ff decl2;
        pp_print_newline ff ();
        spin ncx hs
    | Some ({ core = Fresh (nm, _, _, Bounded (b, Visible)) }, hs) ->
        let srt = get_annot nm in
        let ncx, nm = adj cx nm in
        let decl = mk_fdecl nm [] (TAtom srt) in
        pp_print_decl ff decl;
        pp_print_assert cx ff (
          Apply (Internal B.Mem %% [], [ Opaque nm %% [] ; b ]) %% []);
        pp_print_newline ff ();
        spin ncx hs
    | Some ({ core = Fresh (nm, _, _, _) }, hs) ->
        let srt = get_annot nm in
        let ncx, nm = adj cx nm in
        let decl = mk_fdecl nm [] (TAtom srt) in
        pp_print_decl ff decl;
        spin ncx hs
    | Some ({ core = Defn ({ core = Operator (nm, _) }, _, vis, _) }, hs)
    | Some ({ core = Defn ({ core = Instance (nm, _) }, _, vis, _) }, hs)
    | Some ({ core = Defn ({ core = Recursive (nm, _) }, _, vis, _) }, hs)
    | Some ({ core = Defn ({ core = Bpragma (nm, _, _) }, _, vis, _) }, hs) ->
        let ncx, nm = adj cx nm in
        begin if vis = Visible then
          fprintf ff "; hidden definition: %s@." nm
        end;
        pp_print_newline ff ();
        spin ncx hs
  in
  fprintf ff ";; Hypotheses@.";
  let cx = spin Ctx.dot sq.context in

  (* Print goal *)
  fprintf ff ";; Goal@.";
  pp_print_assert cx ff (Apply (Internal B.Neg %% [], [sq.active]) %% []);
  pp_print_newline ff ();

  fprintf ff "(check-sat)@.";
  fprintf ff "(exit)@."
