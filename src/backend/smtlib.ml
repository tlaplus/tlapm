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

module Names = Reduce.NtAxioms
module B = Builtin

exception Unsupported of string
let unsupp o = raise (Unsupported o)

let get_sort h =
  get h Props.atom_prop

let get_kind h =
  get h Props.kind_prop

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
    | TU -> Names.usort_nm
    | TInt -> "Int"
    | TReal -> "Real"
    | TStr -> Names.stringsort_nm
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
      let s =
        if has op Type.Disambiguation.any_special_prop then
          match get op Type.Disambiguation.any_special_prop with
          | TU -> Names.uany_nm
          | TStr -> Names.stringany_nm
          | _ -> s
        else if has op Type.Disambiguation.cast_special_prop then
          match get op Type.Disambiguation.cast_special_prop with
          | TBool, TU -> Names.booltou_nm
          | TStr, TU -> Names.stringtou_nm
          | _, _ -> s
        else
          s
      in
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
      let is_zarith b =
        has b Type.Disambiguation.int_special_prop
      in
      let is_rarith b =
        has b Type.Disambiguation.real_special_prop
      in
      let is_zrarith b =
        is_zarith b || is_rarith b
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

      | B.STRING,   []      -> atomic Names.string_nm
      | B.BOOLEAN,  []      -> atomic Names.boolean_nm
      | B.SUBSET,   [e]     -> nonatomic Names.power_nm [e]
      | B.UNION,    [e]     -> nonatomic Names.union_nm [e]
      | B.DOMAIN,   [e]     -> nonatomic Names.domain_nm [e]
      | B.Subseteq, [e ; f] -> nonatomic Names.subseteq_nm [e ; f]
      | B.Mem,      [e ; f] -> nonatomic Names.mem_nm [e ; f]
      | B.Notmem,   [e ; f] -> negate (fun () -> nonatomic Names.mem_nm [e ; f])
      | B.Setminus, [e ; f] -> nonatomic Names.setminus_nm [e ; f]
      | B.Cap,      [e ; f] -> nonatomic Names.cap_nm [e ; f]
      | B.Cup,      [e ; f] -> nonatomic Names.cup_nm [e ; f]

      | B.Leadsto,  [e ; f] -> unsupp "~>"
      | B.ENABLED,  [e]     -> unsupp "ENABLED"
      | B.Cdot,     [e ; f] -> unsupp "\\cdot"
      | B.Actplus,  [e ; f] -> unsupp "-+->"
      | B.Box _,    [e]     -> unsupp "[]"
      | B.Diamond,  [e]     -> unsupp "<>"

      | B.Nat,        []      -> atomic Names.nset_nm
      | B.Int,        []      -> atomic Names.zset_nm
      | B.Real,       []      -> atomic Names.rset_nm

      | B.Plus,       [e ; f] when is_zrarith op -> nonatomic "+" [e ; f]
      | B.Minus,      [e ; f] when is_zrarith op -> nonatomic "-" [e ; f]
      | B.Uminus,     [e]     when is_zrarith op -> nonatomic "-" [e]
      | B.Times,      [e ; f] when is_zrarith op -> nonatomic "*" [e ; f]
      | B.Ratio,      [e ; f] when is_rarith op  -> nonatomic "/" [e ; f]
      | B.Quotient,   [e ; f] when is_zarith op  -> nonatomic "div" [e ; f]
      | B.Remainder,  [e ; f] when is_zarith op  -> nonatomic "mod" [e ; f]
      | B.Exp,        [e ; f] when is_zrarith op -> nonatomic Names.exp_nm [e ; f]
      | B.Lteq,       [e ; f] when is_zrarith op -> nonatomic "<=" [e ; f]
      | B.Lt,         [e ; f] when is_zrarith op -> nonatomic "<" [e ; f]
      | B.Gteq,       [e ; f] when is_zrarith op -> nonatomic ">=" [f ; e]
      | B.Gt,         [e ; f] when is_zrarith op -> nonatomic ">" [f ; e]
      | B.Range,      [e ; f] when is_zrarith op -> nonatomic Names.range_nm [e ; f]

      | B.Plus,       [e ; f] -> nonatomic Names.plus_nm [e ; f]
      | B.Minus,      [e ; f] -> nonatomic Names.minus_nm [e ; f]
      | B.Uminus,     [e]     -> nonatomic Names.uminus_nm [e]
      | B.Times,      [e ; f] -> nonatomic Names.times_nm [e ; f]
      | B.Ratio,      [e ; f] -> nonatomic Names.ratio_nm [e ; f]
      | B.Quotient,   [e ; f] -> nonatomic Names.quotient_nm [e ; f]
      | B.Remainder,  [e ; f] -> nonatomic Names.remainder_nm [e ; f]
      | B.Exp,        [e ; f] -> nonatomic Names.exp_nm [e ; f]
      | B.Infinity,   []      -> atomic Names.infinity_nm
      | B.Lteq,       [e ; f] -> nonatomic Names.lteq_nm [e ; f]
      | B.Lt,         [e ; f] -> nonatomic Names.lt_nm [e ; f]
      | B.Gteq,       [e ; f] -> nonatomic Names.gteq_nm [f ; e]
      | B.Gt,         [e ; f] -> nonatomic Names.gt_nm [f ; e]
      | B.Range,      [e ; f] -> nonatomic Names.range_nm [e ; f]

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
      | B.Any,            []      -> atomic Names.uany_nm
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
          let srt = get_sort nm in
          let ncx, nm = adj cx nm in
          Fu.Atm begin fun ff ->
            fprintf ff "@[<hov 2>(@,forall @[<hov 2>(@,(%s %a)@ (%s %a)@]@,)@ %a@]@,)"
            nm pp_print_sort srt
            (primed nm) pp_print_sort srt
            (pp_print_expr ncx) (Sequent { sq with context = hs } @@ oe)
          end
      | Some ({ core = Fresh (nm, _, _, Bounded (b, Visible)) }, hs) ->
          let k = get_kind nm in
          let srt = get_atom (get_ty k) in
          let ncx, nm = adj cx nm in
          Fu.Atm begin fun ff ->
            fprintf ff "@[<hov 2>(@,forall @[<hov 2>(@,(%s %a)@]@,)@ @[<hov 2>(@,=> @[<hov 2>(@,%s@ %s@ %a@]@,)@ %a@]@,)@]@,)"
            nm pp_print_sort srt
            Names.mem_nm nm (pp_print_expr cx) b
            (pp_print_expr ncx) (Sequent { sq with context = hs } @@ oe)
          end
      | Some ({ core = Fresh (nm, _, _, _) }, hs) ->
          let k = get_kind nm in
          let srt = get_atom (get_ty k) in
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
              let srt = get_sort nm in
              let acc_cx, nm = adj acc_cx nm in
              let acc_bs = (nm, srt) :: acc_bs in
              f None acc_cx acc_bs acc_ds bs
          | (nm, _, Domain b) :: bs ->
              let srt = get_sort nm in
              let acc_cx, nm = adj acc_cx nm in
              let acc_bs = (nm, srt) :: acc_bs in
              let acc_ds = (nm, b) :: acc_ds in
              f (Some b) acc_cx acc_bs acc_ds bs
          | (nm, _, Ditto) :: bs ->
              let srt = get_sort nm in
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
        fprintf ff "@[<hov 2>(@,%s@ %s@ %a@]@,)"
        Names.mem_nm nm (pp_print_expr cx) b
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
        fprintf ff "%s" (Names.enum_nm 0)
      end
  | SetEnum es ->
      let n = List.length es in
      Fu.Atm begin fun ff ->
        fprintf ff "@[<hov 2>(@,%s@ %a@]@,)" (Names.enum_nm n)
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
        fprintf ff "@[<hov 2>(%s@ %a@ %a@]@,)"
        Names.fcnapp_nm
        (pp_print_expr cx) e
        (pp_print_expr cx) e1
      end
  | FcnApp (e, es) ->
      let n = List.length es in
      Fu.Atm begin fun ff ->
        fprintf ff "@[<hov 2>(@,%s@ %a@ @[<hov 2>(@,TLA__tuple_%d@ %a@]@,)@]@,)"
        Names.fcnapp_nm
        (pp_print_expr cx) e n
        (pp_print_delimited ~sep:pp_print_space (pp_print_expr cx)) es
      end
  | Arrow (e1, e2) ->
      Fu.Atm begin fun ff ->
        fprintf ff "@[<hov 2>(@,%s@ %a@ %a@]@,)"
        Names.arrow_nm
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
        fprintf ff "@[<hov 2>(@,%s@ %a@ %a@ %a@]@,)"
        Names.fcnexcept_nm
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


(* {3 Preprocessing} *)

(* This very important function does several transformations on the sequent
 * to shape it into something translatable to SMT-LIB. *)
let preprocess ?solver sq =
  let _ = solver in (* FIXME what to do with this? *)

  let sq = Type.Disambiguation.min_reconstruct sq in
  let sq = Reduce.NtCook.cook sq in

  let data = Reduce.NtCollect.collect sq in
  let top = Reduce.NtTable.nt_axiomatize data Deque.empty in
  top, sq


(* {3 Obligation Formatting} *)

let pp_print_assert cx ff e =
  fprintf ff "@[<hov 2>(assert@ %a@]@,)@."
  (pp_print_expr cx) e

let pp_print_declaresort ff nm ar =
  fprintf ff "@[<hov 2>(declare-sort %s %d@])@."
  nm ar

let pp_print_declarefun ff nm ins out =
  fprintf ff "@[<hov 2>(declare-fun %s (%a) %a@])@." nm
  (pp_print_delimited ~sep:pp_print_space pp_print_sort) ins
  pp_print_sort out

let pp_print_obligation ?(solver="CVC4") ff ob =
  (* Shape the sequent into a form that can be translated;
   * Get the top context containing additional declarations and axioms *)
  let top, sq = preprocess ~solver ob.obl.core in

  (* Print preample *)
  pp_print_newline ff ();
  fprintf ff ";; TLA+ Proof Manager %s@." (Params.rawversion ());
  fprintf ff ";; Proof obligation #%d@." (Option.get ob.id);
  fprintf ff ";; Generated from %s@." (Util.location ~cap:false ob.obl);
  pp_print_newline ff ();

  (* Print options *)
  fprintf ff "(set-logic UFNIA)@.";
  pp_print_newline ff ();

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
        let TKind (_, ty) = get_kind nm in (* constant assumed *)
        let srt = get_atom ty in
        let ncx, nm = adj cx nm in
        pp_print_declarefun ff nm [] srt;
        pp_print_newline ff ();
        pp_print_declarefun ff (primed nm) [] srt;
        pp_print_newline ff ();
        spin ncx hs

    | Some ({ core = Fresh (nm, _, _, Bounded (b, Visible)) }, hs) ->
        let TKind (_, ty) = get_kind nm in (* constant op assumed *)
        let ncx, nm = adj cx nm in
        pp_print_declarefun ff nm [] (get_atom ty);
        pp_print_newline ff ();
        pp_print_assert cx ff (
          Apply (Internal B.Mem %% [], [ Opaque nm %% [] ; b ]) %% []);
        pp_print_newline ff ();
        spin ncx hs

    | Some ({ core = Fresh (nm, _, _, _) }, hs) ->
        let TKind (ks, ty) = get_kind nm in
        let ncx, nm = adj cx nm in
        let ins = List.map (fun k -> get_atom (get_ty k)) ks in
        let out = get_atom ty in
        pp_print_declarefun ff nm ins out;
        pp_print_newline ff ();
        spin ncx hs

    | Some ({ core = Defn ({ core = Operator (nm, _) }, _, vis, _) }, hs)
    | Some ({ core = Defn ({ core = Instance (nm, _) }, _, vis, _) }, hs)
    | Some ({ core = Defn ({ core = Recursive (nm, _) }, _, vis, _) }, hs)
    | Some ({ core = Defn ({ core = Bpragma (nm, _, _) }, _, vis, _) }, hs) ->
        let TKind (ks, ty) = get_kind nm in
        let ncx, nm = adj cx nm in
        let ins = List.map (fun k -> get_atom (get_ty k)) ks in
        let out = get_atom ty in
        pp_print_declarefun ff nm ins out;
        pp_print_newline ff ();
        spin ncx hs
  in

  (* Print top context *)
  fprintf ff ";; Top context@.";
  (* FIXME handle this in NtTable in some way *)
  pp_print_newline ff ();
  pp_print_declaresort ff Names.usort_nm 0;
  pp_print_declaresort ff Names.stringsort_nm 0;
  pp_print_newline ff ();
  let cx =
    if Deque.size top = 0 then begin
      pp_print_newline ff ();
      Ctx.dot
    end else
      spin Ctx.dot top
  in

  (* Print hypotheses *)
  fprintf ff ";; Hypotheses@.";
  let cx =
    if Deque.size sq.context = 0 then begin
      pp_print_newline ff ();
      cx
    end else
      spin cx sq.context
  in

  (* Print goal *)
  fprintf ff ";; Goal@.";
  pp_print_assert cx ff (Apply (Internal B.Neg %% [], [sq.active]) %% []);
  pp_print_newline ff ();

  fprintf ff "(check-sat)@.";
  fprintf ff "(exit)@."
