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

module B = Builtin

exception Unsupported of string
let unsupp o = raise (Unsupported o)

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

let pp_print_sort ff (t : ty) =
  pp_print_string ff (ty_to_string t)

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
  (* TODO display arithmetic *)
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

      | B.STRING,   []      -> unsupp "STRING"
      | B.BOOLEAN,  []      -> unsupp "BOOLEAN"
      | B.SUBSET,   [e]     -> unsupp "SUBSET"
      | B.UNION,    [e]     -> unsupp "UNION"
      | B.DOMAIN,   [e]     -> unsupp "DOMAIN"
      | B.Subseteq, [e ; f] -> unsupp "Subseteq"
      | B.Mem,      [e ; f] -> unsupp "Mem"
      | B.Notmem,   [e ; f] -> unsupp "Notmem"
      | B.Setminus, [e ; f] -> unsupp "Setminus"
      | B.Cap,      [e ; f] -> unsupp "Cap"
      | B.Cup,      [e ; f] -> unsupp "Cup"

      | B.Leadsto,  [e ; f] -> unsupp "~>"
      | B.ENABLED,  [e]     -> unsupp "ENABLED"
      | B.Cdot,     [e ; f] -> unsupp "\\cdot"
      | B.Actplus,  [e ; f] -> unsupp "-+->"
      | B.Box _,    [e]     -> unsupp "[]"
      | B.Diamond,  [e]     -> unsupp "<>"

      | B.Nat,        []      -> unsupp "Nat"
      | B.Int,        []      -> unsupp "Int"
      | B.Real,       []      -> unsupp "Real"

      | B.Plus,       [e ; f]  -> unsupp "+"
      | B.Minus,      [e ; f]  -> unsupp "-"
      | B.Uminus,     [e]      -> unsupp "-"
      | B.Times,      [e ; f]  -> unsupp "*"
      | B.Ratio,      [e ; f]  -> unsupp "/"
      | B.Quotient,   [e ; f]  -> unsupp "\\div"
      | B.Remainder,  [e ; f]  -> unsupp "%"
      | B.Exp,        [e ; f]  -> unsupp "^"
      | B.Infinity,   []       -> unsupp "Infinity"
      | B.Lteq,       [e ; f]  -> unsupp "<="
      | B.Lt,         [e ; f]  -> unsupp "<"
      | B.Gteq,       [e ; f]  -> unsupp ">="
      | B.Gt,         [e ; f]  -> unsupp ">"
      | B.Range,      [e ; f]  -> unsupp ".."

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
      | B.JavaTime,       []      -> atomic "TLA__JavaTime"
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
          let ty = get_type nm in
          let ncx, nm = adj cx nm in
          Fu.Atm begin fun ff ->
            fprintf ff "@[<hov 2>(@,forall @[<hov 2>(@,(%s %a)@ (%s %a)@]@,)@ %a@]@,)"
            nm pp_print_sort ty
            (primed nm) pp_print_sort ty
            (pp_print_expr ncx) (Sequent { sq with context = hs } @@ oe)
          end
      | Some ({ core = Fresh (nm, _, _, _) }, hs) ->
          let k = get_kind nm in
          let ty = get_ty k in (* NOTE no second-order *)
          let ncx, nm = adj cx nm in
          Fu.Atm begin fun ff ->
            fprintf ff "@[<hov 2>(@,forall @[<hov 2>(@,(%s %a)@]@,)@ %a@]@,)"
            nm pp_print_sort ty
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
      let ncx, bs =
        let rec spin acc_cx acc_bs bs =
          match bs with
          | [] -> (acc_cx, acc_bs)
          | (nm, _, _) :: bs ->
              let ty = get_type nm in
              let acc_cx, nm = adj acc_cx nm in
              let acc_bs = (nm, ty) :: acc_bs in
              spin acc_cx acc_bs bs
        in
        spin cx [] bs
      in
      let bs = List.rev bs in
      let qrep =
        match q with
        | Forall -> "forall"
        | Exists -> "exists"
      in
      Fu.Atm begin fun ff ->
        fprintf ff "@[<hov 2>(@,%s @[<hov 2>(@,%a@]@,) %a@]@,)" qrep
        (pp_print_delimited ~sep:pp_print_space begin fun ff (nm, ty) ->
          fprintf ff "(%s %a)" nm pp_print_sort ty
        end) bs
        (pp_print_expr ncx) e
      end
  | Tquant (Forall, _, _) -> unsupp "\\AA"
  | Tquant (Exists, _, _) -> unsupp "\\EE"
  | Choose _ -> unsupp "CHOOSE"
  | SetSt _ -> unsupp "{ x \\in _ : _ }"
  | SetOf _ -> unsupp "{ _ : x \\in _ }"
  | SetEnum _ -> unsupp "{ _ }"
  | Product _ -> unsupp "_ \\X _"
  | Tuple _ -> unsupp "<< _ >>"
  | Fcn _ -> unsupp "[ x \\in _ |-> _ ]"
  | FcnApp _ -> unsupp "_ [ _ ]"
  | Arrow _ -> unsupp "[ _ -> _ ]"
  | Rect _ -> unsupp "[ _ : _ ]"
  | Record _ -> unsupp "[ _ = _ ]"
  | Except _ -> unsupp "EXCEPT"
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
  | String _ -> unsupp "string literal"
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
  let _ = solver in (* NOTE not used *)

  let sq = Type.Disambiguation.min_reconstruct sq in

  (* FIXME remove below *)
  (*let sq = Reduce.NtCook.cook sq in*)
  (*let data = Reduce.NtCollect.collect sq in*)
  (*let sq = Reduce.NtTable.nt_axiomatize data sq in*)

  let sq = sq
    |> Encode.Canon.main
    |> Encode.Axiomatize.main
    |> Encode.Reduce.main
  in
  sq


(* {3 Sort Collection} *)

let more_type ss h =
  match query_type h with
  | Some ty ->
      Ss.add (ty_to_string ty) ss
  | None ->
      ss (* NOTE ignore absent annotations *)

let more_kind ss h =
  match query_kind h with
  | Some k ->
      let tys = get_types k in
      List.fold_left begin fun ss ty ->
        Ss.add (ty_to_string ty) ss
      end ss tys
  | None ->
      ss

let collect_sorts_visitor = object (self : 'self)
  inherit [unit, Ss.t] Expr.Visit.fold as super

  method expr scx ss oe =
    match oe.core with
    | Lambda (xs, _) ->
        let ss =
          List.fold_left begin fun ss (h, _) ->
            more_type ss h
          end ss xs
        in
        super#expr scx ss oe
    | Tquant (_, xs, _) ->
        let ss = List.fold_left more_type ss xs in
        super#expr scx ss oe
    | Choose (x, _, _) ->
        let ss = more_type ss x in
        super#expr scx ss oe
    | SetSt (x, _, _) ->
        let ss = more_type ss x in
        super#expr scx ss oe
    | _ -> super#expr scx ss oe

  method bounds scx ss bs =
    let ss =
      List.fold_left begin fun ss (h, _, _) ->
        more_type ss h
      end ss bs
    in
    super#bounds scx ss bs

  method defn scx ss df =
    match df.core with
    | Operator (h, { core = Lambda _ }) ->
        let ss = more_kind ss h in
        super#defn scx ss df
    | Operator (h, _) ->
        let ss = more_type ss h in
        super#defn scx ss df
    | _ -> super#defn scx ss df

  method hyp scx ss h =
    match h.core with
    | Fresh (v, Shape_op n, _, _) when n <> 0 ->
        let ss = more_kind ss v in
        super#hyp scx ss h
    | Fresh (v, Shape_expr, _, _) ->
        let ss = more_type ss v in
        super#hyp scx ss h
    | _ -> super#hyp scx ss h

end

let collect_sorts sq =
  let scx = (), Deque.empty in
  let _, srts = collect_sorts_visitor#sequent scx Ss.empty sq in
  Ss.elements srts


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
   * Append a top context containing additional declarations and axioms *)
  let sq = preprocess ~solver ob.obl.core in

  (* Print preample *)
  pp_print_newline ff ();
  fprintf ff ";; TLA+ Proof Manager %s@." (Params.rawversion ());
  fprintf ff ";; Proof obligation #%d@." (Option.get ob.id);
  fprintf ff ";; Generated from %s@." (Util.location ~cap:false ob.obl);
  pp_print_newline ff ();

  (* Print options *)
  fprintf ff "(set-logic UFNIA)@.";
  pp_print_newline ff ();

  (* Print sorts *)
  fprintf ff ";; Sorts@.";
  pp_print_newline ff ();
  let srts = collect_sorts sq in
  List.iter begin fun s ->
    pp_print_declaresort ff s 0
  end srts;
  pp_print_newline ff ();

  (* Print hypotheses *)
  fprintf ff ";; Hypotheses@.";

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
        let ncx, nm = adj cx nm in
        pp_print_declarefun ff nm [] ty;
        pp_print_newline ff ();
        pp_print_declarefun ff (primed nm) [] ty;
        pp_print_newline ff ();
        spin ncx hs

    | Some ({ core = Fresh (nm, _, _, _) }, hs) ->
        let TKind (ks, ty) = get_kind nm in
        let ncx, nm = adj cx nm in
        let ins = List.map (fun k -> get_ty k) ks in
        let out = ty in
        pp_print_declarefun ff nm ins out;
        pp_print_newline ff ();
        spin ncx hs

    | Some ({ core = Defn ({ core = Operator (nm, _) }, _, vis, _) }, hs)
    | Some ({ core = Defn ({ core = Instance (nm, _) }, _, vis, _) }, hs)
    | Some ({ core = Defn ({ core = Recursive (nm, _) }, _, vis, _) }, hs)
    | Some ({ core = Defn ({ core = Bpragma (nm, _, _) }, _, vis, _) }, hs) ->
        let TKind (ks, ty) = get_kind nm in
        let ncx, nm = adj cx nm in
        let ins = List.map (fun k -> get_ty k) ks in
        let out = ty in
        pp_print_declarefun ff nm ins out;
        pp_print_newline ff ();
        spin ncx hs
  in

  pp_print_newline ff ();
  let cx =
    if Deque.size sq.context = 0 then begin
      pp_print_newline ff ();
      Ctx.dot
    end else
      spin Ctx.dot sq.context
  in

  (* Print goal *)
  fprintf ff ";; Goal@.";
  pp_print_assert cx ff (Apply (Internal B.Neg %% [], [sq.active]) %% []);
  pp_print_newline ff ();

  fprintf ff "(check-sat)@.";
  fprintf ff "(exit)@."
