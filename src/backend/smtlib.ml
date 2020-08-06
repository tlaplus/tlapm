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
open Tla_parser

open Expr.T
open Type.T
open Util.Coll

module B = Builtin

let error ?at mssg =
  Errors.bug ?at mssg

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

let pp_print_sexpr fmt ff v =
  fprintf ff "@[<hov 2>(%a@])" fmt v

let pp_print_sort ff ty =
  pp_print_string ff (ty_to_string ty)

let pp_print_binding ff (nm, ty) =
  fprintf ff "(%s %a)" nm pp_print_sort ty

let rec pp_apply cx ff op args =
  match op.core with
  | Ix n ->
      let id = lookup_id cx n in
      begin match args with
      | [] ->
          pp_print_string ff id
      | _ ->
          pp_print_sexpr begin fun ff (op, args) ->
            fprintf ff "%s %a" op
            (pp_print_delimited ~sep:pp_print_space (pp_print_expr cx)) args
          end ff (id, args)
      end

  (* TODO display arithmetic *)

  | Opaque s ->
      begin match args with
      | [] ->
          pp_print_string ff s
      | _ ->
          pp_print_sexpr begin fun ff (op, args) ->
            fprintf ff "%s %a" op
            (pp_print_delimited ~sep:pp_print_space (pp_print_expr cx)) args
          end ff (s, args)
      end

  | Internal b ->
      let kw =
        (* NOTE It is expected that all non-boolean builtins
         * are encoded away at this point *)
        match b with
        | B.TRUE    -> "true"
        | B.FALSE   -> "false"
        | B.Implies -> "=>"
        | B.Equiv   -> "="
        | B.Conj    -> "and"
        | B.Disj    -> "or"
        | B.Neg     -> "not"
        | B.Eq      -> "="
        | B.Neq     -> "distinct"
        | _ -> error ~at:op "Backend.Smtlib.pp_apply: \
                             unexpected builtin encountered"
      in
      begin match args with
      | [] ->
          pp_print_string ff kw
      | _ ->
          pp_print_sexpr begin fun ff (op, args) ->
            fprintf ff "%s %a" op
            (pp_print_delimited ~sep:pp_print_space (pp_print_expr cx)) args
          end ff (kw, args)
      end

  | _ -> error ~at:op "Backend.Smtlib.pp_apply: \
                       unexpected operator encountered"

and fmt_expr cx oe =
  if has oe pattern_prop then
    Fu.Atm (fun ff ->
      let pats = get oe pattern_prop in
      let pp_print_pat ff es =
        fprintf ff ":pattern %a"
        (pp_print_sexpr (
          pp_print_delimited ~sep:pp_print_space (pp_print_expr cx))
        ) es
      in
      pp_print_sexpr begin fun ff () ->
        fprintf ff "! %a@ %a"
        (pp_print_expr cx) (remove_patterns oe)
        (pp_print_delimited ~sep:pp_print_space pp_print_pat) pats
      end ff ())
  else
  match oe.core with
  | Ix _ | Opaque _ | Internal _ ->
      Fu.Atm (fun ff -> pp_apply cx ff oe [])

  | Lambda _ ->
      error ~at:oe "Backend.Smtlib.fmt_expr: \
                    unexpected lambda-abstraction"

  | Apply (op, args) ->
      Fu.Atm (fun ff -> pp_apply cx ff op args)

  | Sequent sq ->
      begin match Deque.front sq.context with
      | None -> fmt_expr cx sq.active

      | Some ({ core = Fact (e, Visible, _)}, hs) ->
          let ncx = bump cx in
          Fu.Atm begin fun ff ->
            pp_print_sexpr begin fun ff (e1, e2) ->
              fprintf ff "=> %a@ %a"
              (pp_print_expr cx) e1
              (pp_print_expr ncx) e2
            end ff (e, Sequent { sq with context = hs } @@ oe)
          end

      | Some ({ core = Fact (e, Hidden, _)}, hs) ->
          let ncx = bump cx in
          fmt_expr ncx (Sequent { sq with context = hs } @@ oe)

      | Some ({ core = Flex nm }, hs) ->
          let ty = get_type nm in
          let ncx, nm = adj cx nm in
          Fu.Atm begin fun ff ->
            pp_print_sexpr begin fun ff (nm, ty, e) ->
              fprintf ff "forall %a %a"
              (pp_print_sexpr begin fun ff (nm, ty) ->
                fprintf ff "%a %a"
                pp_print_binding (nm, ty)
                pp_print_binding (primed nm, ty)
              end) (nm, ty)
              (pp_print_expr ncx) e
            end ff (nm, ty, Sequent { sq with context = hs } @@ oe)
          end

      | Some ({ core = Fresh (nm, _, _, _) }, hs) ->
          (* NOTE Second-order quantification rejected *)
          let ty = get_type nm in
          let ncx, nm = adj cx nm in
          Fu.Atm begin fun ff ->
            pp_print_sexpr begin fun ff (nm, ty, e) ->
              fprintf ff "forall %a %a"
              (pp_print_sexpr pp_print_binding) (nm, ty)
              (pp_print_expr ncx) e
            end ff (nm, ty, Sequent { sq with context = hs } @@ oe)
          end

      | _ -> error ~at:oe "Backend.Smtlib.fmt_expr: \
                           unsupported sequent expression"
      end

  | With (e, _) ->
      fmt_expr cx e

  | If (e, f, g) ->
      Fu.Atm begin fun ff ->
        pp_print_sexpr begin fun ff (e, f, g) ->
          fprintf ff "ite %a %a %a"
          (pp_print_expr cx) e
          (pp_print_expr cx) f
          (pp_print_expr cx) g
        end ff (e, f, g)
      end

  | List (Refs, []) ->
      error ~at:oe "Backend.Smtlib.fmt_expr: \
                    empty LIST expression"

  | List (Refs, [e]) ->
      fmt_expr cx e

  | List (q, es) ->
      let op =
        match q with
        | And | Refs -> "and"
        | Or -> "or"
      in
      Fu.Atm begin fun ff ->
        pp_print_sexpr begin fun ff (op, es) ->
          fprintf ff "%s %a" op
          (pp_print_delimited ~sep:pp_print_space (pp_print_expr cx)) es
        end ff (op, es)
      end

  | Let ([], e) ->
      fmt_expr cx e

  | Let (ds, e) ->
      let ncx, vs =
        let rec f acc_cx acc_vs ds =
          match ds with
          | [] -> (acc_cx, acc_vs)
          | { core = Operator (_, { core = Lambda _ }) } :: _ ->
              error ~at:oe "Backend.Smtlib.fmt_expr: \
                            higher-order LET expression"
          | { core = Operator (nm, e) } :: ds ->
              let acc_cx, nm = adj acc_cx nm in
              let acc_vs = (nm, e) :: acc_vs in
              f acc_cx acc_vs ds
          | _ ->
              error ~at:oe "Backend.Smtlib.fmt_expr: \
                            unsupported LET expression"
        in
        f cx [] ds
      in
      let pp_print_vbind cx ff (nm, e) =
        fprintf ff "(%s %a)" nm
        (pp_print_expr cx) e
      in
      Fu.Atm begin fun ff ->
        pp_print_sexpr begin fun ff (vs, e) ->
          fprintf ff "let %a@ %a"
          (pp_print_sexpr (
            pp_print_delimited ~sep:pp_print_space (pp_print_vbind cx))) vs
          (pp_print_expr ncx) e
        end ff (vs, e)
      end

  | Quant (_, [], e) ->
      fmt_expr cx e

  | Quant (q, bs, e) ->
      let ncx, rbs =
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
      let bs = List.rev rbs in
      let qrep =
        match q with
        | Forall -> "forall"
        | Exists -> "exists"
      in
      Fu.Atm begin fun ff ->
        pp_print_sexpr begin fun ff (bs, e) ->
          fprintf ff "%s %a %a" qrep
          (pp_print_sexpr (
            pp_print_delimited ~sep:pp_print_space pp_print_binding)) bs
          (pp_print_expr ncx) e
        end ff (bs, e)
      end

  | Case (_, None) ->
      error ~at:oe "Backend.Smtlib.fmt_expr: \
                    incomplete CASE expression encountered"

  | Case ([], _) ->
      error ~at:oe "Backend.Smtlib.fmt_expr: \
                    empty CASE expression"

  | Case ([ (e1, e2) ], Some e3) ->
      fmt_expr cx (If (e1, e2, e3) @@ oe)

  | Case ((e1, e2) :: ps, Some o) ->
      fmt_expr cx (If (e1, e2, Case (ps, Some o) %% []) @@ oe)

  | Num (m, "") ->
      Fu.Atm begin fun ff ->
        fprintf ff "%s" m
      end

  | Num (m, n) ->
      Fu.Atm begin fun ff ->
        fprintf ff "%s.%s" m n
      end

  | Parens (e, _) ->
      fmt_expr cx e

  | _ ->
      error ~at:oe "Backend.Smtlib.fmt_expr: \
                    unsupported expression"

and pp_print_expr cx ff e =
  Fu.pp_print_minimal ff (fmt_expr cx e)


(* {3 Preprocessing} *)

(* This very important function does several transformations on the sequent
 * to shape it into something translatable to SMT-LIB. *)
let preprocess ?solver sq =
  let _ = solver in (* NOTE not used *)

  (*let sq = Type.Disambiguation.min_reconstruct sq in*)

  (* FIXME remove below *)
  (*let sq = Reduce.NtCook.cook sq in*)
  (*let data = Reduce.NtCollect.collect sq in*)
  (*let sq = Reduce.NtTable.nt_axiomatize data sq in*)

  (* FIXME remove *)
  let emp = (Deque.empty, Ctx.dot) in
  let pp_print_sequent ff sq = ignore (Expr.Fmt.pp_print_sequent emp ff sq) in

  let pp_debug mssg sq =
    fprintf err_formatter "  [DEBUG] %s@.%a@.@." mssg
    pp_print_sequent sq
  in
  let debug mssg sq =
    pp_debug mssg sq;
    sq
  in
  (* FIXME end remove *)

  let sq = sq
    |> debug "Start" (* FIXME remove *)
    (*|> Encode.Canon.main*)
    (*|> debug "After Canon" (* FIXME remove *)*)
    (* NOTE eliminating bound notation necessary to make all '\in' visible *)
    |> Encode.Rewrite.simpl_elims
    |> Encode.Rewrite.simpl_bounds
    |> debug "Done Simpl. Bounds" (* FIXME remove *)
    |> Encode.Direct.main
    |> debug "Done Direct"
    |> Encode.Axiomatize.main
    |> debug "Done Axiomatize" (* FIXME remove *)
    |> Encode.Reduce.main
    |> debug "Done Reduce" (* FIXME remove *)
  in
  sq


(* {3 Sort Collection} *)

let add_ty ss ty =
  Ss.add (ty_to_string ty) ss

let more_type ss h =
  match query h Props.type_prop with
  | Some ty ->
      add_ty ss ty
  | None ->
      ss (* NOTE ignore absent annotations *)

let add_from_targ ss = function
  | TRg ty ->
      add_ty ss ty
  | TOp (tys, ty) ->
      List.fold_left add_ty ss (ty :: tys)

let more_targ ss h =
  match query h Props.targ_prop with
  | Some targ ->
      add_from_targ ss targ
  | None ->
      ss

let add_from_tsch ss = function
  | TSch ([], targs, ty) ->
      List.fold_left add_from_targ (add_ty ss ty) targs
  | TSch (_ :: _, _, _) ->
      ss (* NOTE ignore polymorphic schemes *)

let more_tsch ss h =
  match query h Props.tsch_prop with
  | Some tsch ->
      add_from_tsch ss tsch
  | None ->
      ss

let collect_sorts_visitor = object (self : 'self)
  inherit [unit, Ss.t] Expr.Visit.fold as super

  method expr scx ss oe =
    match oe.core with
    | Lambda (xs, _) ->
        let ss =
          List.fold_left begin fun ss (h, _) ->
            (* NOTE lambdas as expressions are first-order, so
             * all annotations are expected to be types *)
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
        let ss = more_tsch ss h in
        super#defn scx ss df
    | Operator (h, _) ->
        let ss = more_type ss h in
        super#defn scx ss df
    | _ -> super#defn scx ss df

  method hyp scx ss h =
    match h.core with
    | Fresh (v, Shape_op n, _, _) when n <> 0 ->
        let ss = more_tsch ss v in
        super#hyp scx ss h
    | Fresh (v, Shape_expr, _, _) ->
        let ss = more_type ss v in
        super#hyp scx ss h
    | Flex v ->
        let ss = more_type ss v in
        super#hyp scx ss h
    | _ -> super#hyp scx ss h

end

let collect_sorts sq =
  let scx = (), Deque.empty in
  let _, srts = collect_sorts_visitor#sequent scx Ss.empty sq in
  let srts = Ss.diff srts (Ss.of_list [
    "Bool" ; "Int" ; "Real"
  ]) in
  Ss.elements srts


(* {3 Obligation Formatting} *)

let pp_print_assert cx ff e =
  pp_print_sexpr begin fun ff () ->
    fprintf ff "assert %a"
    (pp_print_expr cx) e
  end ff ();
  pp_print_newline ff ()

let pp_print_declaresort ff nm ar =
  pp_print_sexpr begin fun ff () ->
    fprintf ff "declare-sort %s %d"
    nm ar
  end ff ();
  pp_print_newline ff ()

let pp_print_declarefun ff nm ins out =
  pp_print_sexpr begin fun ff () ->
    fprintf ff "declare-fun %s (%a) %a" nm
    (pp_print_delimited ~sep:pp_print_space pp_print_sort) ins
    pp_print_sort out
  end ff ();
  pp_print_newline ff ()

let pp_print_obligation ?(solver="CVC4") ff ob =
  (* Shape the sequent into a form that can be translated;
   * Append a top context containing additional declarations and axioms *)
  let sq = preprocess ~solver ob.Proof.T.obl.core in

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
        let ty = get nm Props.type_prop in
        let ncx, nm = adj cx nm in
        pp_print_declarefun ff nm [] ty;
        pp_print_newline ff ();
        pp_print_declarefun ff (primed nm) [] ty;
        pp_print_newline ff ();
        spin ncx hs

    | Some ({ core = Fresh (nm, _, _, _) }, hs) ->
        let ins, out =
          if has nm Props.type_prop then
            ([], get nm Props.type_prop)
          else if has nm Props.tsch_prop then
            match get nm Props.tsch_prop with
            | TSch ([], targs, ty) ->
                let ins =
                  List.map begin function
                    | TRg ty -> ty
                    | TOp _ -> error ~at:nm "Backend.Smtlib.pp_print_obligation: \
                                             Unsupported second-order declaration"
                  end targs
                in
                (ins, ty)
            | _ -> error ~at:nm "Backend.Smtlib.pp_print_obligation: \
                                 Polymorphic type scheme on declaration"
          else
            error ~at:nm ("Backend.Smtlib.pp_print_obligation: \
                          Missing type annotation on declaration '"
                          ^ nm.core ^ "'")
        in
        let ncx, nm = adj cx nm in
        pp_print_declarefun ff nm ins out;
        pp_print_newline ff ();
        spin ncx hs

    | Some ({ core = Defn ({ core = Operator (nm, _) }, _, vis, _) }, hs)
    | Some ({ core = Defn ({ core = Instance (nm, _) }, _, vis, _) }, hs)
    | Some ({ core = Defn ({ core = Recursive (nm, _) }, _, vis, _) }, hs)
    | Some ({ core = Defn ({ core = Bpragma (nm, _, _) }, _, vis, _) }, hs) ->
        let ins, out =
          if has nm Props.type_prop then
            ([], get nm Props.type_prop)
          else if has nm Props.tsch_prop then
            match get nm Props.tsch_prop with
            | TSch ([], targs, ty) ->
                let ins =
                  List.map begin function
                    | TRg ty -> ty
                    | TOp _ -> error ~at:nm "Backend.Smtlib.pp_print_obligation: \
                                             Unsupported second-order declaration"
                  end targs
                in
                (ins, ty)
            | _ -> error ~at:nm "Backend.Smtlib.pp_print_obligation: \
                                 Polymorphic type scheme on declaration"
          else
            error ~at:nm "Backend.Smtlib.pp_print_obligation: \
                          Missing type annotation on declaration"
        in
        let ncx, nm = adj cx nm in
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

