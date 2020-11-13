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
  let mssg = "Backend.Smtlib: " ^ mssg in
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


open Encode.Table
let is_arith op =
  match query op smb_prop with
  | Some smb ->
      begin match get_defn smb with
      | Some ( Plus | Uminus | Minus | Times | Lteq | Lt | Gteq | Gt ) ->
          true
      | _ -> false
      end
  | None -> false


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

  | Opaque s when not (is_arith op) ->
      begin match args with
      | [] ->
          (* FIXME Ad hoc trick that formats primed variables.
           * Would be cleaner to eliminate these beforehand *)
          let s =
            match String.split_on_char '#' s with
            | [ s ; "prime" ] -> primed s
            | _ -> s
          in
          pp_print_string ff s
      | _ ->
          pp_print_sexpr begin fun ff (op, args) ->
            fprintf ff "%s %a" op
            (pp_print_delimited ~sep:pp_print_space (pp_print_expr cx)) args
          end ff (s, args)
      end

  | Opaque _ when is_arith op ->
      let smb = get op smb_prop in
      let s =
        match Option.get (get_defn smb) with
        | Plus -> "+"
        | Uminus | Minus -> "-"
        | Times -> "*"
        | Lteq -> "<="
        | Lt -> "<"
        | Gteq -> ">="
        | Gt -> ">"
        | _ -> error ~at:op "Expected arithmetic operator"
      in
      pp_print_sexpr begin fun ff () ->
        fprintf ff "%s %a" s
        (pp_print_delimited ~sep:pp_print_space (pp_print_expr cx)) args
      end ff ()

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
        | _ -> error ~at:op "Unexpected builtin encountered"
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

  | _ -> error ~at:op "Unexpected operator encountered"

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
      error ~at:oe "Unexpected lambda-abstraction"

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

      | _ -> error ~at:oe "Unsupported sequent expression"
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
      error ~at:oe "Empty LIST expression"

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
              error ~at:oe "Higher-order LET expression"
          | { core = Operator (nm, e) } :: ds ->
              let acc_cx, nm = adj acc_cx nm in
              let acc_vs = (nm, e) :: acc_vs in
              f acc_cx acc_vs ds
          | _ ->
              error ~at:oe "Unsupported LET expression"
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
      error ~at:oe "Incomplete CASE expression encountered"

  | Case ([], _) ->
      error ~at:oe "Empty CASE expression"

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
      error ~at:oe "Unsupported expression"

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
    eprintf "  [DEBUG] %s@.%a@.@." mssg
    pp_print_sequent sq
  in
  let debug mssg sq =
    pp_debug mssg sq;
    sq
  in
  (* FIXME end remove *)

  let sq = sq
    |> Encode.Hints.main
    |> debug "Start" (* FIXME remove *)
    |> Encode.Rewrite.elim_notmem
    |> Encode.Rewrite.elim_multiarg
    |> Encode.Rewrite.elim_tuples
    |> Encode.Rewrite.elim_records
    |> Encode.Rewrite.elim_except
    (* NOTE eliminating bound notation necessary to make all '\in' visible *)
    |> Encode.Rewrite.elim_bounds
    |> debug "Done Simpl." (* FIXME remove *)
    |> Encode.Direct.main
    |> debug "Done Direct"
    |> Encode.Axiomatize.main
    |> debug "Done Axiomatize" (* FIXME remove *)
    |> Encode.Reduce.main
    |> debug "Done Reduce" (* FIXME remove *)
  in
  sq


(* {3 Sort Collection} *)

let collect_sorts sq =
  let srts = Encode.CollectTypes.main sq in
  let srts =
    Ts.fold begin fun srt ->
      Ss.add (ty_to_string srt)
    end srts Ss.empty
  in
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
  let sq =
    try preprocess ~solver ob.Proof.T.obl.core
    with
    | Typechecking_ty (loc, ty0_1, ty0_2) ->
        let loc = Loc.string_of_locus ~cap:true loc in
        eprintf "%s: Typechecking error (0), expected `%a`, found `%a`@."
        loc pp_print_type ty0_1 pp_print_type ty0_2;
        failwith "Typechecking error"
    | Typechecking_ty_arg (loc, ty1_1, ty1_2) ->
        let loc = Loc.string_of_locus ~cap:true loc in
        eprintf "%s: Typechecking error (1), expected `%a`, found `%a`@."
        loc pp_print_targ ty1_1 pp_print_targ ty1_2;
        failwith "Typechecking error"
    | Typechecking_ty_sch (loc, ty2_1, ty2_2) ->
        let loc = Loc.string_of_locus ~cap:true loc in
        eprintf "%s: Typechecking error (2), expected `%a`, found `%a`@."
        loc pp_print_tsch ty2_1 pp_print_tsch ty2_2;
        failwith "Typechecking error"
  in

  (* Print preample *)
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

    | Some ({ core = Fresh (nm, _, _, _) }, hs)
    | Some ({ core = Defn ({ core = Operator (nm, _) }, _, _, _) }, hs)
    | Some ({ core = Defn ({ core = Instance (nm, _) }, _, _, _) }, hs)
    | Some ({ core = Defn ({ core = Recursive (nm, _) }, _, _, _) }, hs)
    | Some ({ core = Defn ({ core = Bpragma (nm, _, _) }, _, _, _) }, hs) ->
        (* The only part of the definition that matters is the declaration.
         * The 'hidden' flag only applies to the definition, so here it does not
         * matter.  Bounds to fresh variables have been removed beforehand. *)
        if not (has nm Props.type_prop) && not (has nm Props.tsch_prop) then
          let ncx = bump cx in
          fprintf ff "; omitted declaration (missing type)@.";
          pp_print_newline ff ();
          spin ncx hs
        else if has nm Props.type_prop then
          let ins = [] in
          let out = get nm Props.type_prop in
          let ncx, nm = adj cx nm in
          pp_print_declarefun ff nm ins out;
          pp_print_newline ff ();
          spin ncx hs
        else
          let TSch (vs, targs, ty) = get nm Props.tsch_prop in
          if vs <> [] then
            let ncx = bump cx in
            fprintf ff "; omitted declaration (polymorphic type)@.";
            pp_print_newline ff ();
            spin ncx hs
          else if List.exists (function TOp _ -> true | TRg _ -> false) targs then
            let ncx = bump cx in
            fprintf ff "; omitted declaration (second-order type)@.";
            pp_print_newline ff ();
            spin ncx hs
          else
            let ins = List.map (function TRg ty -> ty | TOp _ -> error "") targs in
            let out = ty in
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

