(*
 * backend/smtlib.ml --- direct translation to SMT-LIB
 *
 *
 * Copyright (C) 2022  INRIA and Microsoft Corporation
 *)

open Format

open Ext
open Property
open Fmtutil
open Tla_parser

open Expr.T
open Type.T
open Util.Coll

module Smb = Encode.Smb
module T = Encode.Table
module B = Builtin

let (@@@) = Stdlib.(@@)

let error ?at mssg =
  let mssg = "Backend.Smtlib: " ^ mssg in
  (*Errors.bug ?at mssg*)
  failwith mssg

let primed s = s ^ "__prime"


(* {3 Context} *)

let repls =
  [ '_',  "__" (* keep the tempfiles readable *)
  ; '\\', "backslash_"
  ; '+',  "plussign_"
  ; '-',  "hyphen_"
  ; '*',  "asterisk_"
  ; '/',  "slash_"
  ; '%',  "percentsign_"
  ; '^',  "circumflexaccent_"
  ; '&',  "ampersand_"
  ; '@',  "atsign_"
  ; '#',  "pound_"
  ; '$',  "dollarsign_"
  ; '(',  "leftparenthesis_"
  ; ')',  "rightparenthesis_"
  ; '|',  "verticalbar_"
  ; '.',  "period_"
  ; ':',  "colon_"
  ; '?',  "questionmark_"
  ; '!',  "exclamationmark_"
  ; '<',  "lessthansign_"
  ; '>',  "greaterthansign_"
  ; '=',  "equalsign_"
  ; ' ',  "space_"
  ]

let escaped =
  List.fold_right begin fun (c, repl) ->
    let rgx = Str.regexp (Str.quote (String.make 1 c)) in
    Str.global_replace rgx repl
  end repls

let format_smt s =
  "smt__" ^ escaped s

let adj cx v =
  let nm = format_smt v.core in
  let cx = Ctx.push cx nm in
  (cx, Ctx.string_of_ident (Ctx.front cx))

let bump cx =
  fst (adj cx ("" %% []))

let lookup_id cx n =
  Ctx.string_of_ident (fst (Ctx.index cx n))

let quoted_symbol s =
  "|" ^ s ^ "|"


(* {3 Expression Formatting} *)

let pp_box fmt ff x =
  fprintf ff "@[<hov 0>%a@]" fmt x

let pp_print_sexpr fmt ff v =
  fprintf ff "@[<hov 2>(%a@])" fmt v

let rec pp_print_sort ff ty =
  begin match ty with
  | TAtm TABol -> pp_print_string ff "Bool"
  | TAtm TAInt -> pp_print_string ff "Int"
  | _ -> pp_print_string ff (ty_to_string ty)
  end

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
            fprintf ff "%s@ %a" op
            (pp_print_delimited ~sep:pp_print_space (pp_box @@@ pp_print_expr cx)) args
          end ff (id, args)
      end

  | Opaque s when has op Smb.smb_prop ->
      (* The symbols that are left correspond to native operators of SMB-LIB *)
      let smb = get op Smb.smb_prop in
      begin match Smb.get_defn smb, args with
      | T.TIntLit n,      [] ->
          pp_print_int ff n
      | T.TIntPlus,       [ e ; f ] ->
          pp_print_sexpr begin fun ff (e, f) ->
            fprintf ff "+@ %a@ %a"
            (pp_box @@@ pp_print_expr cx) e
            (pp_box @@@ pp_print_expr cx) f
          end ff (e, f)
      | T.TIntUminus,     [ e ] ->
          pp_print_sexpr begin fun ff e ->
            fprintf ff "-@ %a"
            (pp_box @@@ pp_print_expr cx) e
          end ff e
      | T.TIntMinus,      [ e ; f ] ->
          pp_print_sexpr begin fun ff (e, f) ->
            fprintf ff "-@ %a@ %a"
            (pp_box @@@ pp_print_expr cx) e
            (pp_box @@@ pp_print_expr cx) f
          end ff (e, f)
      | T.TIntTimes,      [ e ; f ] ->
          pp_print_sexpr begin fun ff (e, f) ->
            fprintf ff "*@ %a@ %a"
            (pp_box @@@ pp_print_expr cx) e
            (pp_box @@@ pp_print_expr cx) f
          end ff (e, f)
      | T.TIntQuotient,   [ e ; f ] ->
          pp_print_sexpr begin fun ff (e, f) ->
            fprintf ff "div@ %a@ %a"
            (pp_box @@@ pp_print_expr cx) e
            (pp_box @@@ pp_print_expr cx) f
          end ff (e, f)
      | T.TIntRemainder,  [ e ; f ] ->
          pp_print_sexpr begin fun ff (e, f) ->
            fprintf ff "mod@ %a@ %a"
            (pp_box @@@ pp_print_expr cx) e
            (pp_box @@@ pp_print_expr cx) f
          end ff (e, f)
      | T.TIntLteq,       [ e ; f ] ->
          pp_print_sexpr begin fun ff (e, f) ->
            fprintf ff "<=@ %a@ %a"
            (pp_box @@@ pp_print_expr cx) e
            (pp_box @@@ pp_print_expr cx) f
          end ff (e, f)
      | T.TIntLt,         [ e ; f ] ->
          pp_print_sexpr begin fun ff (e, f) ->
            fprintf ff "<@ %a@ %a"
            (pp_box @@@ pp_print_expr cx) e
            (pp_box @@@ pp_print_expr cx) f
          end ff (e, f)
      | T.TIntGteq,       [ e ; f ] ->
          pp_print_sexpr begin fun ff (e, f) ->
            fprintf ff ">=@ %a@ %a"
            (pp_box @@@ pp_print_expr cx) e
            (pp_box @@@ pp_print_expr cx) f
          end ff (e, f)
      | T.TIntGt,         [ e ; f ] ->
          pp_print_sexpr begin fun ff (e, f) ->
            fprintf ff ">@ %a@ %a"
            (pp_box @@@ pp_print_expr cx) e
            (pp_box @@@ pp_print_expr cx) f
          end ff (e, f)
      | _, _ ->
          (* assuming arity is always correct *)
          let mssg = "unknown native operator '" ^ Smb.get_name smb ^ "'" in
          error ~at:op mssg
      end

  | Opaque s ->
      begin match args with
      | [] ->
          (* FIXME This code formats primed variables.
           * Would be cleaner to eliminate these beforehand *)
          let s =
            match String.split_on_char '#' s with
            | [ s ; "prime" ] -> primed (format_smt s)
            | _ -> s
          in
          pp_print_string ff (format_smt s)
      | _ ->
          pp_print_sexpr begin fun ff (op, args) ->
            fprintf ff "%s@ %a" op
            (pp_print_delimited ~sep:pp_print_space (pp_box @@@ pp_print_expr cx)) args
          end ff (s, args)
      end

  | Internal b ->
      let kw =
        (* All non-boolean builtins should be encoded away at this point *)
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
        | _ ->
            let mssg = "Unexpected builtin encountered '" ^ B.builtin_to_string b ^ "'" in
            error ~at:op mssg
      in
      begin match args with
      | [] ->
          pp_print_string ff kw
      | _ ->
          pp_print_sexpr begin fun ff (op, args) ->
            fprintf ff "%s@ %a" op
            (pp_print_delimited ~sep:pp_print_space (pp_box @@@ pp_print_expr cx)) args
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
          pp_print_delimited ~sep:pp_print_space (pp_box @@@ pp_print_expr cx))
        ) es
      in
      pp_print_sexpr begin fun ff () ->
        fprintf ff "!@ %a@ %a"
        (pp_box @@@ pp_print_expr cx) (remove_pats oe)
        (pp_print_delimited ~sep:pp_print_space pp_print_pat) pats
      end ff ())
  else
  match oe.core with
  | Ix _ | Opaque _ | Internal _ ->
      Fu.Atm (fun ff -> pp_apply cx ff oe [])

  | Lambda ([], e) ->
      fmt_expr cx e
  | Lambda _ ->
      let mssg = "Unexpected lambda-abstraction" in
      error ~at:oe mssg

  | Apply ({ core = Internal B.Unprimable }, [ e ]) ->
      fmt_expr cx e

  | Apply (op, args) ->
      Fu.Atm (fun ff -> pp_apply cx ff op args)

  | Sequent sq ->
      begin match Deque.front sq.context with
      | None -> fmt_expr cx sq.active

      | Some ({ core = Fact (e, Visible, _)}, hs) ->
          let ncx = bump cx in
          Fu.Atm begin fun ff ->
            pp_print_sexpr begin fun ff (e1, e2) ->
              fprintf ff "=>@ %a@ %a"
              (pp_box @@@ pp_print_expr cx) e1
              (pp_box @@@ pp_print_expr ncx) e2
            end ff (e, Sequent { sq with context = hs } @@ oe)
          end

      | Some ({ core = Fact (e, Hidden, _)}, hs) ->
          let ncx = bump cx in
          fmt_expr ncx (Sequent { sq with context = hs } @@ oe)

      | Some ({ core = Flex nm }, hs) ->
          error ~at:oe "Nested variable declaration not supported"

      | Some ({ core = Fresh (nm, _, _, _) }, hs) ->
          (* NOTE Second-order quantification rejected *)
          let ty = get nm Props.ty0_prop in
          let ncx, nm = adj cx nm in
          Fu.Atm begin fun ff ->
            pp_print_sexpr begin fun ff (nm, ty, e) ->
              fprintf ff "forall@ %a@ %a"
              (pp_print_sexpr pp_print_binding) (nm, ty)
              (pp_box @@@ pp_print_expr ncx) e
            end ff (nm, ty, Sequent { sq with context = hs } @@ oe)
          end

      | _ -> error ~at:oe "Unsupported sequent expression"
      end

  | With (e, _) ->
      fmt_expr cx e

  | If (e, f, g) ->
      Fu.Atm begin fun ff ->
        pp_print_sexpr begin fun ff (e, f, g) ->
          fprintf ff "ite@ %a@ %a@ %a"
          (pp_box @@@ pp_print_expr cx) e
          (pp_box @@@ pp_print_expr cx) f
          (pp_box @@@ pp_print_expr cx) g
        end ff (e, f, g)
      end

  | List (Refs, []) ->
      error ~at:oe "Empty LIST expression"

  | List (q, [e]) ->
      fmt_expr cx e

  | List (q, es) ->
      let op =
        match q with
        | And | Refs -> "and"
        | Or -> "or"
      in
      Fu.Atm begin fun ff ->
        pp_print_sexpr begin fun ff (op, es) ->
          fprintf ff "%s@ %a" op
          (pp_print_delimited ~sep:pp_print_space (pp_box @@@ pp_print_expr cx)) es
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
          (pp_box @@@ pp_print_expr ncx) e
        end ff (vs, e)
      end

  | Quant (q, bs, e) ->
      let ncx, rbs =
        let rec spin acc_cx acc_bs bs =
          match bs with
          | [] -> (acc_cx, acc_bs)
          | (nm, _, _) :: bs ->
              let ty = get nm Props.ty0_prop in
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
          fprintf ff "%s@ %a@ %a" qrep
          (pp_print_sexpr (
            pp_print_delimited ~sep:pp_print_space pp_print_binding)) bs
          (pp_box @@@ pp_print_expr ncx) e
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

  | Parens (e, _) ->
      fmt_expr cx e

  | _ ->
      error ~at:oe "Unsupported expression"

and pp_print_expr cx ff e =
  Fu.pp_print_minimal ff (fmt_expr cx e)


(* {3 Preprocessing} *)

(* This very important function applies several transformations to the sequent
 * to shape it into something translatable to SMT-LIB. *)
let preprocess ~solver sq =

  let cx = (Deque.empty, Ctx.dot) in
  let pp_print_sequent ff sq = ignore (Expr.Fmt.pp_print_sequent cx ff sq) in

  let debug mssg sq =
    if (Params.debugging "verbose") then begin
      eprintf "  [DEBUG] %s@.%a@.@." mssg
      pp_print_sequent sq
    end;
    sq
  in

  (* The "smarter_types" debug flag will activate elementary type inference to
     translate integer expressions more efficiently for SMT. *)

  let disable_arithmetic = Params.debugging "disable_arithmetic" in
  let smarter_types = Params.debugging "smarter_types" in

  let typelvl =
         if disable_arithmetic  then 0
    else if smarter_types       then 2
    else 1
  in

  let rwlvl =
         if Params.debugging "rw+"      then 3
    else if Params.debugging "rw"       then 2
    else if Params.debugging "rwsetext" then 1
    else 0
  in

  let smt_set_extensionality = not (Params.debugging "no_smt_set_extensionality") in

  let sq = sq
    |> debug "Original Obligation:"
    |> Encode.Rewrite.elim_flex
    |> Type.Synthesize.main ~typelvl
    |> Encode.Rewrite.elim_notmem
    |> Encode.Rewrite.elim_compare
    |> Encode.Rewrite.elim_multiarg
    |> Encode.Rewrite.elim_bounds (* make all '\in' visible *)
    |> Encode.Rewrite.sort_recfields
    |> Encode.Rewrite.simplify_sets ~rwlvl ~disable_arithmetic
    |> debug "Disambiguate and Simplify:"
    |> Encode.Standardize.main ~smt_set_extensionality
    |> debug "Standardize:"
    |> Encode.Axiomatize.main ~solver ~disable_arithmetic ~smt_set_extensionality
    |> debug "Axiomatize:"
    |> Encode.Flatten.main
    |> debug "Flatten:"
  in
  sq


(* {3 Sort Collection} *)

let collect_sorts sq =
  let srts = Type.Collect.main sq in
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

let pp_print_assert ?meta cx ff e =
    match meta with
    | None ->
        pp_print_sexpr begin fun ff () ->
          fprintf ff "assert@ %a"
          (pp_box @@@ pp_print_expr cx) e
        end ff ();
        pp_print_newline ff ()
    | Some m ->
        fprintf ff ";; %s"
        begin match m.hkind with
        | Axiom -> "Axiom: " ^ m.name
        | Hypothesis -> "Hypothesis: " ^ m.name
        | Goal -> "Goal"
        end;
        pp_print_newline ff ();
        pp_print_sexpr begin fun ff () ->
          fprintf ff "assert@ %a"
          begin pp_box @@@ pp_print_sexpr
            begin fun ff e ->
              fprintf ff "!@ %a@ :named %s"
              (pp_box @@@ pp_print_expr cx) e
              (*("name__" ^ format_smt m.name)*)
              (quoted_symbol m.name)
            end
          end e
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

let pp_print_obligation ?(solver="SMT") ff ob =
  (* Shape the sequent into a form that can be translated;
   * Append a top context containing additional declarations and axioms *)
  let sq = preprocess ~solver ob.Proof.T.obl.core in

  (* Print preample *)
  fprintf ff ";; TLA+ Proof Manager %s@." (Params.rawversion ());
  fprintf ff ";; Proof obligation #%d@." (Option.get ob.id);
  fprintf ff ";; Generated from %s@." (Util.location ~cap:false ob.obl);
  pp_print_newline ff ();

  (* Print options *)
  let logic =
    if Params.debugging "disable_arithmetic" then "UF"
    else if solver = "veriT" then "UFLIA"
    else !Params.smt_logic (* default: UFNIA *)
  in
  fprintf ff "(set-logic %s)@." logic;
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

  let is_sndord_fact e =
    match e.core with
    | Sequent sq ->
        Option.is_some begin
          Deque.find sq.context begin fun h ->
            match h.core with
            | Fresh (_, Shape_op n, _, _) when n > 0 ->
                true
            | _ ->
                false
          end
        end
    | _ ->
        false
  in

  let rec spin cx hs =
    match Deque.front hs with
    | None ->
        cx

    | Some ({ core = Fact (e, vis, _) }, hs) ->
        let ncx = bump cx in
        begin if vis = Hidden then
          fprintf ff "; hidden fact@."
        else if is_sndord_fact e then
          fprintf ff "; omitted fact (second-order)@."
        else
          pp_print_assert ?meta:(query e meta_prop) cx ff e
        end;
        pp_print_newline ff ();
        spin ncx hs

    | Some ({ core = Flex nm }, hs) ->
        let ty = get nm Props.ty0_prop in
        let ncx, nm = adj cx nm in
        pp_print_declarefun ff nm [] ty;
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
        if has nm Props.ty0_prop then
          let ins = [] in
          let out = get nm Props.ty0_prop in
          let ncx, nm = adj cx nm in
          pp_print_declarefun ff nm ins out;
          pp_print_newline ff ();
          spin ncx hs

        else if has nm Props.ty1_prop then
          let Ty1 (ins, out) = get nm Props.ty1_prop in
          let ncx, nm = adj cx nm in
          pp_print_declarefun ff nm ins out;
          pp_print_newline ff ();
          spin ncx hs

        else if has nm Props.ty2_prop then
          let ty2 = get nm Props.ty2_prop in
          begin match safe_downcast_ty1 ty2 with
          | None ->
              let ncx = bump cx in
              fprintf ff "; omitted declaration of '%s' (second-order)@." nm.core;
              pp_print_newline ff ();
              spin ncx hs
          | Some (Ty1 (ins, out)) ->
              let ncx, nm = adj cx nm in
              pp_print_declarefun ff nm ins out;
              pp_print_newline ff ();
              spin ncx hs
          end

        else
          let ncx = bump cx in
          fprintf ff "; omitted declaration of '%s' (missing type)@." nm.core;
          pp_print_newline ff ();
          spin ncx hs
    | Some ({core=FreshTuply (_, _); _ }, _) ->
        failwith "unexpected case"
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
  if is_sndord_fact sq.active then
    eprintf "; omitted goal (second-order)@."
  else
    pp_print_assert ~meta:{ hkind = Goal ; name = "Goal" } cx ff (Apply (Internal B.Neg %% [], [sq.active]) %% []);
  pp_print_newline ff ();

  fprintf ff "(check-sat)@.";
  fprintf ff "(exit)@."
