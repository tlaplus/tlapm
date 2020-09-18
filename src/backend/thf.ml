(*
 * backend/thf.mli --- translation to TPTP/THF
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
open Type.T
open Util.Coll

module B = Builtin

let error ?at mssg =
  let mssg = "Backend.Thf: " ^ mssg in
  Errors.bug ?at mssg

(* FIXME remove *)
let primed s = s ^ "__prime"

let to_uppercase s =
  if String.length s > 0 then
    let c = String.get s 0 in
    if 'a' <= c && c <= 'z' then
      "Z__" ^ s
    else s
  else s

let to_lowercase s =
  if String.length s > 0 then
    let c = String.get s 0 in
    if 'A' <= c && c <= 'Z' then
      "z__" ^ s
    else s
  else s


(* {3 Context} *)

let init_cx = Ctx.dot

let adj_l cx v =
  let nm = to_uppercase v.core in
  let cx = Ctx.push cx nm in
  (cx, Ctx.string_of_ident (Ctx.front cx))

let adj_g cx v =
  let nm = to_lowercase v.core in
  let cx = Ctx.push cx nm in
  (cx, Ctx.string_of_ident (Ctx.front cx))

let bump cx =
  fst (adj_l cx ("" %% []))

let lookup_id cx n =
  Ctx.string_of_ident (fst (Ctx.index cx n))


(* {3 Expression Formatting} *)

(* FIXME fix formatting then remove *)
let pp_print_commasp ff () =
  pp_print_string ff ", "

(* FIXME fix formatting then remove *)
let pp_print_delimited ?(sep=pp_print_commasp) =
  Fmtutil.pp_print_delimited ~sep

let pp_print_sort ff ty =
  let s =
    match ty with
    | TAtm TAIdv -> "$i"
    | TAtm TABol -> "$o"
    | TAtm TAInt -> "$int"
    | _ -> ty_to_string ty
  in
  pp_print_string ff s

let pp_print_conn s ff () =
  fprintf ff " %s " s

let pp_print_tyfunc ff (ty1s, ty) =
  let pp_print_ty1 ff = function
    | Ty1 ([], ty) ->
        pp_print_sort ff ty
    | Ty1 (ty0s, ty) ->
        fprintf ff "( %a )"
        (pp_print_delimited ~sep:(pp_print_conn ">") pp_print_sort)
        (ty0s @ [ ty ])
  in
  pp_print_delimited ~sep:(pp_print_conn ">")
  pp_print_ty1 ff (ty1s @ [ Ty1 ([], ty) ])

(* Print type attached to hint, not the hint itself *)
let pp_print_typeof ff v =
  if has v Props.ty0_prop then
    let ty = get v Props.ty0_prop in
    pp_print_sort ff ty
  else if has v Props.ty2_prop then
    let ty2 = get v Props.ty2_prop in
    match ty2 with
    | Ty2 (ty1s, ty) ->
        pp_print_tyfunc ff (ty1s, ty)
  else
    error ~at:v "Missing type annotation"

let pp_print_binding ff v =
  fprintf ff "%s: %a" v.core pp_print_typeof v


let is_arith op =
  false (* FIXME *)


let rec pp_print_thf_atomic cx ff oe =
  match oe.core with
  | Ix n ->
      let id = lookup_id cx n in
      pp_print_string ff id

  | Opaque s ->
      (* FIXME Ad hoc trick that formats primed variables.
       * Would be cleaner to eliminate these beforehand *)
      let s =
        match String.split_on_char '#' s with
        | [ s ; "prime" ] -> primed s
        | _ -> s
      in
      pp_print_string ff s

  | Internal B.TRUE ->
      pp_print_string ff "$true"

  | Internal B.FALSE ->
      pp_print_string ff "$false"

  | Internal _ ->
      error ~at:oe "Unsupported expression"

  | Apply (e, []) ->
      pp_print_thf_atomic cx ff e

  | List (Refs, [e]) ->
      pp_print_thf_atomic cx ff e

  | Let ([], e) ->
      pp_print_thf_atomic cx ff e

  | Quant (_, [], e) ->
      pp_print_thf_atomic cx ff e

  | Num (m, "") ->
      fprintf ff "%s" m

  | Num (m, n) ->
      fprintf ff "%s.%s" m n

  | Parens (e, _) ->
      pp_print_thf_atomic cx ff e

  | _ ->
      fprintf ff "@[<hov 2>( %a@] )"
      (pp_print_thf_logic cx) oe

and pp_print_thf_logic cx ff oe =
  match oe.core with
  | Apply ({ core = Internal B.Neg }, [ e ]) ->
      fprintf ff "~ %a"
      (pp_print_thf_atomic cx) e

  | Apply ({ core = Internal (B.Implies | B.Equiv | B.Conj | B.Disj | B.Eq | B.Neq as b) }, [ e ; f ]) ->
      let s =
        match b with
        | B.Implies -> "=>"
        | B.Equiv -> "<=>"
        | B.Conj -> "&"
        | B.Disj -> "|"
        | B.Eq -> "="
        | B.Neq -> "!="
        | _ -> error "Unexpected builtin"
      in
      fprintf ff "%a%a%a"
      (pp_print_thf_atomic cx) e
      (pp_print_conn s) ()
      (pp_print_thf_atomic cx) f

  | List (q, es) ->
      let s =
        match q with
        | And | Refs -> "&"
        | Or -> "|"
      in
      pp_print_delimited ~sep:(pp_print_conn s)
      (pp_print_thf_atomic cx) ff es

  | Sequent sq when Deque.null sq.context ->
      pp_print_thf_logic cx ff sq.active

  | Sequent sq when not (Deque.null sq.context) ->
      let h, hs = Option.get (Deque.front sq.context) in
      let rest = Sequent { sq with context = hs } @@ oe in
      begin match h.core with
      | Fact (e, Visible, _) ->
          let ncx = bump cx in
          fprintf ff "%a%a%a"
          (pp_print_thf_atomic cx) e
          (pp_print_conn "=>") ()
          (pp_print_thf_atomic ncx) rest

      | Fresh (v, _, _, Unbounded) ->
          let ncx, nm = adj_l cx v in
          let v = nm @@ v in
          fprintf ff "! [ %a ] :@ %a"
          pp_print_binding v
          (pp_print_thf_logic ncx) rest

      | Flex v ->
          let ncx, nm = adj_l cx v in
          let v = nm @@ v in
          let v_primed = primed nm @@ v in
          fprintf ff "! [ %a ] :@ %a"
          (pp_print_delimited pp_print_binding) [ v ; v_primed ]
          (pp_print_thf_logic ncx) rest

      | _ ->
          error ~at:oe "Unsupported expression"
      end

  | _ ->
      pp_print_thf_apply cx ff oe

and pp_print_thf_apply cx ff oe =
  match oe.core with
  | Apply (op, args) when not (is_arith op) ->
      pp_print_delimited ~sep:(pp_print_conn "@")
      (pp_print_thf_atomic cx) ff (op :: args)

  | _ ->
      pp_print_thf_quant cx ff oe

and pp_print_thf_quant cx ff oe =
  match oe.core with
  | Lambda (xs, e) ->
      let ncx, rvs =
        List.fold_left begin fun (cx, rvs) (v, _) ->
          let ncx, nm = adj_l cx v in
          let v = nm @@ v in
          (ncx, v :: rvs)
        end (cx, []) xs
      in
      fprintf ff "^ [ %a ] :@ %a"
      (pp_print_delimited pp_print_binding) (List.rev rvs)
      (pp_print_thf_atomic ncx) e

  | Quant (q, bs, e) ->
      let ncx, rbs =
        let rec spin acc_cx acc_bs bs =
          match bs with
          | [] -> (acc_cx, acc_bs)
          | (v, _, _) :: bs ->
              let acc_cx, nm = adj_l acc_cx v in
              let v = nm @@ v in
              let acc_bs = v :: acc_bs in
              spin acc_cx acc_bs bs
        in
        spin cx [] bs
      in
      let qrep =
        match q with
        | Forall -> "!"
        | Exists -> "?"
      in
      fprintf ff "%s [ %a ] :@ %a" qrep
      (pp_print_delimited pp_print_binding) (List.rev rbs)
      (pp_print_thf_atomic ncx) e

  | _ ->
      pp_print_thf_let cx ff oe

and pp_print_thf_let cx ff oe =
  match oe.core with
  | Let (ds, e) ->
      let ncx, vs =
        let rec f acc_cx acc_vs ds =
          match ds with
          | [] -> (acc_cx, acc_vs)
          | { core = Operator (nm, e) } :: ds ->
              let acc_cx, nm = adj_l acc_cx nm in
              let acc_vs = (nm, e) :: acc_vs in
              f acc_cx acc_vs ds
          | _ ->
              error ~at:oe "unsupported LET expression"
        in
        f cx [] ds
      in
      let pp_print_vbind cx ff (nm, e) =
        fprintf ff "%s :=@ %a" nm
        (pp_print_thf_atomic cx) e
      in
      fprintf ff "@[<hov 2>$let([ %a ],@ %a@])"
      (pp_print_delimited (pp_print_vbind cx)) vs
      (pp_print_thf_atomic ncx) e

  | _ ->
      pp_print_thf_ite cx ff oe

and pp_print_thf_ite cx ff oe =
  match oe.core with
  | If (e, f, g) ->
      fprintf ff "@[<hov 2>$ite(@,%a,@ %a,@ %a@])"
      (pp_print_thf_atomic cx) e
      (pp_print_thf_atomic cx) f
      (pp_print_thf_atomic cx) g

  | Case (_, None) ->
      error ~at:oe "CASE with missing 'default'"

  | Case ([ (e1, e2) ], Some e3) ->
      pp_print_thf_ite cx ff (If (e1, e2, e3) @@ oe)

  | Case ((e1, e2) :: ps, Some o) ->
      pp_print_thf_ite cx ff (If (e1, e2, Case (ps, Some o) %% []) @@ oe)

  | Bang _ | With _
  | Choose _ | SetSt _ | SetOf _ | Product _ | Tuple _
  | Fcn _ | FcnApp _ | Arrow _ | Rect _ | Record _
  | Except _ | Dot _ | Sub _ | Tsub _ | Fair _ | String _
  | At _ ->
      error ~at:oe "Unsupported expression"

  | _ ->
      pp_print_thf_arith cx ff oe

and pp_print_thf_arith cx ff oe =
  match oe.core with
  | Apply (op, es) when is_arith op ->
      error ~at:oe "Not implemented" (* FIXME *)
      (*let smb = get op smb_prop in
      let s =
        match Option.get (get_defn smb) with
        | Plus -> "sum"
        | Uminus -> "uminus"
        | Minus -> "minus"
        | Times -> "product"
        | Lteq -> "lesseq"
        | _ -> error ~at:op "Expected arithmetic operator"
      in
      fprintf ff "@[<hov 2>$%s(@,%a@])" s
      (pp_print_delimited (pp_print_thf_atomic cx)) es*)

  | _ ->
      pp_print_thf_atomic cx ff oe

let pp_print_expr cx ff oe =
  pp_print_thf_atomic cx ff oe


(* {3 Preprocessing} *)

(* This very important function does several transformations on the sequent
 * to shape it into something translatable to THF. *)
let preprocess ?solver sq =
  let _ = solver in (* NOTE not used *)

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
    (* NOTE eliminating bound notation necessary to make all '\in' visible *)
    |> Encode.Rewrite.elim_notmem
    |> Encode.Rewrite.elim_multiarg
    |> Encode.Rewrite.elim_tuples
    |> Encode.Rewrite.elim_bounds
    |> debug "Done Simpl. Bounds" (* FIXME remove *)
    (*|> Encode.Direct.main*)
    |> debug "Done Direct"
    (*|> Encode.Axiomatize.main*)
    |> debug "Done Axiomatize" (* FIXME remove *)
  in
  sq


(* {3 Obligation Formatting} *)

type form =
  | Sort of ty
  | Opr of Util.hint
  | Form of expr

type role =
  | Type
  | Definition
  | Axiom
  | Conjecture

let pp_print_formula cx ff = function
  | Sort ty ->
      fprintf ff "( %a: $tType )" pp_print_sort ty
  | Opr v ->
      fprintf ff "( %a )" pp_print_binding v
  | Form e ->
      pp_print_expr cx ff e

let pp_print_role ff = function
  | Type -> pp_print_string ff "type"
  | Definition -> pp_print_string ff "definition"
  | Axiom -> pp_print_string ff "axiom"
  | Conjecture -> pp_print_string ff "conjecture"

let pp_print_thf cx ff ?comment name role form =
  Option.iter begin fun comment ->
    fprintf ff "%%---- %s@." comment
  end comment;
  fprintf ff "@[<hov 2>thf(%s, %a,@ %a@]).@."
  name pp_print_role role (pp_print_formula cx) form

let pp_print_obligation ?(solver="CVC4") ff ob =
  (* Shape the sequent into a form that can be translated;
   * Append a top context containing additional declarations and axioms *)
  let sq = preprocess ~solver ob.Proof.T.obl.core in

  (* Print preample *)
  pp_print_newline ff ();
  fprintf ff "%%---- TLA+ Proof Manager %s@." (Params.rawversion ());
  fprintf ff "%%---- Proof obligation #%d@." (Option.get ob.id);
  fprintf ff "%%---- Generated from %s@." (Util.location ~cap:false ob.obl);
  pp_print_newline ff ();

  (* Print sorts *)
  fprintf ff "%%---- Sorts@.";
  pp_print_newline ff ();
  let srts = Type.Collect.main sq in
  let srts = Ts.filter begin function
      TAtm TAIdv | TAtm TABol | TAtm TAInt -> false | _ -> true
  end srts in
  List.iteri begin fun i ty ->
    pp_print_thf Ctx.dot ff ("type" ^ string_of_int i) Type (Sort ty)
  end (Ts.elements srts);
  pp_print_newline ff ();

  (* Print hypotheses *)
  fprintf ff "%%---- Hypotheses@.";

  let rec spin cx hs =
    match Deque.front hs with
    | None ->
        cx

    | Some ({ core = Fact (e, vis, _) }, hs) ->
        let ncx = bump cx in
        begin if vis = Visible then
          let i = Ctx.length cx in
          pp_print_thf cx ff ("fact" ^ string_of_int i) Axiom (Form e)
        else
          fprintf ff "%%---- hidden fact@."
        end;
        pp_print_newline ff ();
        spin ncx hs

    | Some ({ core = Flex v }, hs) ->
        let ncx, nm = adj_g cx v in
        let v = nm @@ v in
        pp_print_thf cx ff ("flex_" ^ nm) Type (Opr v);
        pp_print_newline ff ();
        pp_print_thf cx ff ("flex_" ^ primed nm) Type (Opr v);
        pp_print_newline ff ();
        spin ncx hs

    | Some ({ core = Fresh (v, _, _, _) }, hs) ->
        let ncx, nm = adj_g cx v in
        let v = nm @@ v in
        pp_print_thf cx ff ("fresh_" ^ nm) Type (Opr v);
        pp_print_newline ff ();
        spin ncx hs

    | Some ({ core = Defn ({ core = Operator (v, _) }, _, vis, _) }, hs)
    | Some ({ core = Defn ({ core = Instance (v, _) }, _, vis, _) }, hs)
    | Some ({ core = Defn ({ core = Recursive (v, _) }, _, vis, _) }, hs)
    | Some ({ core = Defn ({ core = Bpragma (v, _, _) }, _, vis, _) }, hs) ->
        let ncx, nm = adj_g cx v in
        let v = nm @@ v in
        pp_print_thf cx ff ("defn_" ^ nm) Type (Opr v);
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
  fprintf ff "%%---- Goal@.";
  pp_print_thf cx ff "goal" Conjecture (Form sq.active);
  pp_print_newline ff ();

