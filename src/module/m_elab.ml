(*
 * module/elab.ml --- modules (elaboration)
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

Revision.f "$Rev$";;

open Ext
open Property
open Util.Coll

open Expr.T
open Expr.Subst
open Proof.T

open M_t

(*let debug = Printf.eprintf;;*)

(******************************************************************************)

(* [FIXME] move to module/subst.ml *)

let rec app_modunits s = function
  | [] -> (s, [])
  | mu :: mus ->
      let (s, mu) = app_modunit s mu in
      let (s, mus) = app_modunits s mus in
      (s, mu :: mus)

and app_modunit s mu =
  match mu.core with
  | Constants cs ->
      (bumpn (List.length cs) s, mu)
  | Recursives cs ->
      (bumpn (List.length cs) s, mu)
  | Variables vs ->
      (bumpn (List.length vs) s, mu)
  | Definition (df, wd, vis, ex) ->
      let df = app_defn s df in
      (bump s, Definition (df, wd, vis, ex) @@ mu)
  | Axiom (nm, e) ->
      let e = app_expr s e in
      let s = bumpn (if nm = None then 1 else 2) s in
      (s, Axiom (nm, e) @@ mu)
  | Theorem (nm, sq, naxs, prf, prf_orig,summ) ->
      let sq = app_sequent s sq in
      let s = bump s in
      let prf =
        let s = bumpn (Deque.size sq.context) s in
        Proof.Subst.app_proof s prf
      in
      let s = if nm = None then s else bump s in
      (s, Theorem (nm, sq, naxs, prf, prf_orig, summ) @@ mu)
  | Submod m ->
      let m = app_mule s m in
      (s, Submod m @@ mu)
  | Mutate (uh, us) ->
      let us = Proof.Subst.app_usable s us in
      let s = if uh = `Hide then s else bumpn (List.length us.facts) s in
      (s, Mutate (uh, us) @@ mu)
  | Anoninst (inst, loc) ->
      let isub = List.map (fun (v, e) -> (v, app_expr s e)) inst.inst_sub in
      (s, Anoninst ({inst with inst_sub = isub}, loc) @@ mu)

and app_mule s m =
  let (_, bod) = app_modunits s m.core.body in
  { m.core with body = bod } @@ m

(******************************************************************************)

let localize_axioms body =
  let rec spin prefix = function
    | [] -> List.rev prefix
    | mu :: mus ->
        begin match mu.core with
        | Axiom (nm, e) ->
            let (prefix, e) =
                (* [NOTE] e is shifted by 1 and moved into mus, then
                 * mus is shifted by -1 before spinning *)
              match nm with
              | None ->
                  (prefix, app_expr (shift 1) e)
              | Some nm ->
                  ((Definition (Operator (nm, e) @@ mu, Proof Always, Visible, Export)
                    @@ mu)
                   :: prefix,
                   Ix 2 @@ mu)
            in
            let h = Fact (e, Visible, Always) @@ mu in
            let rec insert_ax rinits n = function
              | [] -> List.rev rinits
              | mu :: mus ->
                  begin match mu.core with
                  | Theorem (nm, sq, naxs, prf,prf_orig, summ) ->
                      let h = app_hyp (shift n) h in
                      let sq = app_sequent (shift 1) sq in
                      let sq = { sq with context = Deque.cons h sq.context } in
                      let mu =
                        Theorem (nm, sq, naxs + 1, prf, prf_orig, summ) @@ mu
                      in
                      insert_ax (mu :: rinits)
                                (if nm = None then n + 1 else n + 2)
                                mus
                  | _ ->
                      insert_ax (mu :: rinits) (n + hyp_size mu) mus
                end
            in
            let mus = insert_ax [] 0 mus in
            let (_, mus) = app_modunits (shift (-1)) mus in
            spin prefix mus
        | _ ->
            spin (mu :: prefix) mus
        end
  in
  spin [] body

(******************************************************************************)

let salt_counter = ref 0;;
let salt oname =
  incr salt_counter;
  (oname.core ^ "$" ^ string_of_int !salt_counter) @@ oname

(* The following function appears complex, but is actually pretty
 * straightforward. Do not be awed by its length, but instead try to
 * understand it piece by piece. *)

let instantiate anon (mcx : modctx) cx (inst : instance wrapped) ~local ~iname =
  let not_complained = ref true in
  if not (Sm.mem inst.core.inst_mod mcx) then begin
    Errors.err ~at:inst "Module %S not found" inst.core.inst_mod;
    failwith "Module.Elab.instantiate"
  end;
  let mule = Sm.find inst.core.inst_mod mcx in

  (* Find all the necessary parameters *)
  let mule_params =
    let rec scan ps = function
      | [] -> ps
      | mu :: mus ->
          begin match mu.core with
          | Constants cs ->
              let ps =
                List.fold_left (fun ps (nm, _) -> Ss.add nm.core ps) ps cs
              in
              scan ps mus
          | Variables vs ->
              let ps = List.fold_left (fun ps nm -> Ss.add nm.core ps) ps vs in
              scan ps mus
          | _ ->
              scan ps mus
        end
    in scan Ss.empty mule.core.body
  in

  (* Roll given substitution into a map for efficient lookup *)
  let subst =
    List.fold_left (fun subst (v, e) -> Hm.add v e subst) Hm.empty
                   inst.core.inst_sub
  in

  (* complain if there are any extra parameters *)
  let complain v _ =
    if not (Ss.mem v.core mule_params) then begin
      Errors.err ~at:v
                 "Parameter %s in substitution not declared in module %S"
                 v.core inst.core.inst_mod;
      failwith "Module.Elab.instantiate"
    end
  in
  Hm.iter complain subst;

  (* Extend the cx *)
  let extend cx v =
    Deque.snoc cx (Fresh (v, Shape_expr, Unknown, Unbounded) @@ v)
  in
  let cx = List.fold_left extend cx inst.core.inst_args in

  (* Complete the substitution with the missing parameters *)
  let f s subst =
    if Hm.mem (s @@ inst) subst then subst
    else match Deque.find cx (Expr.Anon.hyp_is_named s) with
      | None ->
          Errors.err ~at:inst
            "Required parameter %S for module %S could not be inferred.\n"
            s inst.core.inst_mod;
          failwith "Module.Elab.normalize"
      | Some _ ->
          Hm.add (s @@ inst) (Opaque s @@ inst) subst
  in
  let subst = Ss.fold f mule_params subst in

  (* anonymize the subst *)
  let subst = Hm.map (anon#expr ([], cx)) subst in

  (* erases proof *)
  let remove_pf mu =
    match mu.core with
    | Theorem (nm, sq, naxs, prf, prf_orig, summ) ->
        Theorem (nm, sq, naxs, (Omitted Implicit @@ prf), prf_orig, summ) @@ mu
    | _ -> mu
  in

  (* bring mule body to here *)
  assert (Deque.size cx >= mule.core.defdepth);
  let (_, body) =
    app_modunits (shift (Deque.size cx - mule.core.defdepth))
                 (List.map remove_pf mule.core.body)
  in

  (* perform the substitution *)
  let rec apply_subst body body_len = function
    | [] -> List.rev body
    | mu :: mus ->
        begin match mu.core with
        | Constants [nm, _]
        | Variables [nm] ->
            let e = Hm.find nm subst in
            let e = app_expr (shift body_len) e in
            let (_, mus) = app_modunits (scons e (shift 0)) mus in
            apply_subst body body_len mus
        | Constants (c :: cs) ->
            apply_subst body body_len ((Constants [c] @@ mu)
                                       :: (Constants cs @@ mu)
                                       :: mus)
        | Variables (v :: vs) ->
            apply_subst body body_len ((Variables [v] @@ mu)
                                       :: (Variables vs @@ mu)
                                       :: mus)
        | _ ->
            apply_subst (mu :: body) (body_len + hyp_size mu) mus
      end
  in
  let body = apply_subst [] 0 body in

  (* name tweaking *)
  let tweak nm =
    match iname.core with
    | "" -> nm
    | _ -> (iname.core ^ "!" ^ nm.core) @@ nm
  in

  (* tweaking substitution *)
  let niargs = List.length inst.core.inst_args in
  let iargs = List.init niargs (fun k -> Ix (niargs - k) @@ inst) in
  let resub_for n =
    (* This function is inefficient because it builds intermediate lists
     * and then iterates over them. It has a conceptual simplicity,
     * but if/when performance becomes an issue, this should be revisited.
     * Performance will degrade linearly with the product of the number
     * of INSTANCEs and the (maximum) size of the instancees
     *
     * This function builds a substitution to be applied to the nth unit
     * occurring in the body of the instancee.
     *
     * Step 1. all non-params (indexes outside 1 .. n + niargs) are unchanged
     *)
    let sub = shift (n + niargs) in
    (* Step 2. instance parameters, which were bound before in cx, are changed
     *         to be bound locally in the defn. Thus, the tail of the subst
     *         (indexes in range n + 1 .. n + niargs) are moved to 1 .. niargs.
     *)
    let sub =
      List.fold_right scons (List.init niargs (fun k -> Ix (k + 1) @@ inst)) sub
    in
    (* Step 3. original parameters are now shifted up by niargs to account
     *         for the now localized instance parameters.
     *)
    let sub =
      let l =
        List.init n (fun k -> Apply (Ix (k + niargs + 1) @@ inst, iargs) @@inst)
      in
      List.fold_right scons l sub
   in
    sub
  in

  (* add additional lambdas if needed *)
  let lambdify e =
    match e.core with
    | Lambda (vs, le) ->
        let ivs = List.map (fun v -> (v, Shape_expr)) inst.core.inst_args in
        Lambda (ivs @ vs, le) @@ e
    | _ ->
        if niargs = 0
        then e
        else begin
          let ivs = List.map (fun v -> (v, Shape_expr)) inst.core.inst_args in
          Lambda (ivs, e) @@ e
        end
  in

  (* for each definition and fact, resub and lambdify *)
  let rec localize body body_len = function
    | [] -> List.rev body
    | mu :: mus ->
        begin match mu.core with
        | Definition ({core = Operator (nm, e)} as df, wd, vis, ex) ->
            let nm = if ex = Local then salt nm else nm in
            let nm = tweak nm in
            let e = app_expr (resub_for body_len) e in
            let e = lambdify e in
            let wd = if ex = Local then Builtin else wd in
            let ex = if ex = Local then Local else local in
            let mu = Definition (Operator (nm, e) @@ df, wd, vis, ex) @@ mu in
            localize (mu :: body) (body_len + 1) mus
        | Definition ({core = Bpragma (nm, e, meth)} as df, wd, vis, ex) ->
            (* This case is almost excaclty a duplicate of the previous one *)
            let nm = if ex = Local then salt nm else nm in
            let nm = tweak nm in
            let e = app_expr (resub_for body_len) e in
            let e = lambdify e in
            let wd = if ex = Local then Builtin else wd in
            let ex = if ex = Local then Local else local in
            let mu =
              Definition (Bpragma (nm, e, meth) @@ df, wd, vis, ex) @@ mu
            in
            localize (mu :: body) (body_len + 1) mus
        | Axiom (nm, e) ->
            let nm = Option.map tweak nm in
            let e = app_expr (resub_for body_len) e in
            if niargs > 0 && !not_complained then begin
              Errors.warn ~at:inst
                "%s\n%s@\n(%s)"
                "Instancing produces parametric axioms."
                "Such axioms will be forcibly hidden and cannot be cited."
                "This warning appears at-most once per INSTANCE declaration.";
              not_complained := false;
            end;
            let e = lambdify e in
            let mu = Axiom (nm, e) @@ mu in
            localize (mu :: body) (body_len + hyp_size mu) mus
        | Theorem (nm, sq, naxs, prf, prf_orig, summ) ->
            let nm = Option.map tweak nm in
            let e = exprify_sequent sq @@ mu in
            let e = app_expr (resub_for body_len) e in
            if niargs > 0 && !not_complained then begin
              Util.eprintf ~at:inst ~prefix:"Warning: "
                "%s@\n%s@\n(%s)"
                "Instancing produces parametric theorems."
                "Such theorems will be forcibly hidden and cannot be cited."
                "This warning appears at-most once per INSTANCE declaration.";
              not_complained := false;
            end;
            let e = lambdify e in
            let sq =
              match e.core with
              | Sequent sq -> sq
              | _ -> {context = Deque.empty ; active = e}
            in
            let prf = Omitted (Elsewhere (Util.get_locus mu)) @@ mu in
            let mu = Theorem (nm, sq, naxs, prf, prf_orig, summ) @@ mu in
            localize (mu :: body) (body_len + 1) mus
        | Mutate (`Hide, _) ->
            localize body body_len mus
        | Mutate (`Use _, us) ->
            let (_, mus) =
              app_modunits (shift (- (List.length us.Proof.T.facts))) mus
            in
            localize body body_len mus
        | Submod _ ->
            localize body body_len mus
        | Constants _
        | Recursives _
        | Variables _
        | Definition _
        | Anoninst _ ->
            (* the instancee has been normalized before, so there
             * should not be any parameters or (unnamed) instances. *)
            Errors.bug ~at:inst "Module.Elab.localize"
      end
  in
  let body = localize [] 0 body in
  localize_axioms body

(******************************************************************************)

let anon = object (self : 'self)
  inherit Proof.Anon.anon as super

  val mutable __mcx : modctx = Sm.empty

  method mexpr mcx scx e =
    __mcx <- mcx ;
    self#expr scx e

  method mproof mcx scx prf =
    __mcx <- mcx ;
    self#proof scx prf

  method musable mcx scx us =
    __mcx <- mcx ;
    self#usable scx us

  method mhyp mcx scx hyp =
    __mcx <- mcx ;
    self#hyp scx hyp

  method msequent mcx scx sq =
    __mcx <- mcx ;
    self#sequent scx sq

  method defns scx dfs =
    match dfs with
    | {core = Instance (nm, inst)} as df :: dfs ->
        if not (Sm.mem inst.inst_mod __mcx) then begin
          Errors.err ~at:df "Module %S unknown\n%!" inst.inst_mod;
          failwith "Module.Elab.anon#defns"
        end;
        let submus =
          instantiate self __mcx (snd scx) (inst @@ df) ~local:Local ~iname:nm
        in
        let rec make_defs sofar = function
          | [] -> List.rev sofar
          | mu :: mus ->
              begin match mu.core with
              | Definition (df, _, _, _) -> make_defs (df :: sofar) mus
              | _ ->
                  let (_, mus) = app_modunits (shift (-1)) mus in
                  make_defs sofar mus
              end
        in
        self#defns scx (make_defs [] submus @ dfs)
    | _ ->
        super#defns scx dfs
end

(******************************************************************************)

(* is_anon = false => not yet anonymised *)
let rec normalize mcx cx m =
  let origbody = m.core.body in
  let prefix = ref Deque.empty in
  let emit mu = prefix := Deque.snoc !prefix mu in
  let rec spin mcx cx = function
    | [] -> cx
    | (mu, is_anon) :: mus ->
      begin
        let continue mcx cx mu s =
          emit mu;
          let hs = hyps_of_modunit mu in
          let pr_mu ff =
            ignore (M_fmt.pp_print_modunit (cx, Ctx.dot) ff mu)
          in
          let pr_seq ff =
            ignore (Expr.Fmt.pp_print_sequent (cx, Ctx.dot) ff
                             {context = Deque.of_list hs;
                              active = (At false) @@ mu})
          in
          Util.eprintf ~debug:"inst" ~at:mu
                       "((%s)) modunit = %thyps = %t@." s
                       pr_mu pr_seq;
          let cx = Deque.append_list cx (hyps_of_modunit mu) in
          spin mcx cx mus
        in
        match mu.core with
        | Anoninst (inst, loc) ->
          begin
            if not (Sm.mem inst.inst_mod mcx) then begin
              Errors.err ~at:mu "Module %S unknown\n%!" inst.inst_mod;
              failwith "Module.Elab.normalize";
            end;
            let submus =
              instantiate anon mcx cx (inst @@ mu) ~local:loc ~iname:("" @@ mu)
            in
            spin mcx cx ((List.map (fun x -> x,true) submus) @ mus)
          end
        | Definition ({core = Instance (nm, inst)}, _, _, ex) ->
          begin
            if not (Sm.mem inst.inst_mod mcx) then begin
              Errors.err ~at:mu "Module %S unknown\n%!" inst.inst_mod;
              failwith "Module.Elab.normalize";
            end;
            Util.eprintf ~debug:"inst" ~at:mu
              "Instantiating: %t@."
              (fun ff -> ignore (M_fmt.pp_print_modunit (cx, Ctx.dot) ff mu));
            let submus =
              instantiate anon mcx cx (inst @@ mu) ~local:ex ~iname:nm
            in
            spin mcx cx ((List.map (fun x -> x,true) submus) @ mus)
          end
        | Definition ({core = Operator (nm, _)} as df, wd, vis, ex)
            (* treat pragma definitions as usual operator definitions *)
        | Definition ({core = Bpragma (nm, _, _)} as df, wd, vis, ex) ->
          begin
            let df = if is_anon then df else anon#defn ([], cx) df in
            let df =
                let visitor = object
                  inherit Expr.Constness.const_visitor
                end
                in
                visitor#defn ((),cx) df in
            let mu = Definition (df, wd, vis, ex) @@ mu in
            (* merge identical operator definitions *)
            let h = Defn (df, wd, vis, ex) @@ mu in
            match Deque.find ~backwards:true cx
                             (Expr.Anon.hyp_is_named nm.core) with
            | Some (x, ({core = Defn (d, _, _, _)} as oh)) ->
                let oh = app_hyp (shift (x + 1)) oh in
                let eq =
                  match d.core with
                  | Recursive _ -> true
                  | _ -> Expr.Eq.hyp oh h
                in
                if eq then begin
                  let mus,flags = List.split mus in
                  let (_, mus) =
                    app_modunits (scons (Ix (x + 1) @@ h) (shift 0)) (mus) in
                  let mus = List.combine mus flags in
                    spin mcx cx mus
                end else begin
                  continue mcx cx mu "Definition1"
                end
            | _ ->
                continue mcx cx mu "Definition2"
          end
        | Recursives _
        | Definition ({core = Recursive _}, _, _, _)
            (* FIXME eliminate redundant definitions here too *)
        | Constants _
        | Variables _ -> continue mcx cx mu "Variables"
        | Axiom (nm, e) ->
            let redundant =
              match nm with
              | None -> false
              | Some nm ->
                  Deque.find cx (Expr.Anon.hyp_is_named nm.core) != None
            in
            if redundant then begin
              spin mcx cx mus
            end else begin
              let e = anon#mexpr mcx ([], cx) e in
              let e =
                let visitor = object
                  inherit Expr.Constness.const_visitor
                end
                in
                visitor#expr ((),cx) e in
              let mu = Axiom (nm, e) @@ mu in
              continue mcx cx mu "Axiom"
            end
        | Theorem (nm, sq, naxs, pf, pf_orig, summ) ->
            let redundant =
              match nm with
              | None -> false
              | Some nm ->
                  Deque.find cx (Expr.Anon.hyp_is_named nm.core) != None
            in
            let (nm, pf, pf_orig) =
              if redundant then begin
                let name =
                  match nm with
                  | Some n -> ("(redundant)" ^ n.core) @@ n
                  | _ -> assert false
                in
                (Some name, Obvious @@ pf, Obvious @@ pf_orig)
              end else (nm, pf, pf_orig)
            in
            begin
              let (_, sq) = anon#msequent mcx ([], cx) sq in
              let (_, sq) =
                let visitor = object
                  inherit Expr.Constness.const_visitor
                end
                in
                visitor#sequent ((),cx) sq in
              let pf =
                let (cx, sq) =
                  match nm with
                  | Some nm ->
                      let op = Operator (nm, exprify_sequent sq @@ nm) @@ mu in
                      (Deque.snoc cx (Defn (op, Proof Always, Visible, Export) @@ mu),
                       app_sequent (shift 1) sq)
                  | None ->
                      (cx, sq)
                in
                let cx = Deque.append cx sq.context in
                let time_flag = Expr.Temporal_props.check_time_change sq.context Always in
                Util.eprintf ~debug:"simplify" ~at:mu
                  "@[<v0>Simplifying:@,  THEOREM %a@,  %a@]"
                  (Expr.Fmt.pp_print_expr (Deque.empty, Ctx.dot))
                  (exprify_sequent sq @@ mu)
                  (Proof.Fmt.pp_print_proof (cx, Ctx.dot)) pf;
                (*let pf =
                  let visitor1 = object
                    inherit [unit] Proof.Visit.map as proofer
                    inherit Expr.Constness.const_visitor
                    method proof scx pf = proofer#proof scx pf
                  end
                  in
                  visitor1#proof ((),cx) pf in*)
                let pf = anon#mproof mcx ([], cx) pf in
                if m.core.important then
                  Proof.Simplify.simplify cx sq.active pf time_flag
                else pf
              in
              (* we apply it later to obligations so we can skip the proofs
               * themselves *)
(*              let pf =
                let visitor = object
                  inherit [unit] Proof.Visit.map as proofer
                  inherit Expr.Constness.const_visitor
                  method proof scx pf = proofer#proof scx pf
                end
                in
                visitor#proof ((),cx) pf in
              let pf =
                let visitor = object
                  inherit [unit] Proof.Visit.map as proofer
                  inherit Expr.Leibniz.leibniz_visitor
                  method proof scx pf = proofer#proof scx pf
                end
                in
                visitor#proof ((),cx) pf in *)
              let mu = Theorem (nm, sq, naxs, pf, pf_orig, summ) @@ mu in
              continue mcx cx mu "Theorem"
            end
        | Mutate (uh, us) ->
            let us = anon#musable mcx ([], cx) us in
            let mu = Mutate (uh, us) @@ mu in
            continue mcx cx mu "Mutate"
        | Submod m ->
            let (mcx, m, _) = normalize mcx cx m in
            let mu = Submod m @@ mu in
            continue mcx cx mu "Submod"
        end
  in
  let gencx = cx in
  let _cx = spin mcx cx (List.map (fun x -> x,false) m.core.body) in
    Util.eprintf ~debug:"foo" "%a" (fun fmt cx -> ignore (Expr.Fmt.pp_print_sequent (Deque.empty, Ctx.dot) fmt cx))  ({context = _cx ; active = Ix(1) @@ m});
  let prefix = Deque.to_list !prefix in
  let maybe_salt mu =
    if has mu salt_prop then begin
      let mu = match mu.core with
        | Definition ({core = Operator (nm, e)} as df, wd, vis, ex) ->
            Definition (Operator (salt nm, e) @@ df, wd, vis, ex) @@ mu
        | Definition ({core = Instance (nm, ins)} as df, wd, vis, ex) ->
            Definition (Instance (salt nm, ins) @@ df, wd, vis, ex) @@ mu
        | _ ->
            Errors.bug ~at:mu "Module.Elab.normalize: has salt_prop"
      in remove mu salt_prop
    end else mu
  in
  let prefix = List.map maybe_salt prefix in
  let m = { m.core with body = prefix } @@ m in
  let (m, obs, summ) =
    if m.core.important then M_gen.generate gencx m
    else (m, [], {
            sum_total = 0 ;
            sum_absent = 0, [] ;
            sum_omitted = 0, [] ;
            sum_suppressed = 0, []
          })
  in
  let m = match m.core.stage with
    | Special -> m
    | Flat ->
        let stage = Final { final_named  = origbody
                          ; final_obs    = Array.of_list obs
                          ; final_status = (Unchecked, summ)
                          }
        in { m.core with stage = stage } @@ m
    | Parsed ->
        Errors.bug ~at:m "Elaborating an unflattened module"
    | Final _ ->
        Errors.bug ~at:m "Elaborating a final module"
  in
  let m = { m.core with defdepth = Deque.size gencx } @@ m in
  let mcx = Sm.add m.core.name.core m mcx in
  (mcx, m, summ)
