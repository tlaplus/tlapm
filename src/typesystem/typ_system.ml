(************************************************************************
*
*  types_infer.ml
*
*
*  Created by Hernán Vanzetto on 23 Oct 2013.
Copyright (c) 2013  INRIA and Microsoft Corporation
*
************************************************************************)

open Ext
open Property

open Expr.T
open Expr.Subst
open Expr.Visit

open Printf
(* open List *)

module Fu = Fmtutil.Minimal (Tla_parser.Prec)
module B = Builtin
module Smt = Smtcommons
let ( |>> ) = Smt.( |>> )
let ( ||> ) = Smt.( ||> )
let tap = Smt.tap

(* module SMap = Map.Make (String) *)
module SMap = Typ_e.SMap

open Format
open Fmtutil

open Typ_t
open Typ_e
open Typ_c
module T = Typ_t
module E = Typ_e
module C = Typ_c
let map = List.map


(****************************************************************************)


let pp_env_c v env c =
    E.tyvar_assignment_pp v;
    Smt.ifprint
        v
        "  @[<hov2>@[%a@]@, ||-  @[<hov>%a@]@]"
        E.pp env C.pp (env, c)


let pp_prop v env cx e =
    Smt.ifprint
        v
        "<< %a |- %a : Bool >>"
        E.pp env
        (E.pp_print_expr (Smtcommons.to_scx cx, Ctx.dot))
        e


(****************************************************************************)
(* Unification of subtype constraints                                       *)
(****************************************************************************)

let rec rewrite_subs (env, vs, (cs:C.t list)) =
    (** Collect substitutions from subtype constraints,
    returns one type assignment [a <- t]. *)
    let rec collect_ss vs = function
        | CAtom w :: cs ->
            begin match w with
            | CSub (env, t1, t2) ->
                begin match t1, t2 with
                | TyVar (_, a), Set t
                | Set t, TyVar (_, a)
                        when
                            List.mem a vs &&
                            not (T.occurs a t) ->
                    (*
                    Util.eprintf
                        "collect_ss: %a"
                        C.ppc (CSub (E.empty, t1, t2));
                    *)
                    ((a, Set t), [])
                    :: collect_ss vs cs
                | TyVar (_, a), Func (x, t1, t2)
                | Func (x, t1, t2), TyVar (_, a)
                        when
                            List.mem a vs &&
                            not (T.occurs a (Func (x, t1, t2))) ->
                    (*
                    Util.eprintf
                        "collect_ss: %a"
                        C.ppc c;
                    *)
                    (*
                    if T.occurs a (Func (x, t1, t2))
                        then raise (Failure "occurs a Func")
                        else
                    *)
                    begin
                    let a1 = fresh_tyvar
                        ([], Opaque ("temp-" ^ a ^ "#1") %% []) in
                    let a2 = fresh_tyvar
                        ([], Opaque ("temp-" ^ a ^ "#2") %% []) in
                    ((a, Func (x, TyVar ([], a1), TyVar ([], a2))),
                     [a1; a2])
                    :: collect_ss vs cs
                    end
                | TyVar (_, a), (Ref (x, t, r) as tt)
                | (Ref (x, t, r) as tt), TyVar (_, a)
                        when
                            List.mem a vs &&
                            not (T.occurs a tt) ->
                    (*
                    Util.eprintf
                        "collect_ss: %a" C.ppc c;
                    *)
                    (* begin
                    let msg = Util.sprintf
                        "type variable %s occurs in %a"
                        a E.ppt (env, tt) in
                    E.tyvar_assignment_pp 1;
                    if T.occurs a tt
                        then raise (Failure msg)
                    end;
                    *)
                    let pid = C.new_ph (
                        match r with
                        | Ex (cx, e) -> Some ((x, t), env, cx, e)
                        | Ph (_, p) -> SMap.find p !C.phs_log
                        ) in
                    ((a, Ref (x, t, Ph ([], pid))), [])
                    :: collect_ss vs cs

                (** TODO missing case for Rec *)
                | _ ->
                    collect_ss vs cs
                end
            | _ ->
                collect_ss vs cs
            end
        | _ :: cs ->
            collect_ss vs cs
        | [] -> []
        in
    (*
    Smt.ifprint 3
        "__@[<hov2>@[%a@]@. ||-  @[<hov>%a@]@]"
        E.pp env C.pp
        (C.mk_ex (vs, map (fun c -> CAtom c) cs));
    *)
    (* Smt.ifprint 3
        "@[<hov>__0_%a@]"
        C.pp (C.mk_ex (vs, map (fun c -> CAtom c) cs));
    *)
    (* let tx = Sys.time () in *)
    let ssvs = collect_ss vs cs in
    (* Smt.ifprint 4
        "** Collect sub ss in %5.3fs.%!"
        (Sys.time() -. tx);
    *)
    let ss, vars = List.split ssvs in
    let vs = vs @ (List.flatten vars) in
    if ss = []
        then (env, vs, cs)
        else begin
            (* let tx = Sys.time () in *)
            let env, vs, cs = C.apply_ss
                ss (env, vs, cs) in
            C.tccs := C.app_ss
                tcc_subst !C.tccs ss;
            (*
            Smt.ifprint 4
                "** Apply sub ss in %5.3fs.%!"
                (Sys.time() -. tx);
            *)
            rewrite_subs (env, vs, cs)
        end

let unify_subs (env, c) = C.rw_c rewrite_subs (env, c)


(****************************************************************************)
(* Residual constraints                                                     *)
(****************************************************************************)


let rec rewrite_refl (env, vs, cs) =
    let rec pickone_subst = function
        | CAtom w :: cs ->
            begin match w with
            | CEq (_, TyVar (ss, a), TyVar (_, a'))
            | CSub (_, TyVar (ss, a), TyVar (_, a'))
                    when a <> a' ->
                (a', TyVar (ss, a)) :: []
            | CEq (_, TyVar (_, a), TyVar (_, a'))
            | CSub (_, TyVar (_, a), TyVar (_, a')) ->
                (a, TyAtom a) :: (a', TyAtom a) :: []
            | _ ->
                pickone_subst cs
            end
        | _ :: cs ->
            pickone_subst cs
        | [] -> []
        in
    let ss = pickone_subst cs in
    if ss = []
        then (env, vs, cs)
        else begin
            let env, vs, cs = C.apply_ss
                ss (env, vs, cs) in
            rewrite_refl (env, vs, cs)
        end


let rec rewrite_constructs (env, vs, cs) =
    (*
    Util.eprintf
        "rewrite_constructs %a"
        C.pp (env, C.mk_ex (vs, cs));
    *)
    let rec pickone_subst = function
        | CAtom w :: cs ->
            begin match w with
            | CEq (_, Tdom (TyVar ([], a)), t)
                    when T.is_atomic_type (T.ref_to_base t) ->
                Some (Tdom (TyVar ([], a)), t)
            | CEq (_, t, Tdom (TyVar ([], a)))
                    when T.is_atomic_type (T.ref_to_base t) ->
                Some (Tdom (TyVar ([], a)), t)
            | CEq (_, Tcod (TyVar ([], a)), t)
                    when T.is_atomic_type (T.ref_to_base t) ->
                Some (Tcod (TyVar ([], a)), t)
            | CEq (_, t, Tcod (TyVar ([], a)))
                    when T.is_atomic_type (T.ref_to_base t) ->
                Some (Tcod (TyVar ([], a)), t)
            | CEq (_, Rec_dot (TyVar ([], a), h), t)
                    when T.is_atomic_type (T.ref_to_base t) ->
                (** TODO change to accept also Rec_dot *)
                Some (Rec_dot (TyVar ([], a), h), t)
            | CEq (_, t, Rec_dot (TyVar ([], a), h))
                    when T.is_atomic_type (T.ref_to_base t) ->
                (** TODO change to accept also Rec_dot *)
                Some (Rec_dot (TyVar ([], a), h), t)
            | _ ->
                pickone_subst cs
            end
        | _ :: cs ->
            pickone_subst cs
        | [] -> None
        in
    let ss = pickone_subst cs in
    if Option.is_none ss
        then (env, vs, cs)
        else begin
            let a, b = Option.get ss in
            (*
            Util.eprintf
                "pickone_subst %a --> %a"
                E.ppt (env, a)
                E.ppt (env, b);
            *)
            let rep a b t = if T.eq a t
                then b
                else t in
            let rec fff a b = function
                | CAtom (CEq (e, t1, t2)) ->
                    CAtom (CEq (
                        e,
                        rep a b t1,
                        rep a b t2))
                | CAtom (CIsEq (e, t1, t2)) ->
                    CAtom (CIsEq (
                        e,
                        rep a b t1,
                        rep a b t2))
                | CAtom (CSub (e, t1, t2)) ->
                    CAtom (CSub (
                        e,
                        rep a b t1,
                        rep a b t2))
                | CAtom (CIsSub (e, t1, t2)) ->
                    CAtom (CIsSub (
                        e,
                        rep a b t1,
                        rep a b t2))
                | CAtom w ->
                    CAtom w
                | CConj cs ->
                    CConj (
                        List.map (fff a b) cs)
                | CExists (vs, c) ->
                    CExists (
                        vs,
                        fff a b c)
                in
            let cs = List.map (fff a b) cs in
            let cs = List.map C.simp_c cs in
            rewrite_constructs (env, vs, cs)
        end

(** Ground type variables in reflexive constraints *)
let ground_refl (env, c) = (env, c)
    |> C.rw_c rewrite_refl
    |> C.rw_c C.rewrite_eqs

let solve_residual (env, c) = (env, c)
    |> C.rw_c rewrite_constructs

let mdom m =
    let ks, _ = List.split
        (SMap.bindings m) in
    ks

(****************************************************************************)
(* Update placeholders in constraints, types, etc.                          *)
(* using assignment [phs] to update                                         *)
(****************************************************************************)

let update_r phs env = function
    | Ph (ss, p) ->
        begin
        try
            let cx, e = SMap.find p phs in
            (*
            let cx =
                try
                    tl cx
                with _ ->
                    [] in
            *)
            let cx = E.to_cx (env $! E.ss_to_env ss) in
            (*
            Util.eprintf
                "  $ ss: %a"
                (pp_print_delimited E.pp_ss) ss;
            *)
            (*
            Util.eprintf
                "  $ cx: %s"
                (String.concat
                    ","
                    (mapi (fun i k ->
                        lookup_id cx (i + 1)) cx));
            *)
            (*
            Util.eprintf
                "  $ ex: %a"
                (print_prop ())
                (opaque cx e);
            *)
            (*
            Util.eprintf
                "  $ ex: %a"
                (print_prop ())
                e;
            *)
            let cx, e = T.add_exp_substs cx e ss in
            Ex (cx, e)
        with Not_found ->
            Ph (ss, p)
        end
    | r -> r

let rec update_t phs env = function
    | Ref (x, t, r) ->
        Ref (x, update_t phs env t, update_r phs env r)
    | t ->
        T.tmap (update_t phs env) t

let update_e phs env = E.map (update_t phs env) env

let rec update_c phs e = function
    | CConj cs ->
        CConj (map (update_c phs e) cs)
    | CExists (vs, c) ->
        CExists (vs, update_c phs e c)
    | CAtom w ->
        CAtom (update_cc phs e w)
and update_cc phs e = function
    | CEq (env, t1, t2) ->
        let env, t1, t2 = update_triple
            phs e (env, t1, t2) in
        CEq (env, t1, t2)
    | CIsEq (env, t1, t2) ->
        let env, t1, t2 = update_triple
            phs e (env, t1, t2) in
        CIsEq (env, t1, t2)
    | CSub (env, t1, t2) ->
        let env, t1, t2 = update_triple
            phs e (env, t1, t2) in
        CSub (env, t1, t2)
    | CIsSub (env, t1, t2) ->
        let env, t1, t2 = update_triple
            phs e (env, t1, t2) in
        CIsSub (env, t1, t2)
    | c ->
        c
and update_triple phs e = function
    | env, t1, t2 ->
        update_e phs env,
        update_t phs e t1,
        update_t phs e t2

let update_tyvar_assignment phs env =
    E.tyvar_assignment := SMap.mapi
        begin fun _ (cxe, bvar, ot) ->
            let ot = match ot with
                | Some t -> Some (update_t phs env t)
                | None -> None in
            (cxe, bvar, ot)
        end
        !E.tyvar_assignment

let update_tcc phs (op, env, r1, r2) =
    (*
    Util.eprintf
        "  updating vc: %a"
        C.pp_tccs [env, r1, r2];
    *)
    let vc = op, update_e phs (env (* @ T.ss_to_env ss *)),
        update_r phs env r1,
        update_r phs env r2 in
    (*
    Util.eprintf
        "  ---: %a"
        C.pp_tccs [vc];
    *)
    update_tyvar_assignment phs env;  (** CHECK env *)
    vc


(****************************************************************************)
(** Processing TCCs                                                         *)
(****************************************************************************)


let nontrivial_vc = function
    | _, _, Ex (cx, e), Ex (cx', e')
            when Expr.Eq.expr e e' ->
        false
    | B.Implies, _, Ex (cx, e), Ex (cx', e') ->
        let e' = Smt.flatten_conj e' in
        (* let e = opaque cx e in *)
        (* let e = opaque cx e in *)
        (* let e' = opaque cx' e' in *)
        (*
        Util.eprintf
            "@[%a@]  -- @[%a@]"
            (print_prop ()) e (print_prop ()) e';
        *)
        let e_mem e es = List.exists
            (Expr.Eq.expr e) es in
        not
        begin match
                e.core,
                e'.core with
        | _, Internal B.TRUE ->
            true
        | List (Or, es),
          List (Or, es') ->
            List.for_all
                (fun e -> e_mem e es') es
        | List (And, es),
          List (And, es') ->
            List.for_all
                (fun e -> e_mem e es) es'
        | _,
          List (Or, es') ->
            e_mem e es'
        | List (Or, es),
          _ ->
            List.for_all
                (Expr.Eq.expr e') es
        | List (And, es),
          _ ->
            List.exists
                (Expr.Eq.expr e') es
        | _ ->
            false
        end
    | _ -> true

let vc_intro_elim = function
    | (B.Implies, env, Ex (cx, e), Ex (cx', e')) as c ->
        begin
        match
            e.core,
            e'.core with
        | List (Or, es), _ ->
            map
                (fun e -> B.Implies, env,
                    Ex (cx, e), Ex (cx', e'))
                es
        | _, List (And, es') ->
            map
                (fun e' -> B.Implies, env,
                    Ex (cx, e), Ex (cx', e'))
                es'
        | _ -> [c]
        end
    | c -> [c]

(** Encodes a TCC into a TLA+ proof obligation *)
let tccs_to_seq
        (op, env, r1, r2) :
            Typ_e.t * expr =
    let app op x y = Apply
        (Internal op |> noprops, [x ; y]) |> noprops in
    let e = match r1, r2 with
        | Ex (_, e1), Ex (_, e2) ->
            app op e1 e2
        | _ ->
            Util.eprintf
                "TCCs: @,@[%a@]"
                C.pp_tccs [op, env, r1, r2];
            failwith
                "some placeholder was not solved!"
        in
    (*** FIX relativization of
    typing context [env] *)
    (*
    let env, ths = env
    (* |> trim_env e *)
    |> List.filter
        (fun (x, t) ->
            mem x (Smt.fv_expr
                ((), E.to_scx env) e))
    |> mapi
        (fun i (x, t) ->
            let t, cx, p = T.to_predtyp
                (E.to_cx env)
                (Ix (i + 1) |> noprops)
                t in
            (x, t), (cx, p))
    |> split
    in
    let _, ths = split ths in
    let hs, c = Smt.deimpl e in
    let hs = ths @ hs in
    let e = if hs = []
        then c
        else app B.Implies
            (Smt.flatten_conj
                (List (And, hs) |> noprops)) c in
    env, e
    *)
    E.empty, e


(****************************************************************************)
(** Solving procedures                                                      *)
(****************************************************************************)


let remove_repeated_seq sqs =
    let e_mem e es = List.exists
        (fun (_, e') -> Expr.Eq.expr e e')
        es in
    List.fold_left
        (fun r (env, e) -> if e_mem e r then r else (env, e) :: r)
        []
        sqs


(** Solve type-correctness conditions *)
let solve_tccs tccs =
    if tccs = []
    then
        Smt.ifprint 2
            "** No TCCs to prove."
    else begin
        let tx = Sys.time () in
        let pr_answers =
            map tccs_to_seq tccs
            |> remove_repeated_seq
            |> map (fun (env, e) ->
                Smt.ifprint 2
                    "  TCC: @[<hov>%a |- %a@]"
                    E.pp env
                (Expr.Fmt.pp_print_expr
                    (E.to_scx env, Ctx.dot)) e;
                (env, e))
            (* |> map Why3_interface.solve *)
            |> map (fun _ -> "Not solved")
            in
        (*
        Util.eprintf
            " pr_answers: %s"
            (String.concat "," pr_answers);
        *)
        let valids, unknowns = List.partition
            (fun a -> a = "Valid")
            pr_answers in
        Smt.ifprint 2
            "** Solved TCCs in %5.3fs.%!"
                (Sys.time() -. tx);
        Smt.ifprint 2
            "-- TCCs: %d valids, %d unknown/fails"
            (List.length valids)
            (List.length unknowns)
    end


let remove_repeated_tccs tccs =
    let vc_mem (op, env, r1, r2) vs = List.exists
        (function (op', _, r1', r2') ->
            (* op = op' && *) T.eq_ref r1' r2')
        vs in
    List.fold_left
        (fun r vc -> if vc_mem vc r
            then r
            else vc :: r)
        [] tccs


(** Find solutions to placeholders.
[init_phs] = initial placeholders
[tccs] = verification conditions in the form (env, tref1, tref2)
[n] = total number of placeholders
*)
let solve_phs init_phs tccs n =
    if tccs <> []  then
        Smt.ifprint 3
            "-- TCCs: %a"
            C.pp_tccs tccs;

    let tx = Sys.time () in
    let phs = Typ_impgraph.solve
        init_phs tccs n in
    Smt.ifprint 2
        "** Solved => graph in %5.3fs.%!"
        (Sys.time() -. tx);

    C.tccs := map (update_tcc phs) !C.tccs;
    let total = List.length tccs in
    let tccs =
        map (update_tcc phs) tccs
        (* |> remove_repeated *)
        |> remove_repeated_tccs
        |> List.filter nontrivial_vc
        |> map vc_intro_elim |> List.flatten
        |> List.filter nontrivial_vc
        in
    if tccs <> [] then
        Smt.ifprint 3
            "-- TCCs: %a"
            C.pp_tccs tccs;
    Smt.ifprint 2
        "-- Type-correctness conditions: %d/%d (non-trivial/total)"
    (List.length tccs) total;
    solve_tccs tccs;
    phs

(****************************************************************************)
(** Solving procedures (2)                                                  *)
(****************************************************************************)


let _solve_c' (env, c) =
    let _solve_c (env, c) = (env, c)
        (* |> tap (fun (env, c) -> pp_env_c 1 env c) *)
        |> C.simplify
        |> unify_subs
        |> C.simplify
        (* |> tap (fun (env, c) -> ifprint 3
            "```` C.simplify"; pp_env_c 3 env c) *)
        in
    let env, c = (env, c)
        |> C.simplify
        ||> (if !Smt.typesystem_mode = 1
            then (fun c -> c)
            else C.base_to_ref)
        |> C.fix_env_c _solve_c
        in
    env, c

(****************************************************************************)


let solve (env, c) =
    let solve_c' env c =
        let tx = Sys.time () in
        let env, c = _solve_c' (env, c) in
        (* pp_env_c 3 env c; *)
        Smt.ifprint 2
            "** Solved in %5.3fs.%!"
            (Sys.time() -. tx);
        Smt.ifprint 2
            "---------------------------------------------------------------------------" ;
        env, c in

    let solve_and_update env c =
        C.phs := solve_phs
            !C.phs !C.tccs (mdom !C.phs_log);
        (*
        ifprint 2
            "++ Types: @[<hov>%a@]" E.pp env;
        *)
        let env = update_e !C.phs env in
        let c = update_c !C.phs env c in
        let env, c = C.simplify (env, c) in
        (* ifprint 1
            "++ Types: @[<hov>%a@]"
            E.pp env;
        *)
        C.tccs := [];
        C.phs := SMap.empty;
        env, c in

    Smt.ifprint 2
        "-- Solving == and <: ------------------------------------------------------" ;
    let env, c = solve_c' env c in
    (* ifprint 2 "-- Solved TCs to get main type ---------------------------------" ;  *)
    (* Smt.ifprint 2
        "TCs: %a"
        C.pp_tccs !C.tccs;
    *)
    let env, c = solve_and_update env c in
    let env, c = ground_refl (env, c) in

    E.tyvar_assignment_simp ();
    let typesmap = !Typ_e.tyvar_assignment in

    Smt.ifprint 2
        "\n** Final type assignment and constraint:";
    pp_env_c 2 env c;
    Smt.ifprint 2 "\n";
    (**************************************************************************)
    Smt.ifprint 2
        "-- Solving =?= and <? ------------------------------------------------------" ;
    let c = c
        |> C.iseq_to_eq  (** replace =?= by == *)
        |> C.issub_to_sub  (** replace <?  by <: *)
        in
    let env, c = solve_c' env c in
    let env, c = solve_and_update env c in
    let env, c = ground_refl (env, c) in
    let env, c = solve_residual (env, c) in

    pp_env_c 2 env c;

    let typesmap = SMap.mapi
        (fun _ (cxe, bvar, otyp) ->
            cxe, bvar, Option.map T.ref_to_base otyp)
        typesmap in

    (** This resets types for
    type-variables whose constraints
    were not satisfied.
    The type variables in residual
    constraints have no types *)
    let vs = match c with
          CExists (vs, _) -> vs
        | _ -> [] in
    let update (v, w) m = SMap.mapi
        begin fun a (cx, b, ot) ->
            (cx,
             b,
             if a = w then Some (TyVar ([], v)) else ot)
        end
        m
        in
    let typesmap = List.fold_left
        begin fun m v ->
            let _, set = Option.default
                (v, SSet.empty)
                (type_equiv_find v) in
            List.fold_left
                (fun m w -> update (v, w) m)
                m
                (SSet.elements set)
        end
        typesmap vs
    in

    typesmap, env, c

(****************************************************************************)
(** Type decoration                                                         *)
(****************************************************************************)


(** In [sq], replace annotations [TyVar a]
by the corresponding type from [typesmap]
*)
let decorate typesmap sq =
    let decor_env typesmap = function
    | TyVar (ss, a) ->
        begin
        try
            let _, _, otyp = SMap.find a typesmap in
            (Option.default (TyVar (ss, a)) otyp)
        with Not_found ->
            TyVar (ss, a)
        end
    | t -> t
    in
    (* let tvars, env = E.mk (Smt.fv ((), sq.context) sq) in *)
    let env, tvars = E.adj_hyps
        empty sq.context in
    let env = E.map (decor_env typesmap) env in

    let decor (* typesmap *) z =
    (*
    Util.eprintf
        " decor has type? %s "
        (if T.has_type z
            then "yes"
            else "nop");
    *)
    match Typ_t.optype z with
    | Some (TyVar (ss, a)) ->
        let _, _, otyp = SMap.find a typesmap in
        (*
        Util.eprintf
            "    found: @[<h2>\\%s : %a@]"
            a E.ppt (env, Option.default (TyVar a) otyp);
        *)
        z <<< (Option.default (TyVar (ss, a)) otyp)
    | _ -> z
    in

    let visitor = object (self : 'self)
        inherit [unit] Expr.Visit.map as super
        method expr scx e =
            match e.core with
            | SetSt (v, dom, ex) ->
                let v = decor v in
                let dom = self#expr scx dom in
                let scx = Expr.Visit.adj scx
                    (Fresh (
                        v,
                        Shape_expr,
                        Constant,
                        Bounded (dom, Visible))
                            @@ v) in
                let ex = self#expr scx ex in
                SetSt (v, dom, ex) @@ e
            | Choose (v, optdom, ex) ->
                let v = decor v in
                let optdom = Option.map
                    (self#expr scx) optdom in
                let h = match optdom with
                    | None ->
                        Fresh (
                            v,
                            Shape_expr,
                            Constant,
                            Unbounded) @@ v
                    | Some dom ->
                        Fresh (
                            v,
                            Shape_expr,
                            Constant,
                            Bounded (dom, Visible))
                                @@ v in
                let scx = Expr.Visit.adj scx h in
                let ex = self#expr scx ex in
                Choose (v, optdom, ex) @@ e
            | _ ->
                super#expr scx e
        method bounds scx bs =
            let bs = List.map
                begin
                fun (v, k, dom) ->
                    (*
                    Util.eprintf
                        "  decor_b @[<h2>\\%s : %a@]"
                        v.core E.ppt
                        (env,
                         Option.default
                            (TyVar "?")
                            (optype v));
                    *)
                    let v = decor v in
                    match dom with
                    | Domain d ->
                        (v, k, Domain (self#expr scx d))
                    | _ ->
                        (v, k, dom)
                end
                bs in
            let hs = List.map
                begin
                fun (v, k, _) ->
                    Fresh (
                        v,
                        Shape_expr,
                        k,
                        Unbounded) @@ v
                end
                bs in
            let scx = Expr.Visit.adjs scx hs in
            (scx, bs)
        method hyp scx h =
            (* let ph cx ff h = ignore
                (E.pp_print_hyp cx ff h) in *)
            match h.core with
            | Fresh (nm, shp, lc, dom) ->
                (*
                Util.eprintf
                    "<< ...|- %a%s : Bool >>"
                    (ph (snd scx, Ctx.dot)) h "";
                *)
                let nm = decor nm in
                let dom = match dom with
                    | Unbounded ->
                        Unbounded
                    | Bounded (r, rvis) ->
                        Bounded (self#expr scx r, rvis)
                    in
                let h = Fresh (nm, shp, lc, dom) @@ h in
                (Expr.Visit.adj scx h, h)
            | Flex s ->
                (*
                Util.eprintf
                    "<< ...|- %a%s : Bool >>"
                    (ph (snd scx, Ctx.dot)) h "";
                *)
                let s = decor s in
                let h = Flex s @@ h in
                (Expr.Visit.adj scx h, h)
            | _ ->
                super#hyp scx h
        end in
    let _, sq = visitor#sequent ((), sq.context) sq in
    env, sq

(****************************************************************************)

let type_construct sq =
    if !Smt.typesystem_mode = 0
    then sq
    else begin
        let tx = Sys.time () in
        Smt.ifprint 2
            "** Type construction...";
        (* subs := []; *)
        C.tccs := [];  (** Type-correctness conditions *)
        C.phs := SMap.empty;  (** Placeholders *)
        C.phs_log := SMap.empty;

        begin
        try
            (*
            Util.eprintf
                "sq^1: @[<hov2> |-@ %a@]"
                Fu.pp_print_minimal
                (Fu.Big (fun ff -> ignore (
                    E.pp_print_sequent
                        (sq.context, Ctx.dot)
                        ff sq)));
            *)
            let sqt, env, c = (
                if !Smt.typesystem_mode = 1
                    then Typ_cg1.cg
                    else Typ_cg2.cg)
                sq in
            (*
            Util.eprintf
                "sq^2: @[<hov2>%a |-@ %a@]"
                E.pp env Fu.pp_print_minimal
                (Fu.Big (fun ff -> ignore (
                    E.pp_print_sequent
                        (sqt.context, Ctx.dot)
                        ff sqt)));
            *)
            (* E.tyvar_assignment_pp 3; *)
            let typesmap, env, c = solve (env, c) in

            let env', sqt = decorate typesmap sqt in
            Smt.ifprint 1
                "** Type synthesis total time: %5.3fs"
                (Sys.time() -. tx);
            Smt.ifprint 1
                "sq^t: @[<hov2>%a ||-@ %a@]"
                E.pp env' Fu.pp_print_minimal
                (Fu.Big (fun ff -> ignore (
                    E.pp_print_sequent
                    (sqt.context, Ctx.dot)
                    ff sqt)));

            (* if c = CAtom CTrue
                then ()
                else begin
                    Smt.ifprint 1
                        "** Type constraint not satisfied:";
                        pp_env_c 1 env c;
                    raise Typeinf_failed
                end;
            *)

            (*
            Smt.ifprint 3
                "typesmap:";
            SMap.iter (fun k (cxe, bvar, typ) ->
                let cx, e = Option.default
                    ([], Internal B.TRUE %% [])
                    cxe in
                if bvar
                    then (
                        Util.eprintf
                            "@[<h2>\\%s : %a  ~  %a@]"
                            k E.ppt (env, Option.default (TyVar k) typ)
                            (E.pp_print_expr (T.to_scx cx, Ctx.dot)) e)
                    else ())
                typesmap;
            *)

            sqt
        with Typeinf_failed ->
            Smt.ifprint 1
                "** Type synthesis failed. Using untyped encoding.";
            sq
        end
    end
