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
open List

module B = Builtin
module Smt = Smtcommons

(****************************************************************************)

open Format
open Fmtutil

let ident ppf s = fprintf ppf "%s" s

open Typ_t
open Typ_e
module T = Typ_t
module E = Typ_e

(*
let print_hyp h = match h.core with
    | Fresh (nm, _, _, Bounded (d, _)) ->
        sprintf
            "Fresh %s \\in %s"
            nm.core
            (Expr.Fmt.string_of_expr Deque.empty d)
    | Fresh (nm, _, _, Unbounded) ->
        sprintf "Fresh %s" nm.core
    | Flex nm ->
        sprintf "Flex %s" nm.core
    | Defn ({core=Operator (nm, _)
            | Instance (nm, _)
            | Bpragma(nm, _, _)
            | Recursive (nm, _)},
            _, _, _) ->
        sprintf "Defn %s..." nm.core
    | Fact (_, _) ->
        "Fact ..."
*)

(****************************************************************************)
(** Subst applied during subtype unification *)
(****************************************************************************)
type substitutions = (string * T.t) list

(****************************************************************************)
(** Type Constraints                                                        *)
(****************************************************************************)

type tc =
    (** Atomic constraints *)
    | CTrue
    | CFalse
    | CEq of E.t * T.t * T.t
        (** Equality unification *)
    | CIsEq of E.t * T.t * T.t
        (** Syntactic equality on ground types *)
    | CSub of E.t * T.t * T.t
        (** Subtyping unification *)
    | CIsSub of E.t * T.t * T.t
        (** Syntactic subtype on ground types *)
and t =
    (** Structural constraints *)
    | CAtom of tc
    | CConj of t list
    | CExists of string list * t

let rec pp ppf (env, c) =
    match c with
    | CAtom c ->
        ppc ppf (env, c)
    | CConj cs ->
        let pp_print_elem ppf = fprintf
            ppf "@[<h>/\\ %a@]" pp in
        fprintf
            ppf
            "@[<v>%a@]"
            (pp_print_delimited
                ~sep:pp_print_cut
                pp_print_elem)
            (List.map (fun c -> env, c) cs)
    | CExists (vs, c) ->
        let vs = List.map
            (fun v -> "\\" ^ v) vs in
        fprintf
            ppf
            "@[@[<h>\\E %a@].@,  @[<v2>%a@]@]"
            (pp_print_delimited ident)
            vs pp (env, c)
and ppc ppf = function
    | _, CTrue ->
        fprintf ppf "true"
    | _, CFalse ->
        fprintf ppf "false"
    | env, CEq (e, t1, t2) ->
        pp_catom ppf env e "==" t1 t2
    | env, CIsEq (e, t1, t2) ->
        pp_catom ppf env e "=?=" t1 t2
    | env, CSub (e, t1, t2) ->
        pp_catom ppf env e "<:" t1 t2
    | env, CIsSub (e, t1, t2) ->
        pp_catom ppf env e "<?" t1 t2
and pp_catom ppf env e sym t1 t2 =
    let env = env $! e in
    fprintf
        ppf
        "@[<hov>%a@[<hov2>%a %s %a@]@]"
        pp_env e E.ppt (env, t1)
        sym E.ppt (env, t2)
and pp_env ppf = function
    | env ->
        if env = E.empty
            then ()
            else fprintf
                ppf
                "@[<hov>%a@, |-  @]"
                E.pp env

let mk_atoms ccs = List.map
    (fun w -> CAtom w) ccs

let mk_cs = function
    | [] -> CAtom CTrue
    | [c] -> c
    | cs -> CConj cs

let mk_ex = function
    | _, [] -> CAtom CTrue
    | _, [CAtom CTrue] -> CAtom CTrue
    | [], cs -> mk_cs cs
    | vs, cs -> CExists (vs, mk_cs cs)

let rec fv = function
    | CAtom c -> cfv c
    | CConj cs ->
        (*
        fold_left
            (fun xs x -> (fv x) @ xs)
            [] cs
        *)
        flatten (List.map fv cs)
    | CExists (vs, c) ->
        Smt.list_minus (fv c) vs
and cfv = function
    | CTrue
    | CFalse ->
        []
    | CEq (env, t1, t2)
    | CIsEq (env, t1, t2) ->
        T.fv t1 @
        T.fv t2
    | CSub (env, t1, t2)
    | CIsSub (env, t1, t2) ->
        E.tyvars env @
        T.fv t1 @
        T.fv t2

let rec eq c1 c2 =
    match c1, c2 with
    | CAtom c1,
      CAtom c2 ->
        eqc c1 c2
    | CConj xs,
      CConj ys ->
        (try
            for_all2 eq xs ys
        with _ ->
            false)
    | CExists (xs, c1),
      CExists (ys, c2) ->
        for_all (fun a -> mem a ys) xs &&
        for_all (fun a -> mem a xs) ys &&
        eq c1 c2
    | _ ->
        false
and eqc c1 c2 =
    match c1, c2 with
    | CTrue, CTrue -> true
    | CFalse, CFalse -> true
    | CEq (env, t1, t2),
      CEq (env', t1', t2') ->
        E.eq env env' &&
        T.eq t1 t1' &&
        T.eq t2 t2'
    | CIsEq (env, t1, t2),
      CIsEq (env', t1', t2') ->
        E.eq env env' &&
        T.eq t1 t1' &&
        T.eq t2 t2'
    | CSub (env, t1, t2),
      CSub (env', t1', t2') ->
        E.eq env env' &&
        T.eq t1 t1' &&
        T.eq t2 t2'
    | CIsSub (env, t1, t2),
      CIsSub (env', t1', t2') ->
        E.eq env env' &&
        T.eq t1 t1' &&
        T.eq t2 t2'
    | _ ->
        false

(** Apply type variable substitution [a -> t] to a constraint *)
let rec subst (a:string) (t:T.t) = function
    | CAtom c -> CAtom (substc a t c)
    | CConj cs ->
        CConj (fold_left
            (fun xs x -> xs @ [subst a t x])
            [] cs)
        (*
        CConj (fold_left
            (fun xs x -> subst a t x :: xs)
            [] cs)
        *)
    | CExists (vs, c) ->
        CExists (vs, subst a t c)
and substc (a:string) (t:T.t) = function
    | CEq (env, t1, t2) ->
        CEq (
            E.subst a t env,
            T.subst a t t1,
            T.subst a t t2)
    | CIsEq (env, t1, t2) ->
        CIsEq (
            E.subst a t env,
            T.subst a t t1,
            T.subst a t t2)
    | CSub (env, t1, t2) ->
        CSub (
            E.subst a t env,
            T.subst a t t1,
            T.subst a t t2)
    | CIsSub (env, t1, t2) ->
        CIsSub (
            E.subst a t env,
            T.subst a t t1,
            T.subst a t t2)
    | c -> c

(** Extension of [T.vsubst] for constraints *)
let rec vsubst (a:string) (b:string) = function
    | CAtom c ->
        CAtom (vsubstc a b c)
    | CConj cs ->
        (*
        CConj (fold_left
            (fun xs x -> vsubst a b x :: xs)
            [] cs)
        *)
        CConj (List.map (vsubst a b) cs)
    | CExists (vs, c) ->
        CExists (vs, vsubst a b c)
and vsubstc a b = function
    | CEq (env, t1, t2) ->
        CEq (
            E.vsubst a b env,
            T.vsubst a b t1,
            T.vsubst a b t2)
    | CIsEq (env, t1, t2) ->
        CIsEq (
            E.vsubst a b env,
            T.vsubst a b t1,
            T.vsubst a b t2)
    | CSub (env, t1, t2) ->
        CSub (
            E.vsubst a b env,
            T.vsubst a b t1,
            T.vsubst a b t2)
    | CIsSub (env, t1, t2) ->
        CIsSub (
            E.vsubst a b env,
            T.vsubst a b t1,
            T.vsubst a b t2)
    | c -> c

(****************************************************************************)
(* Type-Correctness Conditions (TCC)                                        *)
(****************************************************************************)

type tcc_raw = Builtin.builtin * Typ_e.t * tref * tref
    (** Unprocessed TCAtom *)

let tccs : tcc_raw list ref = ref []

let pp_tcc ppf (op, env, r1, r2) =
    fprintf
        ppf
        "@[<hov2>* %a@, |- @[<hov2>%a@   %s   %a@]@]"
        E.pp env E.pp_ref (env, r1)
        (if op = B.Equiv
            then "<==>"
            else "==>")
        E.pp_ref (env, r2)

let pp_tccs ppf tccs =
    fprintf
        ppf
        "@[<v>%a@]"
        (pp_print_delimited
            ~sep:pp_print_cut pp_tcc)
        tccs

let tcc_subst a t (op, env, r1, r2) = (
    op,
    E.subst a t env,
    T.subst_ref a t r1,
    T.subst_ref a t r2)

(*
let apply_substs_tccs tccs ss =
    fold_left
        (fun tccs' (a, t) ->
            List.map (tcc_subst a t) tccs')
        tccs
        ss  (** FIX: subst exprs *)
*)

(****************************************************************************)
(* Atomic constraint simplification                                         *)
(* Generation of TCCs from Ref <: Ref and Ref == Ref                        *)
(****************************************************************************)

let _simp_cc = function
    | CEq (env, t1, t2) ->
        let env = E.simplify env in
        let t1 = T.simplify t1 in
        let t2 = T.simplify t2 in
        if T.eq t1 t2 then [] else
        begin
        match t1, t2 with
        | Set t1,
          Set t2 ->
            [CEq (env, t1, t2)]
        | Func (_, s1, s2),
          Func (_, t1, t2) ->
            [CEq (env, t1, s1); CEq (env, s2, t2)]
        | Ref (x, t, r1), Ref (y, t', r2) ->
            let ss, x = match r1, r2 with
                | Ex (cx1, e1),
                  Ex (cx2, e2) ->
                    [], x
                | Ph (ss, p),
                  Ph (ss', q) ->
                    ss @ ss', x
                    (** Can this case happen? *)
                | _,
                  Ph (ss, p) ->
                    ss, y
                | Ph (ss, p),
                  _ ->
                    ss, x in
            let env = env $!
                (E.adj (E.ss_to_env ss) (x, t)) in
            tccs := (B.Equiv, env, r1, r2) :: !tccs;
            [CEq (env, t, t')]
        | _
                when T.unify_fails t1 t2 ->
            Smt.ifprint 2
                "Unification failed for@, @[<v>%a@ ==@ %a@]"
                E.ppt (env, t1)
                E.ppt (env, t2);
            [CFalse]
        | _ ->
            [CEq (env, t1, t2)]
        end
    | CIsEq (env, t1, t2) ->
        let env = E.simplify env in
        let t1 = T.simplify t1 in
        let t2 = T.simplify t2 in
        if T.eq t1 t2 then [] else
        begin
        match t1, t2 with
        | Set t1,
          Set t2 ->
            [CIsEq (env, t1, t2)]
        | Func (_, s1, s2),
          Func (_, t1, t2) ->
            [CIsEq (env, t1, s1);
             CIsEq (env, s2, t2)]
        | _
                when T.unify_fails t1 t2 ->
            Smt.ifprint 2
                "Unification failed for@, @[<v>%a@ ==@ %a@]"
                E.ppt (env, t1)
                E.ppt (env, t2);
            [CFalse]
        | _ ->
            [CIsEq (env, t1, t2)]
        end
    | CSub (env, t1, t2) ->
        let env = E.simplify env in
        let t1 = T.simplify t1 in
        let t2 = T.simplify t2 in
        if T.eq t1 t2
            then []
            else begin
                match t1, t2 with
                | Set t1,
                  Set t2 ->
                    [CSub (env, t1, t2)]
                | Func (x, s1, s2),
                  Func (_, t1, t2) ->
                    [CSub (env, t1, s1);
                     CSub (E.adj env (x, t1), s2, t2)]
                | Ref (_, t, Ex _),
                  Ref (_, t', Ex (_, {core=Internal B.TRUE})) ->
                    [CEq (env, t, t')]
                | Ref (_, t, Ex _),
                  t'
                        when T.eq t t' ->
                    []
                | Ref (x, t, r1),
                  Ref (y, t', r2) ->
                    let ss, _ =
                    match r1, r2 with
                    | Ex _, Ex _ ->
                        [], x
                    (*
                    | Ex (cx1, e1), Ex (cx2, e2) ->
                        [], x
                    *)
                    | Ph (ss, p),
                      Ph (ss', q) ->
                        ss @ ss', x
                        (** Can this case happen? *)
                    | _,
                      Ph (ss, p) ->
                        ss, y
                    | Ph (ss, p),
                      _ ->
                        ss, x
                    in
                    let z = Smt.fresh_name () in
                    (* let r1 = T.add_x_ref z t r1 in *)
                    (* let r2 = T.add_x_ref z t r2 in *)
                    (* let env = (E.adj env (x, t))
                        @ (T.ss_to_env ss) in *)
                    let env = env $!
                        (E.adj (E.ss_to_env ss) (z, t)) in
                    let vc = (B.Implies, env, r1, r2) in
                    tccs := vc :: !tccs;
                    [CSub (env, t, t')]
                | _ when T.unify_fails t1 t2 ->
                    Smt.ifprint 2
                        "Unification failed for@, @[<v>%a@ ==@ %a@]"
                        E.ppt (env, t1)
                        E.ppt (env, t2);
                    [CFalse]
                | _ ->
                    [CSub (env, t1, t2)]
            end
    | CIsSub (env, t1, t2) ->
        let env = E.simplify env in
        let t1 = T.simplify t1 in
        let t2 = T.simplify t2 in
        if T.eq t1 t2
            then []
            else begin
                match t1, t2 with
                | Set t1,
                  Set t2 ->
                    [CIsSub (env, t1, t2)]
                | Func (x, s1, s2),
                  Func (_, t1, t2) ->
                    [CIsSub (env, t1, s1);
                     CIsSub (E.adj env (x, t1), s2, t2)]
                | Ref (_, t, Ex _),
                  Ref (_, t', Ex (_, {core=Internal B.TRUE})) ->
                    [CIsEq (env, t, t')]
                | Ref (_, t, Ex _), t'
                        when T.eq t t' ->
                    []
                | _
                        when T.unify_fails t1 t2 ->
                    Smt.ifprint 2
                        "Unification failed for@, @[<v>%a@ ==@ %a@]"
                    E.ppt (env, t1)
                    E.ppt (env, t2);
                    [CFalse]
                | _ ->
                    [CIsSub (env, t1, t2)]
            end
    | CTrue -> []
    | c -> [c]

let rec simp_ccs cs =
    let eq_cs cs cs' = length cs =
        length cs' &&
        for_all2 (fun c c' -> eqc c c') cs cs' in
    let cs' = flatten (List.map _simp_cc cs) in
    if eq_cs cs cs'
        then cs
        else simp_ccs cs'

let rec simp_c = function
    | CAtom w ->
        mk_cs (mk_atoms (_simp_cc w))
    | CConj cs ->
        let cs = List.map
            (function
                  CConj cs -> cs
                | c -> [c])
            cs
            |> flatten in
        let cs = filter (fun c -> c <> CAtom CTrue) cs in
        mk_cs (List.map simp_c cs)
    | CExists (vs, c) ->
        mk_ex (vs, [simp_c c])

(****************************************************************************)
(* Equality constraint unification                                          *)
(****************************************************************************)

let rec subs_ss a t = function
    | [] -> []
    | (b, t') :: ss ->
        (b, T.subst a t t')
        :: subs_ss a t ss

(** Apply substitution-function [f] to [xs] with substitution [ss] *)
let app_ss f xs ss = fold_left
    (fun xs (a, t) -> List.map (f a t) xs) xs ss

let apply_ss ss (env, vs, (cs:t list)) =
    (*
    let pp_subst ppf (a, t) = fprintf
        ppf
        "@[<h>[\\%s <- %a]@]"
        a E.ppt (env, t) in
    Smt.ifprint 1 "  -- ss: @[%a@]"
    (pp_print_delimited pp_subst) ss;
    *)
    let dom_ss ss = List.map (fun (a, _) -> a) ss in
    let ss = fold_left
        begin fun ss (a, t) ->
            if mem a (dom_ss ss)
                then ss
                else (a, t) :: ss  (* @ [(a, t)] *)
        end
        [] ss in
    let ss = fold_left
        (fun ss (a, t) -> subs_ss a t ss)
        ss ss in
    (** Apply substitution [ss] to [ss] *)
    let env = fold_left
        (fun env (a, t) -> E.subst a t env)
        env ss in
    iter (fun (a, t) -> E.tyvar_assignment_subst a t) ss;
    iter (fun (a, t) -> iter (E.type_equiv_union a) (T.fv t)) ss;
    (* let tx = Sys.time () in *)
    let vs = Smt.list_minus vs (dom_ss ss) in
    let cs = List.map
        begin fun c ->
            fold_left
                (fun c' (a, t) -> subst a t c' |> simp_c)
                c ss
        end
        cs in
    (*
    Smt.ifprint 1
        "  ## app_ss substc <<%d x %d>> in %5.3fs.%!"
        (List.length ss)
        (List.length cs)
        (Sys.time() -. tx);
    *)
    let env = E.simplify env in
    let cs = List.map simp_c cs in
    env, vs, cs

let rec rewrite_eqs (env, vs, cs) =
    (*
    Util.eprintf "  @[<hov2>rewrite_eqs @[<h>%a |- EX %s. %a@]@]"
        E.pp env (String.concat "," vs)
        pp (env, CConj cs);
    *)
    let rec collect_ss vs = function
    | CAtom w :: cs ->
        (* let w = simp_cc w in *)
        let collect_bound env' a t =
            if T.occurs a t then begin
                let cxe, _, _ = SMap.find a !E.tyvar_assignment in
                let cx, e = Option.default
                    ([], Internal B.TRUE %% []) cxe in
                Smt.ifprint 1
                    "Recursive equality %a where \\%s is the type of %a"
                    ppc (env $! env', w) a
                    (Expr.Fmt.pp_print_expr (Smt.to_scx cx, Ctx.dot)) e;
                raise Typeinf_failed
            end else
                (a, t) :: collect_ss vs cs in
        begin
        match w with
        | CEq (e, TyVar (_, a), TyVar (_, a'))  (** ignore this case *)
                when a = a' ->
            collect_ss vs cs
        | CEq (env', TyVar (_, a), t)
                when mem a vs
            (** The type variable [a] is one
            of the bound variables [vs] *)
            (* && not (mem a (T.fv t))  *)
            (* && not (mem a (E.finds e (expr_fv t)))  *)
            ->
            collect_bound env' a t
        | CEq (env', t, TyVar (_, a))
                when mem a vs ->
            collect_bound env' a t
        (*
        | CEq (e, t, TyVar (_, a))
        | CEq (e, TyVar (_, a), t)
                when T.is_atomic_type t && mem a vs ->
            (a, t) :: collect_ss vs cs
        *)
        | _ ->
            collect_ss vs cs
        end
    (** In case of CExists,
    type variables have all different ids,
    so variable capture does not happen. *)
    | _ :: cs ->
        collect_ss vs cs
    | [] -> []
    in
    let ss = collect_ss vs cs in  (** [ss] = substitutions,
        bound by variables [vs] *)
    if ss = []
        then (env, vs, cs)
        else begin
            let env, vs, cs = apply_ss ss (env, vs, cs) in
            rewrite_eqs (env, vs, cs)
        end

(****************************************************************************)
(* Constraint simplification                                                *)
(****************************************************************************)

(** Simplify by applying rewriting function
[rw_func] to constraint [env, c] *)
let rec rw_c rw_func (env, c) =
    let env = E.simplify env in
    let c = simp_c c in
    begin
    match c with
    | CExists (vs, c) ->
        let env, c = rw_c rw_func (env, c) in
        begin
        match c with
        | CExists (vs', c) ->
            (env,
             mk_ex (vs @ vs', [c]))
            |> rw_c rw_func
        | CConj cs ->
            let env, vs, cs = rw_func (env, vs, cs) in
            env,
            (mk_ex (vs, cs) |> simp_c)
        | CAtom _ ->
            (* env, mk_ex (vs, [c]) *)
            let env, vs, cs = rw_func (env, vs, [c]) in
            env,
            (mk_ex (vs, cs) |> simp_c)
        end
    | CConj cs ->
        let cs = List.map
            (fun c -> snd (rw_c rw_func (env, c)))
            cs in
        env, mk_cs cs
    | CAtom w ->
        env,
        mk_cs (mk_atoms (simp_ccs [w]))
    end

(****************************************************************************)

(** Apply [f] to [x] until reaching a fixpoint *)
let rec fix eq f x =
    let x' = f x in
    if eq x x'
        then x
        else fix eq f x'

let fix_env_c f (x:Typ_e.t * t) =
    let eq (env1, c1) (env2, c2) =
        E.eq env1 env2 &&
        eq c1 c2 in
    fix eq f x

(****************************************************************************)

(** Flatten constraint, ie pull all quantifiers out *)
let rec flatten_c c : string list * tc list =
    match c with
    | CAtom c -> [], [c]
    | CExists (vs', c) ->
        let vs, cs = flatten_c c in
        vs' @ vs, cs
    | CConj cs ->
        let vss, css = split (List.map flatten_c cs) in
        flatten vss, flatten css

let simplify (env, c) =
    (* let tx = Sys.time () in   *)
    let (env, c) = (env, c)
        |> fix_env_c (rw_c rewrite_eqs) in
    let vs, ccs = flatten_c c in
    let c = mk_ex (vs, mk_atoms ccs) in
    let (env, c) = (env, c)
        |> fix_env_c (rw_c rewrite_eqs) in
    (* Smt.ifprint 1 "** C.simplify in %5.3fs.%!" (Sys.time() -. tx); *)
    (env, c)

(****************************************************************************)

let map_c f = function
    | CConj cs -> CConj (List.map f cs)
    | CExists (vs, c) -> CExists (vs, f c)
    | CAtom w -> CAtom w

let map_cc f = function
    | CEq (e, t1, t2) -> CEq (e, f t1, f t2)
    | CIsEq (e, t1, t2) -> CIsEq (e, f t1, f t2)
    | CSub (e, t1, t2) -> CSub (e, f t1, f t2)
    | CIsSub (e, t1, t2) -> CIsSub (e, f t1, f t2)
    | w -> w

(** Transforms [t1 =?= t2] to [t1 == t2] *)
let rec iseq_to_eq = function
    | CAtom (CIsEq (e, t1, t2)) -> CAtom (CEq (e, t1, t2))
    | c -> map_c iseq_to_eq c

(** Transforms [t1 <? t2] to [t1 <: t2] *)
let rec issub_to_sub = function
    | CAtom (CIsSub (e, t1, t2)) -> CAtom (CSub (e, t1, t2))
    | c -> map_c issub_to_sub c

(** From type [t] to [{ x : t | TRUE}] *)
let rec base_to_ref = function
    | CAtom w -> CAtom (map_cc T.base_to_ref w)
    | c -> map_c base_to_ref c

let rec c_length = function
    | CAtom _ -> 1
    | CExists (_, c) -> c_length c
    | CConj cs -> fold_left (fun r x -> c_length x + r) 0 cs

(** [cg_mode]: Used only for contraint generation *)
type cg_mode =
    | OnlySafe  (* Only safe types, no unification *)
    | TypHyp  (* As a typing hypothesis *)


(****************************************************************************)
(* Placeholders                                                             *)
(****************************************************************************)

module SMap = Typ_e.SMap

let ctr_phs = ref 0
let fresh_pholder () = "@" ^ string_of_int (
    incr ctr_phs; !ctr_phs)

let phs = ref SMap.empty
let phs_log = ref SMap.empty
let new_ph info =
    let id = fresh_pholder () in
    (*
    begin
    match info with
    | Some ((x, t), env, cx, e) ->
        let fvs = T.expr_fv (Ref (x, t, Ex (cx, e))) in
        (* let fvs = map (fun v -> v, SMap.find) fvs in *)
        Util.eprintf
            "  @[<h6>** new_ph %s == %s:%a + %a + %s |- %a@]"
            id x
            E.ppt (env, t)
            E.pp env
            (* (String.concat "," (free_vars (T.add_x_ctx x t cx) e)) *)
            (String.concat "," fvs)
            (* (String.concat "," xs) *) (* x E.ppt (env, t) *)
            (print_prop ()) (opaque (T.add_x_ctx x t cx) e)
    | None ->
        Util.eprintf
            "  @[<h6>** new_ph %s == ?@]"
            id
    end;
    *)
    phs_log := SMap.add id info !phs_log;
    (* let cx = [
        Fresh (
            id,
            Shape_expr,
            k,
            Unbounded)
                |> noprops] in *)
    (* (cx, Opaque id |> noprops) *)
    id

let pp_cx ppf cx =
    Util.eprintf
        "@[<h>cx: %a@]"
        (Fmtutil.pp_print_delimited Format.pp_print_string)
        (mapi (fun i k -> Smtcommons.lookup_id cx (i + 1)) cx)

(*
let pp_ph p (cx, ex) =
    Util.eprintf
        "    @[%s == @[[%s]@] |- @[<hov>%a@]@]" p
        (String.concat "," (mapi (fun i k -> lookup_id cx (i + 1)) cx))
        (* pp_cx cx  *)
        (Smt.print_prop ()) ((* opaque cx *) ex) *)

let pp_ph p (cx, ex) =
    Smt.ifprint 3
        "@[<hov2># [%s] %a |- @[<hov>%a@]@]" p
        (*
        (String.concat ","
        (mapi (fun i k -> Smtcommons.lookup_id cx (i + 1)) cx))
        *)
        pp_cx cx
        (* (Smt.print_prop ()) ex *)
        (Typ_e.pp_print_expr (Smtcommons.to_scx cx, Ctx.dot)) ex
