(*
 * backend/smt3.ml --- ATP/SMT backend.
 *
 * Author: Hernán Vanzetto <hernanv@gmail.com>
 *
 * Copyright (C) 2011-2014  INRIA and Microsoft Corporation
 *)
open Ext
open Format
open Fmtutil
open Tla_parser
open Property

open Expr.T
open Expr.Subst
open Proof.T

module Smt = Smtcommons
module B = Builtin
module Dq = Deque
module SSet = Smt.SSet
module SMap = Smt.SMap
module T = Typ_t
module E = Typ_e

open Axioms


let ( |>> ) = Smt.( |>> )
let ( ||> ) = Smt.( ||> )
let map = List.map



(* Translation: mapping from basic TLA+
(purely first-order) to target language
(defined by [!Smt.mode]).
*)


let set_map () = match !Smt.mode with
    | Smt.Yices -> Axioms.yices_map
    | Smt.Spass -> Axioms.dfg_map
    | Smt.Fof -> Axioms.fof_map
    | _ -> Axioms.smtlib_map


let rec pp_apply (ecx:Ectx.t) ff op args =
    let m = set_map () in
    let pp_id ecx ff id args =
    match args with
        | [] -> pp_print_string ff id
        | _  -> m.apply ff id (to_fol_expr ecx) args
    in
    match op.core with
    | Ix n ->
        let id = Ectx.smt_id ecx n in
        (* pp_apply ecx ff { op with core = Opaque id } args *)
        pp_id ecx ff id args
    | Opaque id ->
        let id = if Smt.has_boundvar op then
                Tla_parser.pickle id
            else
                Smt.smt_pickle false id in
        pp_id ecx ff id args
    | Internal b ->
        let atomic op = pp_print_string ff op
        and nonatomic id args =
            m.apply ff id (to_fol_expr ecx) args
        and infix id args =
            m.apply ~isinfix:true ff id (to_fol_expr ecx) args
        (* and unsupp o =
            Errors.warning := true;
            Errors.set op ("TLAPM does not handle "^o);
            Util.eprintf ~at:op "%s not supported" o ;
            failwith "Backend.SMT.pp_apply"
        *)
        in
        let arith fmt b args =
            if fmt && !Smt.mode != Smt.Spass
                && !Smt.mode != Smt.Fof
            then
                infix (m.op b) args
            else
                nonatomic (Axioms.m_tla b) args
        in
        begin match b, args with
        | B.TRUE, []
        | B.FALSE, [] ->
            atomic (m.op b)
        | B.Implies, _
        | B.Equiv, _
        | B.Conj, _
        | B.Disj, _
        | B.Eq, _ ->
            infix (m.op b) args
        | B.Neg, _ ->
            nonatomic (m.op b) args
        | B.STRING, []
        | B.BOOLEAN, [] ->
            atomic (Axioms.m_tla b)
        | B.SUBSET, [e]
        | B.UNION, [e]
        | B.DOMAIN, [e] ->
            nonatomic (Axioms.m_tla b) args
        | B.Mem, [ex ; ({core = Internal B.Int})]
                when !Smt.mode = Smt.Fof
                    || !Smt.mode = Smt.Spass ->
            nonatomic "isint" [ex]
        | B.Mem, [e ; ({core = Internal B.Int})]
                when T.is_int (fst ecx) e ->
            atomic (m.op B.TRUE)
        | B.Mem, [e ; f] ->
            nonatomic (Axioms.m_tla b) args
        | B.Nat, []
        | B.Int, []
        | B.Real, [] ->
            atomic (Axioms.m_tla b)
        | (B.Plus | B.Minus | B.Times | B.Exp), [e; f] ->
            arith (Smt.fmt_as_int op) b args
        | (B.Quotient | B.Remainder), [e ; f] ->
            arith (Smt.fmt_as_int op) b args
        | B.Uminus, [ex] ->
            if (Smt.fmt_as_int op) then
                m.uminus ff (to_fol_expr ecx) ex
                (* fprintf ff "(- %a)" (to_fol_expr ecx) ex *)
            else
                nonatomic "tla__uminus" args
        | B.Ratio, [e; f] ->
            nonatomic (Axioms.m_tla b) [e; f]
        | (B.Lteq | B.Lt | B.Gteq | B.Gt), [e; f] ->
            arith (Smt.fmt_as_int op) b args
        | B.Range, [e; f] ->
            nonatomic (Axioms.m_tla b) args
        | B.Seq, [e] ->
            nonatomic "tla__Seq" [e]
        | B.Len, [e] ->
            nonatomic "tla__Len" [e]
        | B.BSeq, [e] ->
            nonatomic "tla__BSeq" [e]
        | B.Cat, [e; f] ->
            nonatomic "tla__concat" [e; f]
        | B.Append, [e; f] ->
            nonatomic "tla__Append" [e; f]
        | B.Head, [e] ->
            nonatomic "tla__Head" [e]
        | B.Tail, [e] ->
            nonatomic "tla__Tail" [e]
        | B.SubSeq, [e; m; n] ->
            nonatomic "tla__SubSeq" [e; m; n]
        | B.SelectSeq, [e; f] ->
            nonatomic "tla__SelectSeq" [e; f]
        | _ ->
            Errors.set op "smt3.ml: Arity mismatch";
            Util.eprintf ~at:op "Arity mismatch" ;
            failwith "Backend.SMT.fmt_apply"
        end
    | _ -> assert false


and fmt_expr (ecx:Ectx.t) e =
    let m = set_map () in
    let unsupp o =
        Errors.warning := true;
        Errors.set e ("TLAPM does not handle "^o);
        Util.eprintf ~at:e "%s not supported" o ;
        failwith "Backend.SMT.fmt_expr"
    in
    (* Util.eprintf "___ %a"
        (Expr.Fmt.pp_print_expr (Dq.empty, Ctx.dot)) e ;
    *)
    match e.core with
    | ( Ix _ | Internal _ | Opaque _ | Lambda _ ) ->
        Fu.Atm (fun ff -> pp_apply ecx ff e [])
    | Apply (op, args) ->
        Fu.Atm (fun ff -> pp_apply ecx ff op args)
    | If (e, f, g) ->
        Fu.Big begin fun ff ->
            m.apply ff (Option.get m.ite) (to_fol_expr ecx) [e; f; g]
        end
    | List (Refs, []) ->
        Errors.bug ~at:e
            "Backend.SMT.fmt_exp: internal error (List)"
    | List (_, [e]) ->
        fmt_expr ecx e
    | List (q, es) ->
        let rep =
            match q with
            | And | Refs -> m.op B.Conj
            | Or -> m.op B.Disj
        in
        Fu.Big begin fun ff ->
            m.apply ~isinfix:true
                ff rep (to_fol_expr ecx) es
        end
    | Quant (q, [], e) ->
        fmt_expr ecx e
    | Quant (q, bs, {core = Quant (q', bs', ex)})
            when q = q' ->
        fmt_expr ecx (Quant (q, bs @ bs', ex) @@ e)
    | Quant (q, bs, ex) ->
        (** Assumption: [ex] is [Smt.unditto]'ed and
        [bs] has [No_domain]s.
        *)
        let ecx, vss, _ = Ectx.adj_bs ecx bs in
        let pat = if Smt.has_pattern e then
                Some (Smt.get_pattern e)
            else
                None in
        Fu.Big (fun ff ->
            m.quant ff q pat vss (to_fol_expr ecx) ex)
    | SetEnum [] ->
        Fu.Atm (fun ff -> fprintf ff "tla__emptyset")
    | Tuple [] ->
        Fu.Atm (fun ff -> fprintf ff "tla__tuple0")
    | SetEnum es ->
        let n = List.length es in
        Fu.Big (fun ff ->
            fprintf ff "(tla__set_%d" n;
            List.iter (fun x -> fprintf ff " %a" (to_fol_expr ecx) x) es;
            fprintf ff ")";)
    | Arrow (a, b) ->
        Fu.Atm begin fun ff ->
            m.apply ff "tla__FuncSet"
                (to_fol_expr ecx) [a; b]
        end
    | Record rs ->
        let fs, es = List.split rs in
        Fu.Atm begin fun ff ->
            (* let print_pair (f, v) =
                fprintf ff " %a %a"
                    (pp_print_expr sd cx) (String f @@ e)
                    (pp_print_expr sd cx) v
            in
            *)
            m.apply ff
                (sprintf "tla__record__%d" (Smt.get_recid fs))
                (to_fol_expr ecx) es
            (* fprintf ff "(tla__record__%d %a)" (Smt.get_recid fs)
                (pp_print_delimited ~sep:pp_print_space
                    (to_fol_expr ecx)) es
            *)
            (* List.iter print_pair rs; *)
        end
    | Dot (ex, h) ->
        Fu.Atm begin fun ff ->
            m.apply ff "tla__Dot" (to_fol_expr ecx) [ex; String h %% []]
        end
    (* | Dot (ex, h) ->
        fmt_expr ecx (FcnApp (ex, [String h @@ e]) @@ e)
    *)
    | String s ->
        (* Fu.Atm (fun ff -> fprintf ff "(str2u %s)" (Smt.mk_string s)) *)
        Fu.Atm (fun ff -> fprintf ff "%s" (Smt.mk_string s))
    | Num (n, "") when n.[0] = '-' ->
        Fu.Atm (fun ff ->
            m.uminus ff pp_print_string
            (String.sub n 1 ((String.length n) - 1)))
    | Num (n, "") ->
        Fu.Atm (fun ff -> fprintf ff "%s" n)
    | Num _ -> unsupp "real numbers"
    | Choose _ -> unsupp "CHOOSE"
    | SetSt _ -> unsupp "SetSt"
    | SetOf _ -> unsupp "SetOf"
    | Except _ -> unsupp "Except"
    | Fcn _ -> unsupp "[x \\in S : e]"
    | At _ ->
        Errors.bug ~at:e "Backend.SMT.fmt_exp: encountered @"
    | Bang _ ->
        Errors.bug ~at:e "Backend.SMT.fmt_exp: !"
    | Parens (e, _) ->
        fmt_expr ecx e
    | With (e, _) ->
        fmt_expr ecx e
    | Let (ds, f) ->
        Errors.bug ~at:e "Backend.SMT.fmt_exp: encountered LET" ;
    | Tquant _ | Sub _ | Tsub _ | Fair _ ->
        unsupp "temporal logic"
    | _ ->
        Errors.set e "Expression not supported yet";
        Util.eprintf ~at:e "Expression not supported yet" ;
        failwith "Backend.SMT.fmt_expr"


and pp_print_boundvar cx ff (v, _, _) = pp_print_string ff v


and pp_print_boundset ecx ff b =
    match b.core with
    | (_, _, Domain e) ->
        to_fol_expr ecx ff e
    | _ ->
        Errors.bug ~at:b
            "Backend.SMT.pp_print_boundset: Fcn or SetOf without bounds"

and to_fol_expr ecx ff e =
    Fu.pp_print_minimal ff (fmt_expr ecx e)


(****************************************************************************)


let collect_data scx (hs, c) =
    let ops = ref SMap.empty in
    (** user operators: id |-> <<arity, arg_types, ret_type>> *)
    let std = ref SSet.empty in
    (** set of standard TLA+ operators *)
    let strs = ref SSet.empty in
    (** set of strings *)
    let nums = ref SSet.empty in
    (** set of numbers *)
    let visitor = object (self: 'self)
        inherit [unit] Expr.Visit.iter as super

        method expr scx e =
            (* Util.eprintf "collect: %a"
                (Expr.Fmt.pp_print_expr (snd scx, Ctx.dot)) e;
            *)
            let to_sort = function
                | Some T.Int -> "Int"
                | Some (T.Ref (_, T.Int, _)) -> "Int"
                | Some T.Str -> "str"
                | Some (T.Ref (_, T.Str, _)) -> "str"
                (** do not declare booleans:
                the boolean terms are already boolified.
                *)
                (*
                | Some T.Bool -> "Bool"
                | Some (T.Ref (_, T.Bool, _)) -> "Bool"
                *)
                | _ -> "u"
                in
            match e.core with
            | Apply ({core = Opaque id}, es)
                    when Smt.is_smt_kwd id ->
                std := SSet.add id !std;
                List.iter (self#expr scx) es
            | Apply ({core = Opaque id} as op, es) ->
                (** TODO: fix names of abstracted and
                bounded variables ("a__1"):
                add [isbounded] property to Opaque.
                *)
                let id' = if Smt.has_boundvar op then
                        id
                    else
                        Smt.smt_pickle false id in
                let ar = List.length es in
                let targs = List.map (fun _ -> "u") (Smt.n_to_list ar) in
                ops := SMap.add id' (ar, targs, "u") !ops;
                (* SMap.iter (fun id (_, xs, r) ->
                    Printf.eprintf "(user-op1 %s (%s) %s)\n"
                        id (String.concat " " xs) r) !ops;
                *)
                List.iter (self#expr scx) es
            | Apply ({core = Ix n}, es) ->
                let id' = Ectx.smt_id
                    (Ectx.from_hyps Ectx.dot (snd scx)) n in
                let ar = List.length es in  (** arity *)
                let targs = List.map
                    (fun _ -> "u")
                    (Smt.n_to_list ar) in
                ops := SMap.add id' (ar, targs, "u") !ops;
                List.iter (self#expr scx) es
            | Ix n
                    when not (Ectx.is_bounded (snd scx) n) ->
                let sort = to_sort (T.lookup_type (snd scx) n) in
                let id' = Ectx.smt_id
                    (Ectx.from_hyps Ectx.dot (snd scx)) n in
                ops := SMap.add id' (0, [], sort) !ops
            | Opaque id ->
                let sort = to_sort
                    (T.lookup_type_by_id (snd scx) id) in
                let id' = Smt.smt_pickle false id in
                (* Util.eprintf "collect opaques: %a : %s : %s"
                    (Expr.Fmt.pp_print_expr (snd scx, Ctx.dot))
                    e id' sort;
                *)
                ops := SMap.add id' (0, [], sort) !ops
                (** CHECK: [id] may be a bounded and abstracted id *)
            | Internal o ->
                begin
                try
                    std := SSet.add (Axioms.m_tla o) !std
                with Not_found -> ()
                end
            | String s ->
                std := SSet.add "str2u" !std;
                strs := SSet.add s !strs
            | Num (n, "") ->
                std := SSet.add "int2u" !std;
                nums := SSet.add n !nums
            | Tuple [] ->
                std := SSet.add "tla__tuple0" !std
            | SetEnum [] ->
                std := SSet.add "tla__emptyset" !std;
            (** Non-basic expressions *)
            | SetEnum es ->
                std := SSet.add
                    ("tla__set_"^(string_of_int (List.length es)))
                    !std;
                super#expr scx e
            | SetSt (v, dom, e) ->
                std := SSet.add "tla__SetSt" !std;
                super#expr scx e
            | SetOf (e, bs) ->
                std := SSet.add "tla__SetOf" !std;
                super#expr scx e
            | Arrow (a, b) ->
                std := SSet.add "tla__FcnSet" !std;
                super#expr scx e
            | Record fes ->
                let fs, _ = List.split fes in
                ignore (Smt.add_record_id fs);
                let r_id = sprintf
                    "tla__record__%d"
                    (Smt.get_recid fs) in
                std := SSet.add r_id !std;
                List.iter
                    (fun f -> strs := SSet.add f !strs)
                    fs;
                super#expr scx e
            | Rect fes ->
                let fs, _ = List.split fes in
                ignore (Smt.add_record_id fs);
                List.iter
                    (fun f -> strs := SSet.add f !strs)
                    fs;
                super#expr scx e
            | Dot (ex, h) ->
                std := SSet.add "str2u" !std;
                (* std := SSet.add Smt.fcnapp !std; *)
                std := SSet.add "tla__Dot" !std;
                strs := SSet.add h !strs;
                super#expr scx e
            | _ ->
                super#expr scx e

        method bounds scx bs =
            List.iter
                begin fun (v, k, dom) ->
                    match dom with
                    | Domain d ->
                        (* std := SSet.add "tla__in" !std; *)
                        self#expr scx d
                    | _ -> ()
                end bs ;
            let hs = List.map begin
                fun (v, k, _) -> Fresh (v, Shape_op 0, k, Unbounded) @@ v
                    (** Hack to recognize bounded variables by [Shape_op 0] *)
                end bs in
            Expr.Visit.adjs scx hs
    end in
    List.iter (visitor#expr scx) hs;
    ignore (visitor#expr scx c);
    let strs = List.map Smt.mk_string (SSet.elements !strs) in
    (!ops, SSet.elements !std, strs, SSet.elements !nums)


(* Rewriting system *)


(** Rewriter object *)
let rws = new Rewrite.rw


(** Rewrite and simplify hypotheses [hs] + conclusion [c] *)
let rw_hsc scx (hs, c) =
    Smt.sf#reset ;
    (** TODO: instead of resetting,
    [sf#add] only facts not already recorded.
    *)
    ignore (Smt.sf#push (snd scx) hs) ;
    let is_not_true e = not (
        Expr.Eq.expr e (Internal B.TRUE %% [])) in
    let hs = List.map begin fun h ->
        let h = rws#expr scx h in
        ignore (Smt.sf#push (snd scx) [h]) ;
        h
        end hs
        |> List.filter is_not_true
        |> List.map (fun e ->
            match e.core with
              List (And, es) -> es
            | _ -> [e])
        |> List.flatten
    in
    let c = rws#expr scx c in
    (* Smt.sf#pop nf; *)
    (* let hs, c = to_list (skolemize {context=hs ; active=c}) in *)
    (** TODO: make Skolemization work at this point *)
    List.iteri (fun i e ->
        Smt.ifprint 4 ">>>[%d] = %a" i
        (Expr.Fmt.pp_print_expr (snd scx, Ctx.dot)) e)
        (hs @ [c]);
    Smt.ifprint 4 "\n";
    hs, c


let rec fix2 d f (hs, c) =
    let eq (hs, c) (hs', c') =
        List.length hs = List.length hs'
        && List.for_all2 Expr.Eq.expr hs hs'
        && Expr.Eq.expr c c' in
    if d = 0 then
        failwith
            "backend/smt.ml: Cannot reach fixed point [fix2].\n"
    else begin
        let hs', c' = f (hs, c) in
        if eq (hs, c) (hs', c') then
            (hs, c)
        else
            fix2 (d - 1) f (hs', c')
    end


let abstract_func = ref Preprocess.abstract


let (@@@) f g = fun x -> g (f x)


let to_basic scx (hs, c) =
    Smt.skolem1_ids := SMap.empty;
    (hs, c)
    |> fix2 99 ((Preprocess.simpl_eq scx) @@@ (fix2 9 (rw_hsc scx)))
    |> fix2 99 ((!abstract_func scx) @@@ (fix2 9 (rw_hsc scx)))


(* Post-pre-process (after type synthesis)

- Rewriting rules to apply:
    [a \div b] -->
        [IF a \in Int /\ b \in Int /\ 0 < b
            THEN a \div b
            ELSE tla__div(a, b)]
    [a \mod b] -->
        [IF a \in Int /\ b \in Int /\ 0 < b
            THEN a \mod b
            ELSE tla__mod(a, b)]
    [a ^ b] -->
        [IF a \in Int /\ b \in Int /\ a # 0
            THEN exp(a, b)
            ELSE tla__exp(a, b)]
    (* [a + b] -->
        [IF a \in Int /\ b \in Int
            THEN a + b
            ELSE tla__plus(a, b)] *)
    (* [Cardinality(S)] -->
        [IF IsFiniteSet(S)
            THEN Cardinality(S)
            ELSE tla__Cardinality(S)] *)
*)
let postpreproc sq =
    let app op es = Apply (Internal op %% [], es) %% [] in
    let lAnd = function [e] -> e | es -> List (And, es) %% [] in
    let in_int e = app B.Mem [e; Internal B.Int %% []] in
    let opq p es = Apply (Opaque p %% [], es) %% [] in
    let zero = Num ("0", "") %% [] in
    let visitor = object (self: 'self)
        inherit [unit] Expr.Visit.map as super

        method expr scx e =
            match e.core with
            | Apply ({core = Internal (B.Exp as op)}, [a; b]) ->
                If (lAnd [in_int a; in_int b; app B.Neq [a; zero]],
                    e, opq (Axioms.m_tla op) [a; b]) @@ e
            | Apply ({core = Internal (B.Quotient | B.Remainder as op)},
                    [a; b]) ->
                If (lAnd [in_int a; in_int b; app B.Lt [zero; b]],
                    e, opq (Axioms.m_tla op) [a; b]) @@ e
            (*
            | Apply ({core = Internal (
                    B.Lt | B.Lteq | B.Gt | B.Gteq as op)}, [a; b]) ->
                If (lAnd [in_int a; in_int b],
                    e, opq (Axioms.m_tla op) [a; b]) @@ e
            *)
            (*
            | Apply ({core = Internal (
                    B.Plus | B.Minus | B.Times as op)}, [a; b]) ->
                If (lAnd [in_int a; in_int b],
                    e, opq (Axioms.m_tla op) [a; b]) @@ e
            *)
            (*
            | Apply ({core = Ix n}, [s]) ->
                    (*
                    when
                        (Ectx.smt_id (Ectx.from_hyps Ectx.dot (snd scx)) n) =
                        "Cardinality" ->
                    *)
                let id = Ectx.smt_id
                    (Ectx.from_hyps Ectx.dot (snd scx)) n in
                if id = "Cardinality" then
                    If (Boolify.mk_bool (opq "IsFiniteSet" [s]),
                        e, opq "tla__Cardinality" [s]) @@ e
                else
                    super#expr scx e
            *)
            | _ ->
                super#expr scx e

        method hyp scx h =
            match h.core with
            | Defn (_, _, Hidden, _)
            (** ignore these cases *)
            | Fact (_, Hidden, _) ->
                (Expr.Visit.adj scx h, h)
            | _ -> super#hyp scx h
    end in
    let cx = sq.context in
    (**
    1. get type annotations from [sq.context]
       whose types are different from [u]
    2. for each pair (x, t) add a new hyp [to_typred x t]
    *)
    snd (visitor#sequent ((), cx) sq)


(** Add SMTLIB pattern annotations to definitions of abstracted operators *)
let add_patterns scx hs =
    let is_abstract e =
        match e.core with
        | Opaque s
                when Smt.is_nonbasic_var s ->
            true
        | Apply ({core = Opaque s}, _)
                when Smt.is_nonbasic_var s ->
            true
        | _ -> false
    in
    List.map begin fun e ->
        match e.core with
        | Quant (_, bs, {core = Apply ({core = Internal B.Equiv},
            [{core = Apply ({core = Internal B.Mem}, [_; ex])} as pat; _])})
                when is_abstract ex ->
            Property.assign e Smt.pattern_prop pat
        | _ -> e
    end hs


let process_obligation sq =
    (* Util.eprintf "[0]: %a" Fu.pp_print_minimal
        (Fu.Big (fun ff ->
            ignore (E.pp_print_sequent (sq.context, Ctx.dot) ff sq)));
    *)
    let ops = Smt.free_operators sq in
    (** List of unexpanded operator identifiers *)
    let tx = Sys.time () in
    let scx, hs, c = sq
    |> Preprocess.prepreproc  (** Pre-preprocessing *)
    (* |> fun sq -> Util.eprintf
        "[1]: %a" Fu.pp_print_minimal
        (Fu.Big (fun ff ->
            ignore (E.pp_print_sequent (sq.context, Ctx.dot) ff sq))); sq
    *)
    |> Preprocess.skolemize  (** Uncurry
        [conc] + Skolemize hyps and
        conc + deconj hyps *)
    (* |> fun sq -> Util.eprintf
        "[2]: %a" Fu.pp_print_minimal
        (Fu.Big (fun ff ->
            ignore (E.pp_print_sequent (sq.context, Ctx.dot) ff sq))); sq
    *)
    |> Boolify.boolify  (** Boolify *)
    (* |> fun sq -> Util.eprintf
        "[3]: %a" Fu.pp_print_minimal
        (Fu.Big (fun ff ->
            ignore (E.pp_print_sequent (sq.context, Ctx.dot) ff sq))); sq
    *)
    |> Typ_system.type_construct
        (** Type synthesis + type decoration *)
    (* |> fun sq -> Util.eprintf
        "[4]: %a" Fu.pp_print_minimal
        (Fu.Big (fun ff ->
            ignore (E.pp_print_sequent (sq.context, Ctx.dot) ff sq))); sq
    *)
    |> postpreproc  (** Post-preprocessing *)
    (* |> fun sq -> Util.eprintf
        "[5]: %a" Fu.pp_print_minimal
        (Fu.Big (fun ff ->
            ignore (E.pp_print_sequent (sq.context, Ctx.dot) ff sq))); sq
    *)
    |> Smt.to_list
    in
    (* List.iteri (fun i e ->
        Util.eprintf "#[%d] = %a"
        i (E.pp_print_expr (snd scx, Ctx.dot)) e)
        (hs @ [c]) ;
    Util.eprintf "\n" ;
    *)
    let hs, c = (hs, c)
    |> fix2 9 (to_basic scx)  (** Normalization +
        Optimizations *)
    |> Fmt.lift_sq (snd scx) (** Insert sort-lifting
        functions [int2u] and [str2u] *)
    |>> add_patterns (snd scx)  (** Add SMTLIB pattern
        annotations to definitions of abstracted operators *)
    in
    (* List.iteri (fun i e ->
        Util.eprintf "=[%d] = %a"
        i (E.pp_print_expr (snd scx, Ctx.dot)) e)
        (hs @ [c]) ;
    Util.eprintf "\n" ;
    *)
    Smt.ifprint 1 "** Preprocessing took %5.3fs%! (including type synthesis)"
        (Sys.time () -. tx);
    List.iteri (fun i e -> Smt.ifprint 1 "*[%d] = %a" i
        (** Actual translation *)
        (E.pp_print_expr (snd scx, Ctx.dot)) e) (hs @ [c]);
    Smt.ifprint 1 "\n";
    Smt.ifprint 0 "** @[<b2>Unexpanded symbols: %s@]\n"
       (if ops = [] then "---" else (String.concat ", " ops));
    scx, hs, c


let reset () =
    Smt.record_ids := Smt.SSMap.empty;
    Smt.skolem1_ids := SMap.empty;
    Smt.skolem2_ids := SMap.empty;
    Smt.record_signatures := [];
    Smt.ctr := 0;
    E.ctr_types := 0;
    T.ctr_funarg := 0;
    Smt.typesystem_mode := begin
        if Params.debugging "notypes" then 0  (** Untyped *)
        else if Params.debugging "types0" then 0  (** Untyped *)
        else if Params.debugging "types1" then 1  (** Elementary type system *)
        else if Params.debugging "types2" then 2  (** Refinement type system *)
        else 1
    end;
    Smt.ifprint 1 "** Type system mode = %d" !Smt.typesystem_mode;
    Smt.verbosity := begin
        if Params.debugging "verbose0" then 0
        else if Params.debugging "verbose1" then 1
        else if Params.debugging "verbose2" then 2
        else if Params.debugging "verbose3" then 3
        else if Params.debugging "verbose4" then 4
        else 0
    end;
    abstract_func := begin
        if Params.debugging "abstract1" then Preprocess.abstract
        else if Params.debugging "abstract2" then Preprocess.abstract2
        else Preprocess.abstract
    end;
    ()


let encode_smtlib ?solver:(mode="SMTLIB") ff ob =
    Smt.mode := if mode = "Z3" then Smt.Z3 else Smt.Smtlib ;
    let m: Axioms.t_map = set_map () in
    reset ();
    let scx, hs, c = process_obligation (ob.obl.core) in
    let ops, std, strs, nums = collect_data scx (hs, c) in
    let sorts = ["u"] @ (if strs <> [] then ["str"] else []) in
    (* SMap.iter
        (fun id (_, xs, r) ->
            Printf.eprintf "___user-op %s : (%s) %s\n"
                id (String.concat " " xs) r) ops;
    *)
    (* Printf.eprintf "___std: %s\n" (String.concat "," std) ; *)
    let std', axioms = Axioms.build_tla_ops m std in
    fprintf ff ";; TLA+ Proof Manager %s\n" (Params.rawversion ());
    fprintf ff ";; Proof obligation #%d\n" (Option.get ob.id);
    fprintf ff ";;   generated from %s\n" (Util.location ~cap:false ob.obl);
    fprintf ff "\n";
    fprintf ff "%s" ("(set-logic " ^ !Params.smt_logic ^ ")\n");
    (* This was formerly AUFNIRA. *)
    List.iter (fprintf ff "(declare-sort %s 0)\n") sorts;
    fprintf ff ";; Standard TLA+ operators\n";
    List.iter (fun (id, xs, r) ->
        fprintf ff "(declare-fun %s (%s) %s)\n"
        id (String.concat " " (map m.print_sort xs)) (m.print_sort r))
        std';
    fprintf ff "\n;; Terms, predicates and strings\n";
    (* iter (fun (f, xs, r) ->
        fprintf ff "(declare-fun %s (%s) %s)"
        f (String.concat " " (map m.print_sort xs)) (m.print_sort r)) ops;
    *)
    SMap.iter (fun id (_, xs, r) ->
        fprintf ff "(declare-fun %s (%s) %s)\n"
        id (String.concat " " xs) r)
        ops;
    List.iter (fun s -> fprintf ff "(declare-fun %s () str)\n" s) strs;
    List.iter (fprintf ff "@[<hov2>(assert@ %s)@]") axioms;
    (if List.length strs > 1 then
        fprintf ff "\n(assert (distinct %s))\n" (String.concat " " strs));
    let ecx = Ectx.from_hyps Ectx.dot (snd scx) in
    fprintf ff "\n";
    fprintf ff
        "@?@[<hov2>(assert@ (not@ %a))@]\n"
        (to_fol_expr ecx) c;
        (** The conjecture goes before the hypotheses *)
    List.iter
        (fprintf ff "@?@[<hov2>(assert@ %a)@]\n"
            (to_fol_expr ecx))
        hs;
        (** Hypotheses *)
    fprintf ff "\n";
    fprintf ff "(check-sat)\n";
    fprintf ff "(exit)\n"


let encode_fof ff ob =
    Smt.mode := Smt.Fof;
    let m = set_map () in
    reset ();
    let scx, hs, c = process_obligation (ob.obl.core) in
    let ops, std, strs, nums = collect_data scx (hs, c) in
    let nums = map (fun n ->
        if n.[0] = '-' then
            Util.sprintf ~nonl:() "%a"
                (fun ff -> m.uminus ff pp_print_string)
                (String.sub n 1 ((String.length n) - 1))
        else n)
        nums in
    let std', axioms = Axioms.build_tla_ops m std in
    fprintf ff "%% Author : TLA+ Proof Manager %s\n" (Params.rawversion ());
    fprintf ff "%% Proof obligation #%d\n" (Option.get ob.id);
    fprintf ff "%%   generated from %s\n" (Util.location ~cap:false ob.obl);
    fprintf ff "\n";
    let to_sort = (Axioms.smtlib_map).print_sort in
    (** Just for debugging information,
    print sorts as in SMT-LIB in comments.
    *)
    List.iter (fun (id, xs, r) -> fprintf ff "%%  %s : (%s) -> %s\n"
        id (String.concat "," (map to_sort xs)) (to_sort r)) std';
    SMap.iter (fun id (_, xs, r) -> fprintf ff "%%  %s : (%s) -> %s\n"
        id (String.concat "," xs) r) ops;
    List.iter (fun s -> fprintf ff "%%  %s : () -> str\n" s) strs;
    fprintf ff "\n";
    let distincts = List.map
        (fun (x, y) -> sprintf "%s != %s" x y)
        (Smt.perms strs) in
    List.iteri (fprintf ff "@[<hov2>fof(n%d,axiom,isint(%s)).@]@.") nums;
    List.iteri
        (fprintf ff "@[<hov2>fof(a%d,axiom,@,@[<hov2>%s@]).@]@.")
        axioms;
    List.iteri
        (fprintf ff "@[<hov2>fof(s%d,axiom,@,@[<hov2>%s@]).@]@.")
        distincts;
    let ecx = Ectx.from_hyps Ectx.dot (snd scx) in
    List.iteri
        (fun i e ->
            fprintf ff "@?@[<hov2>fof(h%d,axiom,@,@[<hov2>%a@]).@]@."
            i (to_fol_expr ecx) e)
        hs;
    fprintf ff "@?@[<hov2>fof(conc,conjecture,@,@[<hov2>%a@]).@]@."
        (to_fol_expr ecx) c


(* Everything below is part of a deprecated version
of the SMT encoding; ignore it
*)
(*
open Smtlib.T
open Smtlib.Fmt

module Sm = Util.Coll.Sm


type smt_logic =
    | AUFNIRA
    | UFNIA


let to_string = function
    | AUFNIRA -> "AUFNIRA"
    | UFNIA   -> "UFNIA"


let pp_print_obligation ?solver:(solver="?") ?logic:(logic=AUFNIRA) ff ob =
    let sq = ob.obl.core in
    let sq = Typ_system.type_construct sq in
    let th = Smtlib.Direct.encode_direct sq in
    Format.fprintf ff "(set-logic %s)@." (to_string logic);
    Format.pp_print_newline ff ();
    (* Iter on [th.sorts] and [th.ops] to print declarations
    * in the same order they were made.
    *)
    if Deque.size th.sorts > 0 then begin
        Format.fprintf ff ";; Sort Declarations@.";
        Deque.iter begin fun _ smb ->
            let dcl = find th smb in
            if not dcl.iscore then
                Format.fprintf ff "(@[declare-sort %s %d)@]@."
                    dcl.smb
                    (fst dcl.rank |> List.length)
            end th.sorts;
        Format.pp_print_newline ff ()
    end;
    if Deque.size th.ops > 0 then begin
        Format.fprintf ff ";; Operator Declarations@.";
        Deque.iter begin fun _ smb ->
            let dcl = find th smb in
            if not dcl.iscore then begin
                begin if List.length dcl.pars > 0 then
          failwith "Backend.Smt.pp_print_obligation: Can't declare parametric functions"
                end;
                Format.fprintf ff
                    "(@[declare-fun %s (@[%a)@]@ %a)@]@."
                    dcl.smb
                    (Format.pp_print_list
                        ~pp_sep:Format.pp_print_space pp_print_sort)
                    (fst dcl.rank)
                    pp_print_sort (snd dcl.rank)
            end
            end th.ops;
        Format.pp_print_newline ff ()
    end;
    (* The order for assertions doesn't matter. *)
    begin if not (Sm.is_empty th.assrts) then
        Format.fprintf ff ";; Assertions@.";
        let k, assrt = Sm.choose th.assrts in
        begin if String.length assrt.name > 0 then
            Format.fprintf ff ";;   %s@." assrt.name
        end;
        Format.fprintf ff "(@[assert %a)@]@."
            pp_print_term assrt.form;
        Sm.remove k th.assrts
        |> Sm.iter begin fun _ assrt ->
            Format.pp_print_newline ff ();
            begin if assrt.name != "" then
                Format.fprintf ff ";;   %s@." assrt.name
            end;
            Format.fprintf ff "(@[assert %a)@]@."
                pp_print_term assrt.form
        end
    end;
    Format.pp_print_newline ff ();
    Format.fprintf ff "(check-sat)@.";
    Format.fprintf ff "(exit)"


(* REDIRECT *)
(* let encode_smtlib = pp_print_obligation ~logic:UFNIA *)
*)
