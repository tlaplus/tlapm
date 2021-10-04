(*
 * encode/rewrite.ml --- rewrite sequents
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

open Expr.T
open Type.T

open Ext
open Property
open Expr.T
open Type.T

module Subst = Expr.Subst
module Visit = Expr.Visit
module B = Builtin

(* TODO Type preservation for elim_except, elim_multiarg, elim_tuples *)
(* Need to think about a different use of type annotations for tuples
 * before that. *)


(* {3 Helpers} *)

let error ?at mssg =
  let mssg = "Encode.Rewrite: " ^ mssg in
  (*Errors.bug ?at mssg*)
  failwith mssg

let maybe_assign prop a = function
  | Some p -> assign a prop p
  | None -> a

(* Return a with the value of prop attached to from, if present *)
let copy_prop prop a from =
  maybe_assign prop a (query from prop)


(* {3 Bounds Elimination} *)

let elim_bounds_visitor = object (self : 'self)
  inherit [unit] Visit.map as super

  method expr scx oe =
    match oe.core with

    | Quant (q, bs, e) ->
        let n = List.length bs in
        let scx, bs, hs, _, _ =
          List.fold_left begin fun (nscx, r_bs, r_hs, dit, i) (v, k, d) ->
            let h = Fresh (v, Shape_expr, k, Unbounded) %% [] in
            let nscx = Visit.adj scx h in
            let b = (v, k, No_domain) in
            match d, dit with
            | No_domain, _ ->
                (nscx, b :: r_bs, r_hs, None, i - 1)
            | Domain d, _ ->
                let d = self#expr scx d in
                let d = Subst.app_expr (Subst.shift n) d in
                let op =
                  Option.map (fun ty -> [ ty ]) (query d Props.mpars_prop) |>
                  maybe_assign Props.tpars_prop (Internal B.Mem %% [])
                in
                let ix = copy_prop Props.icast_prop (Ix i %% []) v in
                let h = Apply (op, [ ix ; d ]) %% [] in
                (nscx, b :: r_bs, h :: r_hs, Some d, i - 1)
            | Ditto, Some d ->
                let op =
                  Option.map (fun ty -> [ ty ]) (query d Props.mpars_prop) |>
                  maybe_assign Props.tpars_prop (Internal B.Mem %% [])
                in
                let ix = copy_prop Props.icast_prop (Ix i %% []) v in
                let h = Apply (op, [ ix ; d ]) %% [] in
                (nscx, b :: r_bs, h :: r_hs, Some d, i - 1)
            | _, _ ->
                error ~at:oe "Missing bound"
          end (scx, [], [], None, n) bs |>
          fun (nscx, r_bs, r_hs, dit, i) ->
            (nscx, List.rev r_bs, List.rev r_hs, dit, i)
        in
        let e = self#expr scx e in
        let e, opats =
          (* Patterns must be displaced as the body of a quantified expr
           * is modified. *)
          match query e pattern_prop with
          | None -> e, None
          | Some pats -> remove_pats e, Some pats
        in
        let e =
          match hs, q with
          | [], _ -> e
          | [h], Forall ->
              Apply (Internal B.Implies %% [], [
                h ; e
              ]) %% []
          | _, Forall ->
              Apply (Internal B.Implies %% [], [
                List (And, hs) %% [] ; e
              ]) %% []
          | _, Exists ->
              List (And, hs @ [ e ]) %% []
        in
        let e = Option.fold add_pats e opats in
        Quant (q, bs, e) @@ oe

    | Choose (v, Some d, e) ->
        let d = self#expr scx d in
        let h = Fresh (v, Shape_expr, Constant, Unbounded) %% [] in
        let scx = Visit.adj scx h in
        let e = self#expr scx e in
        let op =
          Option.map (fun ty -> [ ty ]) (query d Props.mpars_prop) |>
          maybe_assign Props.tpars_prop (Internal B.Mem %% [])
        in
        let ix = copy_prop Props.icast_prop (Ix 1 %% []) v in
        let h = Apply (op, [ ix ; Subst.app_expr (Subst.shift 1) d ]) %% [] in
        let e = Apply (Internal B.Conj %% [], [ h ; e ]) %% [] in
        Choose (v, None, e) @@ oe

    | _ -> super#expr scx oe

  (* NOTE method hyps is ignored, because a substitution must be built across the context
   * and applied to each hyp and the succedent.  This substitution renames variables to
   * account for new hypotheses in the context. *)
  method sequent scx sq =
    let rec spin scx sub hs =
      match Deque.front hs with
      | None -> (scx, sub, Deque.empty)

      | Some ({ core = Fresh (v, shp, k, Bounded (d, vis)) } as h, hs) ->
          let d = Subst.app_expr sub d in
          let d = self#expr scx d in
          let h = Fresh (v, shp, k, Unbounded) @@ h in
          let op =
            Option.map (fun ty -> [ ty ]) (query d Props.mpars_prop) |>
            maybe_assign Props.tpars_prop (Internal B.Mem %% [])
          in
          let ix = copy_prop Props.icast_prop (Ix 1 %% []) v in
          let e = Apply (op, [ ix ; Subst.app_expr (Subst.shift 1) d ]) %% [] in
          let hh = Fact (e, vis, NotSet) %% [] in
          let scx = Visit.adj scx h in
          let sub = Subst.bump sub in
          let scx = Visit.adj scx hh in
          let sub = Subst.compose (Subst.shift 1) sub in
          let scx, sub, hs = spin scx sub hs in
          (scx, sub, Deque.cons h (Deque.cons hh hs))

      | Some (h, hs) ->
          let h = Subst.app_hyp sub h in
          let scx, h = self#hyp scx h in
          let sub = Subst.bump sub in
          let scx, sub, hs = spin scx sub hs in
          (scx, sub, Deque.cons h hs)
    in
    let scx, sub, hs = spin scx (Subst.shift 0) sq.context in
    let e = Subst.app_expr sub sq.active in
    let e = self#expr scx e in
    (scx, { context = hs ; active = e })
end

let elim_bounds sq =
  let cx = ((), Deque.empty) in
  snd (elim_bounds_visitor#sequent cx sq)


(* {3 Flex Elimination} *)

let is_prime s =
  let rgx = Str.regexp "#prime$" in
  try
    let _ = Str.search_forward rgx s 0 in
    true
  with Not_found ->
    false

let remove_prime s =
  let rgx = Str.regexp "#prime$" in
  Str.replace_first rgx "" s

let mk_prime s =
  s ^ "_prime"

let elim_flex_visitor = object (self : 'self)
  inherit [unit] Expr.Visit.map as super

  method expr scx oe =
    match oe.core with
    | Opaque s when is_prime s ->
        let s = mk_prime (remove_prime s) in
        let n, _ = Option.get (Deque.find ~backwards:true (snd scx) (fun h -> hyp_name h = s)) in
        Ix (n + 1) %% []
    | _ -> super#expr scx oe

  (* See the sequent method for elim_bounds_visitor *)
  method sequent scx sq =
    let rec spin scx sub hs =
      match Deque.front hs with
      | None -> (scx, sub, Deque.empty)

      | Some ({ core = Flex v } as h, hs) ->
          let h1 = Fresh (v, Shape_expr, Constant, Unbounded) @@ h in
          let v' = mk_prime v.core %% [] in
          let h2 = Fresh (v', Shape_expr, Constant, Unbounded) %% [] in
          let scx = Visit.adj scx h1 in
          let sub = Subst.bump sub in
          let scx = Visit.adj scx h2 in
          let sub = Subst.compose (Subst.shift 1) sub in
          let scx, sub, hs = spin scx sub hs in
          (scx, sub, Deque.cons h1 (Deque.cons h2 hs))

      | Some (h, hs) ->
          let h = Subst.app_hyp sub h in
          let scx, h = self#hyp scx h in
          let sub = Subst.bump sub in
          let scx, sub, hs = spin scx sub hs in
          (scx, sub, Deque.cons h hs)
    in
    let scx, sub, hs = spin scx (Subst.shift 0) sq.context in
    let e = Subst.app_expr sub sq.active in
    let e = self#expr scx e in
    (scx, { context = hs ; active = e })
end

let elim_flex sq =
  let cx = ((), Deque.empty) in
  snd (elim_flex_visitor#sequent cx sq)


(* {3 NotMem Simplification} *)

let elim_notmem_visitor = object (self : 'self)
  inherit [unit] Visit.map as super

  method expr scx oe =
    match oe.core with
    | Apply ({ core = Internal B.Notmem } as op, [ e ; f ]) ->
        let e = self#expr scx e in
        let f = self#expr scx f in
        Apply (Internal B.Neg %% [], [
          Apply (Internal B.Mem @@ op, [ e ; f ]) %% []
        ]) @@ oe
    | _ -> super#expr scx oe
end

let elim_notmem sq =
  let cx = ((), Deque.empty) in
  snd (elim_notmem_visitor #sequent cx sq)


(* {3 Comparisons Simplification} *)

let elim_compare_visitor = object (self : 'self)
  inherit [unit] Visit.map as super

  method expr scx oe =
    match oe.core with
    | Apply ({ core = Internal B.Lt } as op, [ e ; f ])
      when not (has op Props.tpars_prop) ->
        let e = self#expr scx e in
        let f = self#expr scx f in
        let neq_op = assign (Internal B.Neq %% []) Props.tpars_prop [ TAtm TAIdv ] in
        if has oe Props.icast_prop then
          Apply (Internal B.Conj %% [], [
            remove (Apply (Internal B.Lteq @@ op, [ e ; f ]) @@ oe) Props.icast_prop ;
            Apply (neq_op, [ e ; f ]) %% []
          ]) %% [] |> fun oe ->
            assign oe Props.icast_prop (TAtm TABol)
        else
          Apply (Internal B.Conj %% [], [
            Apply (Internal B.Lteq @@ op, [ e ; f ]) @@ oe ;
            Apply (neq_op, [ e ; f ]) %% []
          ]) %% []

    | Apply ({ core = Internal B.Gt } as op, [ e ; f ])
      when not (has op Props.tpars_prop) ->
        let e = self#expr scx e in
        let f = self#expr scx f in
        let neq_op = assign (Internal B.Neq %% []) Props.tpars_prop [ TAtm TAIdv ] in
        if has oe Props.icast_prop then
          Apply (Internal B.Conj %% [], [
            remove (Apply (Internal B.Lteq @@ op, [ f ; e ]) @@ oe) Props.icast_prop ;
            Apply (neq_op, [ f ; e ]) %% []
          ]) %% [] |> fun oe ->
            assign oe Props.icast_prop (TAtm TABol)
        else
          Apply (Internal B.Conj %% [], [
            Apply (Internal B.Lteq @@ op, [ f ; e ]) @@ oe ;
            Apply (neq_op, [ f ; e ]) %% []
          ]) %% []

    | Apply ({ core = Internal B.Gteq } as op, [ e ; f ])
      when not (has op Props.tpars_prop) ->
        let e = self#expr scx e in
        let f = self#expr scx f in
        Apply (Internal B.Lteq @@ op, [ f ; e ]) @@ oe

    | _ -> super#expr scx oe
end

let elim_compare sq =
  let cx = ((), Deque.empty) in
  snd (elim_compare_visitor #sequent cx sq)


(* {3 EXCEPT Elimination} *)

let elim_except_visitor = object (self : 'self)
  inherit [unit] Visit.map as super

  method expr scx oe =
    match oe.core with
    | Except (e, [ ([d], a as exp) ]) when not (has oe Props.tpars_prop) ->
        let e = self#expr scx e in
        let exp = self#exspec scx exp in
        let d, a =
          match exp with
          | [Except_dot s], a -> String s %% [], a
          | [Except_apply d], a -> d, a
          | _ -> failwith ""
        in
        let b = Apply (Internal B.DOMAIN %% [], [ e ]) %% [] in
        let v = assign ("x" %% []) Props.ty0_prop (TAtm TAIdv) in
        Fcn (
          [ v, Constant, Domain b ],
          If (
            Apply (Internal B.Eq %% [], [ Ix 1 %% [] ; Subst.app_expr (Subst.shift 1) d ]) %% [],
            Subst.app_expr (Subst.shift 1) a,
            FcnApp (Subst.app_expr (Subst.shift 1) e, [ Ix 1 %% [] ]) %% []
          ) %% []
        ) %% []

    (* FIXME Cases below  are preprocessed away in {!Expr.Elab} *)

    | Except (e, [ d :: ds, a ]) ->
        Except (e, [ [d], begin
          let app =
            match d with
            | Except_dot s -> Dot (e, s) %% []
            | Except_apply d -> FcnApp (e, [d]) %% []
          in
          Except (app, [ ds, a ]) %% []
        end ]) %% [] |>
        self#expr scx

    | Except (e, exs) (* when List.length exs > 1 *) ->
        List.fold_left begin fun e exp ->
          Except (e, [ exp ]) %% []
        end e exs |>
        self#expr scx

    | _ -> super#expr scx oe
end

let elim_except sq =
  let cx = ((), Deque.empty) in
  snd (elim_except_visitor #sequent cx sq)


(* {3 Multi-arguments Functions Elimination} *)

let elim_multiarg_visitor = object (self : 'self)
  inherit [unit] Visit.map as super

  method expr scx oe =
    match oe.core with
    | Fcn (bs, e) when List.length bs > 1 && not (has oe Props.tpars_prop) ->
        let scx, bs = self#bounds scx bs in
        let vs, bs, _ =
          List.fold_left begin fun (r_vs, r_bs, dit) (v, _, d) ->
            match d, dit with
            | Domain b, _
            | Ditto, Some b ->
                (v :: r_vs, b :: r_bs, Some b)
            | _, _ -> error ~at:oe "Missing bound on Fcn"
          end ([], [], None) bs |>
          fun (r_vs, r_bs, dit) ->
            (List.rev r_vs, List.rev r_bs, dit)
        in
        let v = assign ("t" %% []) Props.ty0_prop (TAtm TAIdv) in
        let b = Product bs %% [] in
        let e = self#expr scx e in
        let dfs =
          List.mapi begin fun i v ->
            Operator (v, FcnApp (
              Ix 1 %% [], [ Num (string_of_int (i + 1), "") %% [] ]
            ) %% []) %% []
          end vs
        in
        let e = Let (dfs, e) %% [] in
        Fcn ([ v, Constant, Domain b ], e) @@ oe

    | FcnApp (e1, es) when List.length es > 1 && not (has oe Props.tpars_prop) ->
        let e1 = self#expr scx e1 in
        let es = List.map (self#expr scx) es in
        let e2 = Tuple es %% [] in
        FcnApp (e1, [ e2 ]) @@ oe

    | _ -> super#expr scx oe
end

let elim_multiarg sq =
  let cx = ((), Deque.empty) in
  snd (elim_multiarg_visitor #sequent cx sq)


(* {3 Tuples Elimination} *)

let elim_tuples_visitor = object (self : 'self)
  inherit [unit] Visit.map as super

  method expr scx oe =
    match oe.core with
    | Product es when not (has oe Props.tpars_prop) ->
      let es = List.map (self#expr scx) es in
      let n = List.length es in
      let rg =
        Apply (
          Internal B.Range %% [],
          [ Num ("1", "") %% [] ; Num (string_of_int n, "") %% [] ]
        ) %% []
      in
      let e1 =
        Arrow (
          rg,
          Apply (
            Internal B.UNION %% [],
            [ SetEnum es %% [] ]
          ) %% []
        ) %% []
      in
      let e2 =
        List (
          And,
          List.mapi begin fun i e ->
            Apply (
              Internal B.Mem %% [],
              [
                FcnApp (Ix 1 %% [], [ Num (string_of_int (i + 1), "") %% [] ]) %% [] ;
                Subst.app_expr (Subst.shift 1) e
              ]
            ) %% []
          end es
        ) %% []
      in
      let v = assign ("f" %% []) Props.ty0_prop (TAtm TAIdv) in
      SetSt (v, e1, e2) @@ oe

    | Tuple es when not (has oe Props.tpars_prop) ->
        let es = List.map (self#expr scx) es in
        let n = List.length es in
        let b =
          Apply (
            Internal B.Range %% [],
            [ Num ("1", "") %% [] ; Num (string_of_int n, "") %% [] ]
          ) %% []
        in
        let e =
          Case (
            List.mapi begin fun i e ->
              let p =
                Apply (
                  Internal B.Eq %% [],
                  [ Ix 1 %% [] ; Num (string_of_int (i + 1), "") %% [] ]
                ) %% []
              in
              (p, Subst.app_expr (Subst.shift 1) e)
            end es,
            None
          ) %% []
        in
        let v = assign ("i" %% []) Props.ty0_prop (TAtm TAIdv) in
        Fcn ([ v, Constant, Domain b ], e) @@ oe

    | _ -> super#expr scx oe
end

let elim_tuples sq =
  let cx = ((), Deque.empty) in
  snd (elim_tuples_visitor#sequent cx sq)


(* {3 Records Elimination} *)

let elim_records_visitor = object (self : 'self)
  inherit [unit] Visit.map as super

  method expr scx oe =
    match oe.core with
    | Rect fs when not (has oe Props.tpars_prop) ->
        let rg = SetEnum (List.map (fun (s, _) -> String s %% []) fs) %% [] in
        let im = SetEnum (List.map snd fs) %% [] in
        let e1 = Arrow (rg, Apply (Internal B.UNION %% [], [ im ]) %% []) %% [] in
        let e2 =
          List (
            And,
            List.map begin fun (s, e) ->
              Apply (
                Internal B.Mem %% [],
                [ FcnApp (Ix 1 %% [], [ String s %% [] ]) %% []
                ; Subst.app_expr (Subst.shift 1) e ]
              ) %% []
            end fs
          ) %% []
        in
        let v = assign ("f" %% []) Props.ty0_prop (TAtm TAIdv) in
        SetSt (v, e1, e2) @@ oe

    | Record fs when not (has oe Props.tpars_prop) ->
        let rg = SetEnum (List.map (fun (s, _) -> String s %% []) fs) %% [] in
        let ps =
          List.map begin fun (s, e) ->
            let p =
              Apply (
                Internal B.Eq %% [],
                [ Ix 1 %% [] ; String s %% [] ]) %% []
            in
            (p, Subst.app_expr (Subst.shift 1) e)
          end fs
        in
        let e = Case (ps, None) %% [] in
        let v = assign ("s" %% []) Props.ty0_prop (TAtm TAIdv) in
        Fcn ([ v, Constant, Domain rg ], e) @@ oe

    | Dot (e, s) when not (has oe Props.tpars_prop) ->
        FcnApp (e, [ String s %% [] ]) @@ oe

    | _ -> super#expr scx oe

  method exspec scx (trail, res) =
    let do_trail = function
      | Except_dot s -> Except_apply (String s %% [])
      | Except_apply e -> Except_apply (self#expr scx e)
    in
    (List.map do_trail trail, self#expr scx res)

end

let elim_records sq =
  let cx = ((), Deque.empty) in
  snd (elim_records_visitor#sequent cx sq)


(* {3 Apply Extensionnality} *)

let is_set e =
  match e.core with
  | SetEnum _
  | SetSt _
  | SetOf _
  | Apply ({ core = Internal (B.Cap | B.Cup | B.Setminus) }, [ _ ; _ ])
  | Product _
  | Arrow _
  | Rect _
  | Internal (B.STRING | B.BOOLEAN | B.Nat | B.Int) ->
          true
  | _ ->
          false

let eq_pol b = function
  | B.Eq -> b
  | B.Neq -> not b
  | _ -> failwith "eq_pol"

let apply_ext_visitor = object (self : 'self)
  inherit [bool] Expr.Visit.map as super

  method expr (b, cx as scx) oe =
    match oe.core with
    | Apply ({ core = Internal (B.Eq | B.Neq as blt) } as op, [ e ; f ])
      when eq_pol b blt
      && (is_set e || is_set f)
      && (match query op Props.tpars_prop with
          Some [TAtm TAIdv] -> true | _ -> false) ->
        (* TODO Typelvl=1 *)
        let e = self#expr scx e in
        let f = self#expr scx f in
        let q =
          match blt with
          | B.Eq -> Forall
          | B.Neq -> Exists
          | _ -> failwith ""
        in
        let v = assign ("x" %% []) Props.ty0_prop (TAtm TAIdv) in
        let mem_op = Internal B.Mem %% [] in
        Quant (
          q, [ v, Constant, No_domain ],
          Apply (
            Internal B.Equiv %% [],
            [ Apply (mem_op, [ Ix 1 %% [] ; Subst.app_expr (Subst.shift 1) e ]) %% []
            ; Apply (mem_op, [ Ix 1 %% [] ; Subst.app_expr (Subst.shift 1) f ]) %% []
            ]
          ) %% []
          |> fun e ->
              match blt with
              | B.Eq -> e
              | B.Neq ->
                  Apply (Internal B.Neg %% [], [e]) %% []
              | _ -> failwith ""
        ) @@ oe

    | Apply ({ core = Internal B.Implies } as op, [ e ; f ]) ->
        let e = self#expr (not b, cx) e in
        let f = self#expr scx f in
        Apply (op, [ e ; f ]) @@ oe
    | Apply ({ core = Internal B.Neg } as op, [ e ]) ->
        let e = self#expr (not b, cx) e in
        Apply (op, [ e ]) @@ oe

    | _ -> super#expr scx oe

  method sequent (b, hx) sq =
    let (_, hx), hs = self#hyps (not b, hx) sq.context in
    let e = self#expr (b, hx) sq.active in
    (b, hx), { context = hs ; active = e }
end

let apply_ext sq =
  let cx = (true, Deque.empty) in
  snd (apply_ext_visitor#sequent cx sq)


let simpl_subseteq_visitor = object (self : 'self)
  inherit [bool] Expr.Visit.map as super

  method expr (b, cx as scx) oe =
    match oe.core with
    | Apply ({ core = Internal B.Subseteq } as op, [ e ; f ])
      when b && (match query op Props.tpars_prop with
                 None -> true | _ -> false) ->
        (* TODO Typelvl=1 *)
        let e = self#expr scx e in
        let f = self#expr scx f in
        let q = Forall in
        let v = assign ("x" %% []) Props.ty0_prop (TAtm TAIdv) in
        let mem_op = Internal B.Mem %% [] in
        Quant (
          q, [ v, Constant, No_domain ],
          Apply (
            Internal B.Implies %% [],
            [ Apply (mem_op, [ Ix 1 %% [] ; Subst.app_expr (Subst.shift 1) e ]) %% []
            ; Apply (mem_op, [ Ix 1 %% [] ; Subst.app_expr (Subst.shift 1) f ]) %% []
            ]
          ) %% []
        ) @@ oe

    | Apply ({ core = Internal B.Implies } as op, [ e ; f ]) ->
        let e = self#expr (not b, cx) e in
        let f = self#expr scx f in
        Apply (op, [ e ; f ]) @@ oe
    | Apply ({ core = Internal B.Neg } as op, [ e ]) ->
        let e = self#expr (not b, cx) e in
        Apply (op, [ e ]) @@ oe

    | _ -> super#expr scx oe

  method sequent (b, hx) sq =
    let (_, hx), hs = self#hyps (not b, hx) sq.context in
    let e = self#expr (b, hx) sq.active in
    (b, hx), { context = hs ; active = e }
end

let simpl_subseteq sq =
  let cx = (true, Deque.empty) in
  snd (simpl_subseteq_visitor#sequent cx sq)


(* {3 Simplify Sets} *)

let normalize = object (self : 'self)
  inherit [unit] Expr.Visit.map as super
  method expr scx oe =
    match oe.core with
    | Apply (e, []) ->
        e $$ oe
    | _ ->
        super#expr scx oe
end

(* A simple function to make one substitution.
 * NOTE This is a DIRTY HACK that circumvents a limitation of {!Subst.app_expr}
 * regarding annotations.  The functions of {!Subst} do not always preserve
 * annotations, which would be an issue here. *)
let subst a b =
  let lam = Lambda ([ "x" %% [], Shape_expr ], a) %% [] in
  let arg = Apply (b, []) %% [] in
  Subst.normalize lam [arg] |>
  normalize#expr ((), Deque.empty)

let simplify_sets_visitor = object (self : 'self)
  inherit [bool] Expr.Visit.map as super

  method expr (b, hx as scx) oe =
    match oe.core with
    (* x \in { a1, .., an }
     *    -->
     * x = a1 \/ .. \/ x = an *)
    | Apply ({ core = Internal B.Mem } as op, [ e1 ; { core = SetEnum es } as e2 ])
      when not (has op Props.tpars_prop) ->
        let n = List.length es in
        if n = 0 then
          Internal B.FALSE @@ oe
        else if n = 1 then
          let e1 = self#expr scx e1 in
          let es = List.map (self#expr scx) es in
          let e2 =
            match es with
            | [e] -> e $$ e2
            | _ -> error ~at:e2 "Internal error"
          in
          let eq = assign (Internal B.Eq %% []) Props.tpars_prop [ TAtm TAIdv ] in
          Apply (eq, [ e1 ; e2 ]) @@ oe
        else
          let e1 = self#expr scx e1 in
          let es = List.map (self#expr scx) es in
          let eq = assign (Internal B.Eq %% []) Props.tpars_prop [ TAtm TAIdv ] in
          List (Or, List.map begin fun e2 ->
            Apply (eq, [ e1 ; e2 ]) %% []
          end es) @@ e2

    (* x \in SUBSET a
     *    -->
     * \A y : y \in x => y \in a *)
    | Apply ({ core = Internal B.Mem } as op1, [ e1 ; { core = Apply ({ core = Internal B.SUBSET } as op2, [ e2 ]) } ])
      when ((not b) || not (Params.debugging "nonewqut"))
      && not (has op1 Props.tpars_prop) && not (has op2 Props.tpars_prop) ->
        let e1 = self#expr scx e1 in
        let e2 = self#expr scx e2 in
        let v = assign ("v" %% []) Props.ty0_prop (TAtm TAIdv) in
        let e =
          let e1 = Subst.app_expr (Subst.shift 1) e1 in
          let e2 = Subst.app_expr (Subst.shift 1) e2 in
          Apply (
            Internal B.Implies %% [],
            [ Apply (
              Internal B.Mem %% [],
              [ Ix 1 %% []
              ; e1 ]
            ) %% []
            ; Apply (
              Internal B.Mem %% [],
              [ Ix 1 %% []
              ; e2 ]
            ) %% [] ]
          ) %% []
        in
        Quant (Forall, [ v, Constant, No_domain ], e) @@ oe

    (* x \in UNION a
     *    -->
     * \E y : y \in a /\ x \in y *)
    | Apply ({ core = Internal B.Mem } as op1, [ e1 ; { core = Apply ({ core = Internal B.UNION } as op2, [ e2 ]) } ])
      when ((not b) && not (Params.debugging "nonewqut"))
      && not (has op1 Props.tpars_prop) && not (has op2 Props.tpars_prop) ->
        let e1 = self#expr scx e1 in
        let e2 = self#expr scx e2 in
        let v = assign ("v" %% []) Props.ty0_prop (TAtm TAIdv) in
        let e =
          let e1 = Subst.app_expr (Subst.shift 1) e1 in
          let e2 = Subst.app_expr (Subst.shift 1) e2 in
          Apply (
            Internal B.Conj %% [],
            [ Apply (
              Internal B.Mem %% [],
              [ Ix 1 %% []
              ; e2 ]
            ) %% []
            ; Apply (
              Internal B.Mem %% [],
              [ e1
              ; Ix 1 %% [] ]
            ) %% [] ]
          ) %% []
        in
        Quant (Exists, [ v, Constant, No_domain ], e) @@ oe

    (* x \in a \cup b
     *    -->
     * x \in a \/ x \in b *)
    | Apply ({ core = Internal B.Mem } as op1, [ e1 ; { core = Apply ({ core = Internal B.Cup } as op2, [ e2 ; e3 ]) } ])
      when not (has op1 Props.tpars_prop) && not (has op2 Props.tpars_prop) ->
        let e1 = self#expr scx e1 in
        let e2 = self#expr scx e2 in
        let e3 = self#expr scx e3 in
        Apply (
          Internal B.Disj %% [],
          [ Apply (
            Internal B.Mem %% [],
            [ e1
            ; e2 ]
          ) %% []
          ; Apply (
            Internal B.Mem %% [],
            [ e1
            ; e3 ]
          ) %% [] ]
        ) @@ oe

    (* x \in a \cap b
     *    -->
     * x \in a /\ x \in b *)
    | Apply ({ core = Internal B.Mem } as op1, [ e1 ; { core = Apply ({ core = Internal B.Cap } as op2, [ e2 ; e3 ]) } ])
      when not (has op1 Props.tpars_prop) && not (has op2 Props.tpars_prop) ->
        let e1 = self#expr scx e1 in
        let e2 = self#expr scx e2 in
        let e3 = self#expr scx e3 in
        Apply (
          Internal B.Conj %% [],
          [ Apply (
            Internal B.Mem %% [],
            [ e1
            ; e2 ]
          ) %% []
          ; Apply (
            Internal B.Mem %% [],
            [ e1
            ; e3 ]
          ) %% [] ]
        ) @@ oe

    (* x \in a \ b
     *    -->
     * x \in a /\ ~ x \in b *)
    | Apply ({ core = Internal B.Mem } as op1, [ e1 ; { core = Apply ({ core = Internal B.Setminus } as op2, [ e2 ; e3 ]) } ])
      when not (has op1 Props.tpars_prop) && not (has op2 Props.tpars_prop) ->
        let e1 = self#expr scx e1 in
        let e2 = self#expr scx e2 in
        let e3 = self#expr scx e3 in
        Apply (
          Internal B.Conj %% [],
          [ Apply (
            Internal B.Mem %% [],
            [ e1
            ; e2 ]
          ) %% []
          ; Apply (
            Internal B.Neg %% [],
            [ Apply (
              Internal B.Mem %% [],
              [ e1
              ; e3 ]
            ) %% [] ]
          ) %% [] ]
        ) @@ oe

    (* x \in { y \in S : P(y) }
     *    -->
     * x \in S /\ P(x) *)
    | Apply ({ core = Internal B.Mem } as op, [ e1 ; { core = SetSt (v, e2, e3) } ])
      when not (has op Props.tpars_prop) ->
        let e1 = self#expr scx e1 in
        let e2 = self#expr scx e2 in
        let h = Fresh (v, Shape_expr, Constant, Unbounded) %% [] in
        let scx' = Expr.Visit.adj scx h in
        let e3 = self#expr scx' e3 in
        Apply (
          Internal B.Conj %% [],
          [ Apply (
            Internal B.Mem %% [],
            [ e1
            ; e2 ]
          ) %% []
          ; subst e3 e1 ]
        ) @@ oe

    (* x \in { F(y1, .., yn) : y1 \in a1, .., yn \in an }
     *    -->
     * \E y1, .., yn : y1 \in a1 /\ .. /\ yn \in an /\ x = F(y1, .., yn) *)
    | Apply ({ core = Internal B.Mem } as op, [ e1 ; { core = SetOf (e2, bs) } ])
      when ((not b) || not (Params.debugging "nonewqut"))
      && not (has op Props.tpars_prop) ->
        let e1 = self#expr scx e1 in
        let scx', bs = self#bounds scx bs in
        let e2 = self#expr scx' e2 in
        let bs, ds =
          List.fold_left begin fun (r_bs, r_ds, dit) (v, k, dom) ->
            match dom, dit with
            | Domain d, _
            | Ditto, Some d ->
                (v, k, No_domain) :: r_bs, d :: r_ds, Some d
            | _ ->
                error ~at:v "Missing bound"
          end ([], [], None) bs |>
          fun (r_bs, r_ds, _) ->
            (List.rev r_bs, List.rev r_ds)
        in
        let eq_op = assign (Internal B.Eq %% []) Props.tpars_prop [ TAtm TAIdv ] in
        let n = List.length bs in
        Quant (
          Exists,
          bs,
          List (
            And,
            Apply (
              eq_op,
              [ Subst.app_expr (Subst.shift n) e1
              ; e2
              ]
            ) %% [] ::
            List.mapi begin fun i d ->
              Apply (
                Internal B.Mem %% [],
                [ Ix (i + 1) %% []
                ; Subst.app_expr (Subst.shift n) d
                ]
              ) %% []
            end ds
          ) %% []
        ) @@ oe

    (* x \in [ a -> b ]
     *    -->
     * IsAFcn(x) /\ DOMAIN x = a /\ \A y : y \in a => x[y] \in b *)
    (* FIXME This rule inserts an Opaque "IsAFcn" which is recognized later
     * during standardization. Careful when modifying! *)
    | Apply ({ core = Internal B.Mem } as op1, [ e1 ; { core = Arrow (e2, e3) } ])
      when (b || not (Params.debugging "nonewqut"))
      && not (has op1 Props.tpars_prop) ->
        let e1 = self#expr scx e1 in
        let e2 = self#expr scx e2 in
        let e3 = self#expr scx e3 in
        let eq_op = assign (Internal B.Eq %% []) Props.tpars_prop [ TAtm TAIdv ] in
        List (
          And,
          [ Apply (
            Opaque "IsAFcn" %% [],
            [ e1
            ]) %% []
          ; Apply (
            eq_op,
            [ Apply (
              Internal B.DOMAIN %% [],
              [ e1
              ]) %% []
            ; e2
            ]) %% []
          ; Quant (
            Forall,
            [ assign ("x" %% []) Props.ty0_prop (TAtm TAIdv), Constant, No_domain ],
            Apply (
              Internal B.Implies %% [],
              [ Apply (
                Internal B.Mem %% [],
                [ Ix 1 %% []
                ; Subst.app_expr (Subst.shift 1) e2
                ]) %% []
              ; Apply (
                Internal B.Mem %% [],
                [ FcnApp (
                  Subst.app_expr (Subst.shift 1) e1,
                  [ Ix 1 %% []
                  ]) %% []
                ; Subst.app_expr (Subst.shift 1) e3
                ]) %% []
              ]
            ) %% []
          ) %% []
          ]) @@ oe

    (* x \in a1 \X .. \X an
     *    -->
     * \E y1, .., yn : y1 \in a1 /\ .. /\ yn \in an /\ x = << y1, .., yn >> *)
    | Apply ({ core = Internal B.Mem } as op, [ e1 ; { core = Product es } ])
      when ((not b) || not (Params.debugging "nonewqut"))
      && not (has op Props.tpars_prop) ->
        let e1 = self#expr scx e1 in
        let es = List.map (self#expr scx) es in
        let eq_op = assign (Internal B.Eq %% []) Props.tpars_prop [ TAtm TAIdv ] in
        let n = List.length es in
        let bs =
          List.init n begin fun i ->
            let v = ("e" ^ string_of_int (i + 1)) %% [] in
            let v = assign v Props.ty0_prop (TAtm TAIdv) in
            (v, Constant, No_domain)
          end
        in
        Quant (
          Exists,
          bs,
          List (
            And,
            Apply (
              eq_op,
              [ Subst.app_expr (Subst.shift n) e1
              ; Tuple (
                List.init n (fun i -> Ix (n - i) %% [])
              ) %% []
              ]
            ) %% [] ::
            List.mapi begin fun i e ->
              Apply (
                Internal B.Mem %% [],
                [ Ix (n - i) %% []
                ; Subst.app_expr (Subst.shift n) e
                ]
              ) %% []
            end es
          ) %% []
        ) @@ oe

    (* x \in a..b
     *    -->
     * x \in Int /\ a <= x /\ x <= b *)
    | Apply ({ core = Internal B.Mem } as op1, [ e1 ; { core = Apply ({ core = Internal B.Range } as op2, [ e2 ; e3 ]) } ])
      when not (has op1 Props.tpars_prop) && not (has op2 Props.tpars_prop) ->
        let e1 = self#expr scx e1 in
        let e2 = self#expr scx e2 in
        let e3 = self#expr scx e3 in
        List (
          And,
          [ Apply (
            Internal B.Mem %% [],
            [ e1
            ; Internal B.Int %% []
            ]) %% []
          ; Apply (
            Internal B.Lteq %% [],
            [ e2
            ; e1
            ]) %% []
          ; Apply (
            Internal B.Lteq %% [],
            [ e1
            ; e3
            ]) %% []
          ]
        ) @@ oe

    (* x \in Nat
     *    -->
     * x \in Int /\ 0 <= x *)
    | Apply ({ core = Internal B.Mem } as op1, [ e1 ; { core = Internal B.Nat } as op2 ])
      when not (has op1 Props.tpars_prop) && not (has op2 Props.tpars_prop) ->
        let e1 = self#expr scx e1 in
        let zero_op =
          if Params.debugging "noarith" then
            Num ("0", "") %% []
          else
            Num ("0", "") %% [] |> fun e ->
             assign e Props.tpars_prop [] |> fun e ->
               assign e Props.icast_prop (TAtm TAInt)
        in
        Apply (
          Internal B.Conj %% [],
          [ Apply (
            Internal B.Mem %% [],
            [ e1
            ; Internal B.Int %% []
            ]) %% []
          ; Apply (
            Internal B.Lteq %% [],
            [ zero_op
            ; e1
            ]) %% []
          ]) %% []

    (* x = y    when x or y's top connective is a set constructor
     *    -->
     * \A z : z \in x <=> z \in y *)
    | Apply ({ core = Internal (B.Eq | B.Neq as blt) } as op, [ e ; f ])
      when (eq_pol b blt || not (Params.debugging "nonewqut"))
      && (is_set e || is_set f)
      && (match query op Props.tpars_prop with
          Some [TAtm TAIdv] -> true | _ -> false) ->
        let e = self#expr scx e in
        let f = self#expr scx f in
        let q =
          match blt with
          | B.Eq -> Forall
          | B.Neq -> Exists
          | _ -> failwith ""
        in
        let v = assign ("x" %% []) Props.ty0_prop (TAtm TAIdv) in
        let mem_op = Internal B.Mem %% [] in
        Quant (
          q, [ v, Constant, No_domain ],
          Apply (
            Internal B.Equiv %% [],
            [ Apply (mem_op, [ Ix 1 %% [] ; Subst.app_expr (Subst.shift 1) e ]) %% []
            ; Apply (mem_op, [ Ix 1 %% [] ; Subst.app_expr (Subst.shift 1) f ]) %% []
            ]
          ) %% []
          |> fun e ->
              match blt with
              | B.Eq -> e
              | B.Neq ->
                  Apply (Internal B.Neg %% [], [e]) %% []
              | _ -> failwith ""
        ) @@ oe

    (* x \subseteq y    when x or y's top connective is a set constructor
     *    -->
     * \A z : z \in x => z \in y *)
    | Apply ({ core = Internal B.Subseteq } as op, [ e ; f ])
      when (b || not (Params.debugging "nonewqut"))
        && (match query op Props.tpars_prop with
                 None -> true | _ -> false) ->
        let e = self#expr scx e in
        let f = self#expr scx f in
        let q = Forall in
        let v = assign ("x" %% []) Props.ty0_prop (TAtm TAIdv) in
        let mem_op = Internal B.Mem %% [] in
        Quant (
          q, [ v, Constant, No_domain ],
          Apply (
            Internal B.Implies %% [],
            [ Apply (mem_op, [ Ix 1 %% [] ; Subst.app_expr (Subst.shift 1) e ]) %% []
            ; Apply (mem_op, [ Ix 1 %% [] ; Subst.app_expr (Subst.shift 1) f ]) %% []
            ]
          ) %% []
        ) @@ oe

    (* x \in a..b   when x, a, b : int
     *    -->
     * a <= x /\ x <= b *)
    | Apply ({ core = Internal B.Mem } as op1, [ e1 ; { core = Apply ({ core = Internal B.Range } as op2, [ e2 ; e3 ]) } ])
      when query op2 Props.tpars_prop = Some []
        && ((query op1 Props.tpars_prop = Some [ TAtm TAInt ])
          || (not (has op1 Props.tpars_prop)
              && query e1 Props.icast_prop = Some (TAtm TAInt))) ->
        let e1 = Property.remove (self#expr scx e1) Props.icast_prop in
        let e2 = self#expr scx e2 in
        let e3 = self#expr scx e3 in
        let lteq_op = assign (Internal B.Lteq %% []) Props.tpars_prop [ TAtm TAInt ] in
        List (
          And,
          [ Apply (
            lteq_op,
            [ e2
            ; e1
            ]) %% []
          ; Apply (
            lteq_op,
            [ e1
            ; e3
            ]) %% []
          ]
        ) @@ oe

    (* x \in Int    when x : int
     *    -->
     * TRUE *)
    | Apply ({ core = Internal B.Mem } as op1, [ e1 ; { core = Internal B.Int } as op2 ])
      when (query op2 Props.tpars_prop = Some [])
        && ((query op1 Props.tpars_prop = Some [ TAtm TAInt ])
          || (not (has op1 Props.tpars_prop)
            && query e1 Props.icast_prop = Some (TAtm TAInt))) ->
        Internal B.TRUE @@ oe

    (* x \in Nat    when x : int
     *    -->
     * x \in Int /\ 0 <= x *)
    | Apply ({ core = Internal B.Mem } as op1, [ e1 ; { core = Internal B.Nat } as op2 ])
      when (query op2 Props.tpars_prop = Some [])
        && ((query op1 Props.tpars_prop = Some [ TAtm TAInt ])
          || (not (has op1 Props.tpars_prop)
            && query e1 Props.icast_prop = Some (TAtm TAInt))) ->
        let e1 = Property.remove (self#expr scx e1) Props.icast_prop in
        let lteq_op = assign (Internal B.Lteq %% []) Props.tpars_prop [ TAtm TAInt ] in
        let zero_op = assign (Num ("0", "") %% []) Props.tpars_prop [] in
        Apply (
          lteq_op,
          [ zero_op
          ; e1
        ]) @@ oe

    | Apply ({ core = Internal B.Implies } as op, [ e ; f ]) ->
        let e = self#expr (not b, hx) e in
        let f = self#expr scx f in
        Apply (op, [ e ; f ]) @@ oe
    | Apply ({ core = Internal B.Neg } as op, [ e ]) ->
        let e = self#expr (not b, hx) e in
        Apply (op, [ e ]) @@ oe
    | Apply ({ core = Internal B.Equiv } as op, [ e ; f ]) ->
        let e1 = self#expr (not b, hx) e in
        let f1 = self#expr (b, hx) f in
        let e2 = self#expr (b, hx) e in
        let f2 = self#expr (not b, hx) f in
        Apply (
          Internal B.Conj @@ op,
          [ Apply (
            Internal B.Implies %% [],
            [ e1
            ; f1
            ]) %% []
          ; Apply (
            Internal B.Implies %% [],
            [ f2
            ; e2
            ]) %% []
          ]) @@ oe

    | _ -> super#expr scx oe

  method sequent (b, hx) sq =
    let (_, hx), hs = self#hyps (not b, hx) sq.context in
    let e = self#expr (b, hx) sq.active in
    (b, hx), { context = hs ; active = e }
end

let simplify_sets sq =
  let cx = (true, Deque.empty) in
  snd (simplify_sets_visitor#sequent cx sq)

