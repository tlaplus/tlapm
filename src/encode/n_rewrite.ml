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

(* TODO Type preservation for elim_multiarg, elim_tuples *)
(* Need to think about a different use of type annotations for tuples
 * before that. *)


(* {3 Helpers} *)

let error ?at mssg =
  let mssg = "Encode.Rewrite: " ^ mssg in
  (*Errors.bug ?at mssg*)
  failwith mssg

let maybe_assign prop =
  Option.fold (fun x -> assign x prop)


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
                let op = maybe_assign Props.tpars_prop (Internal B.Mem %% []) (query d Props.tpars_prop) in
                let h =
                  Apply (op, [
                    Ix i %% [] ; Subst.app_expr (Subst.shift n) d
                  ]) %% []
                in
                let h =
                  if has d Props.tpars_prop || not !Params.enc_nobool then h
                  else assign h Props.bproj_prop (TAtm TAIdv)
                in
                (nscx, b :: r_bs, h :: r_hs, Some d, i - 1)
            | Ditto, Some d ->
                let op = maybe_assign Props.tpars_prop (Internal B.Mem %% []) (query d Props.tpars_prop) in
                let h = Apply (op, [ Ix i %% [] ; d ]) %% [] in
                let h =
                  if has d Props.tpars_prop || not !Params.enc_nobool then h
                  else assign h Props.bproj_prop (TAtm TAIdv)
                in
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
        let op = maybe_assign Props.tpars_prop (Internal B.Mem %% []) (query d Props.tpars_prop) in
        let h =
          Apply (op, [
            Ix 1 %% [] ; Subst.app_expr (Subst.shift 1) d
          ]) %% []
        in
        let h =
          if has d Props.tpars_prop || not !Params.enc_nobool then h
          else assign h Props.bproj_prop (TAtm TAIdv)
        in
        let e =
          if has oe Props.tpars_prop || not !Params.enc_nobool then
            Apply (Internal B.Conj %% [], [ h ; e ]) %% []
          else if has e Props.icast_prop && get e Props.icast_prop = TAtm TABol then
            (* Optimization:
              * `to_idv(e) = true_idv`  -->  `e` *)
            let e = remove e Props.icast_prop in
            assign (
              Apply (Internal B.Conj %% [], [ h ; e ]) %% []
            ) Props.icast_prop (TAtm TABol)
          else
            let e = assign e Props.bproj_prop (TAtm TAIdv) in
            assign (
              Apply (Internal B.Conj %% [], [ h ; e ]) %% []
            ) Props.icast_prop (TAtm TABol)
        in
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
          let op = maybe_assign Props.tpars_prop (Internal B.Mem %% []) (query d Props.tpars_prop) in
          let e =
            Apply (op, [
              Ix 1 %% [] ; Subst.app_expr (Subst.shift 1) d
            ]) %% []
          in
          let e =
            if has d Props.tpars_prop || not !Params.enc_nobool then e
            else assign e Props.bproj_prop (TAtm TAIdv)
          in
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


(* {3 NotMem Simplification} *)

let elim_notmem_visitor = object (self : 'self)
  inherit [unit] Visit.map as super

  method expr scx oe =
    match oe.core with
    | Apply ({ core = Internal B.Notmem } as op, [ e ; f ]) ->
        let e = self#expr scx e in
        let f = self#expr scx f in
        if has op Props.tpars_prop || not !Params.enc_nobool then
          Apply (Internal B.Neg %% [], [
            Apply (Internal B.Mem @@ op, [ e ; f ]) %% []
          ]) @@ oe
        else
          (* Not sure this is the best way to preserve properties *)
          remove (
            Apply (Internal B.Neg %% [], [
              assign (
                Apply (Internal B.Mem @@ op, [ e ; f ]) %% []
              ) Props.bproj_prop (TAtm TAIdv)
            ]) @@ oe
          ) Props.bproj_prop
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
    | Apply ({ core = Internal B.Lt } as op, [ e ; f ]) ->
        let e = self#expr scx e in
        let f = self#expr scx f in
        let neq_op = maybe_assign Props.tpars_prop (Internal B.Neq %% []) (query op Props.tpars_prop) in
        Apply (Internal B.Conj %% [], [
          Apply (Internal B.Lteq @@ op, [ e ; f ]) @@ oe ;
          Apply (neq_op, [ e ; f ]) %% []
        ]) %% []

    | Apply ({ core = Internal B.Gt } as op, [ e ; f ]) ->
        let e = self#expr scx e in
        let f = self#expr scx f in
        let neq_op = maybe_assign Props.tpars_prop (Internal B.Neq %% []) (query op Props.tpars_prop) in
        Apply (Internal B.Conj %% [], [
          Apply (Internal B.Lteq @@ op, [ f ; e ]) @@ oe ;
          Apply (neq_op, [ f ; e ]) %% []
        ]) %% []

    | Apply ({ core = Internal B.Gteq } as op, [ e ; f ]) ->
        let e = self#expr scx e in
        let f = self#expr scx f in
        Apply (Internal B.Lteq @@ op, [ f ; e ]) @@ oe

    | _ -> super#expr scx oe
end

let elim_compare sq =
  let cx = ((), Deque.empty) in
  snd (elim_compare_visitor #sequent cx sq)


(* {3 EXCEPT Elimination} *)

(* FIXME not type preserving *)

let elim_except_visitor = object (self : 'self)
  inherit [unit] Visit.map as super

  method expr scx oe =
    match oe.core with
    | Except (e, [ ([d], a as exp) ]) ->
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
    | Fcn (bs, e) when List.length bs > 1 ->
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
        let v = "t" %% [] in
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

    | FcnApp (e1, es) when List.length es > 1 ->
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
    | Product es ->
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
      let v = "f" %% [] in
      SetSt (v, e1, e2) @@ oe

    | Tuple es ->
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
        let v = "i" %% [] in
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
    | Rect fs ->
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
        let v = "f" %% [] in
        SetSt (v, e1, e2) @@ oe

    | Record fs ->
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
        let v = "s" %% [] in
        Fcn ([ v, Constant, Domain rg ], e) @@ oe

    | Dot (e, s) ->
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

  method expr scx oe =
    match oe.core with
    | Apply ({ core = Internal (B.Eq | B.Neq as b) } as op, [ e ; f ])
      when eq_pol (fst scx) b && (is_set e || is_set f) ->
        let e = self#expr scx e in
        let f = self#expr scx f in
        let oty =
          query op Props.tpars_prop |>
          Option.map begin function [ty] -> ty | _ -> error ~at:op "Bad type annotation" end
        in
        let q =
          match b with
          | B.Eq -> Forall
          | B.Neq -> Exists
          | _ -> failwith ""
        in
        let v = Option.fold (fun v -> assign v Props.ty0_prop) ("x" %% []) oty in
        let mem_op = Option.fold (fun e ty -> assign e Props.tpars_prop [ ty ]) (Internal B.Mem %% []) oty in
        Quant (
          q, [ v, Constant, No_domain ],
          Apply (
            Internal B.Equiv %% [],
            [ Apply (mem_op, [ Ix 1 %% [] ; Subst.app_expr (Subst.shift 1) e ]) %% []
            ; Apply (mem_op, [ Ix 1 %% [] ; Subst.app_expr (Subst.shift 1) f ]) %% []
            ]
          ) %% []
          |> fun e ->
              match b with
              | B.Eq -> e
              | B.Neq ->
                  Apply (Internal B.Neg %% [], [e]) %% []
              | _ -> failwith ""
        ) @@ oe
    | _ -> super#expr scx oe
end

let apply_ext sq =
  let cx = (true, Deque.empty) in
  snd (apply_ext_visitor#sequent cx sq)

