(*
 * encode/rewrite.ml --- rewrite sequents
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

open Ext
open Property
open Expr.T
open Type.T

module Subst = Expr.Subst
module Visit = Expr.Visit
module B = Builtin

(* TODO Type preservation for elim_bounds, elim_multiarg, elim_tuples, elim_records *)


let error ?at mssg =
  let mssg = "Encode.Rewrite: " ^ mssg in
  Errors.bug ?at mssg


(* {3 Bounds Elimination} *)

let elim_bounds_visitor = object (self : 'self)
  inherit [unit] Visit.map as super

  method expr scx oe =
    match oe.core with

    | Quant (q, bs, e) ->
        let n = List.length bs in
        let scx, rbs, hs, dit, _ =
          List.fold_left begin fun (nscx, rbs, hs, dit, i) (v, k, d) ->
            let h = Fresh (v, Shape_expr, k, Unbounded) %% [] in
            let nscx = Visit.adj scx h in
            let b = (v, k, No_domain) in
            match d, dit with
            | No_domain, _ ->
                (nscx, b :: rbs, hs, None, i - 1)
            | Domain d, _ ->
                let d = self#expr scx d in
                let d = Subst.app_expr (Subst.shift n) d in
                let h =
                  Apply (Internal B.Mem %% [], [
                    Ix i %% [] ; d
                  ]) %% []
                in
                (nscx, b :: rbs, h :: hs, Some d, i - 1)
            | Ditto, Some d ->
                let h =
                  Apply (Internal B.Mem %% [], [
                    Ix i %% [] ; d
                  ]) %% []
                in
                (nscx, b :: rbs, h :: hs, Some d, i - 1)
            | _, _ ->
                error ~at:oe "Missing bound"
          end (scx, [], [], None, n) bs
        in
        let bs = List.rev rbs in
        let hs = List.rev hs in
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
        let e =
          Apply (Internal B.Conj %% [], [
            Apply (Internal B.Mem %% [], [
              Ix 1 %% [] ; Subst.app_expr (Subst.shift 1) d
            ]) %% [] ;
            e
          ]) %% []
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
          let hh =
            Fact (
              Apply (Internal B.Mem %% [], [
                Ix 1 %% [] ; Subst.app_expr (Subst.shift 1) d
              ]) %% [],
              vis, NotSet
            ) %% []
          in
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


(* {3 NotMem Elimination} *)

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
    | Apply ({ core = Internal B.Lt } as op, [ e ; f ]) ->
        let e = self#expr scx e in
        let f = self#expr scx f in
        Apply (Internal B.Conj %% [], [
          Apply (Internal B.Lteq @@ op, [ e ; f ]) @@ oe ;
          Apply (Internal B.Neq %% [], [ e ; f ]) %% []
        ]) %% []

    | Apply ({ core = Internal B.Gt } as op, [ e ; f ]) ->
        let e = self#expr scx e in
        let f = self#expr scx f in
        Apply (Internal B.Conj %% [], [
          Apply (Internal B.Lteq @@ op, [ f ; e ]) @@ oe ;
          Apply (Internal B.Neq %% [], [ f ; e ]) %% []
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


(* {3 Multi-arguments Functions Elimination} *)

let elim_multiarg_visitor = object (self : 'self)
  inherit [unit] Visit.map as super

  method expr scx oe =
    match oe.core with
    | Fcn (bs, e) when List.length bs > 1 ->
        let scx, bs = self#bounds scx bs in
        let rvs, rbs, _ =
          List.fold_left begin fun (rvs, rbs, dit) (v, _, d) ->
            match d, dit with
            | Domain b, _
            | Ditto, Some b ->
                (v :: rvs, b :: rbs, Some b)
            | _, _ -> error ~at:oe "Missing bound on Fcn"
          end ([], [], None) bs
        in
        let v = "t" %% [] in
        let b = Product (List.rev rbs) %% [] in
        let e = self#expr scx e in
        let dfs =
          List.mapi begin fun i v ->
            Operator (v, FcnApp (
              Ix 1 %% [], [ Num (string_of_int (i + 1), "") %% [] ]
            ) %% []) %% []
          end (List.rev rvs)
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


(* {3 Except Elimination} *)

let elim_except_visitor = object (self : 'self)
  inherit [unit] Visit.map as super

  method expr scx oe =
    match oe.core with
    (* NOTE Except-expressions are normalized in {!Expr.Elab} *)
    | Except (e1, [ xp ]) ->
        let e1 = self#expr scx e1 in
        let xps, e3 = self#exspec scx xp in
        let e2 =
          match xps with
          | [ Except_apply e2 ] -> e2
          | [ Except_dot s ] -> String s %% []
          | _ -> error ~at:oe "Unsupported EXCEPT"
        in
        let b = Apply (Internal B.DOMAIN %% [], [ e1 ]) %% [] in
        let e =
          If (
            Apply (Internal B.Eq %% [], [ Ix 1 %% [] ; Subst.app_expr (Subst.shift 1) e2 ]) %% [],
            Subst.app_expr (Subst.shift 1) e3,
            FcnApp (Subst.app_expr (Subst.shift 1) e1, [ Ix 1 %% [] ]) %% []
          ) %% []
        in
        let v = "x" %% [] in
        Fcn ([ v, Constant, Domain b ], e) @@ oe

    | _ -> super#expr scx oe
end

let elim_except sq =
  let cx = ((), Deque.empty) in
  snd (elim_except_visitor #sequent cx sq)


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
          query op Props.targs_prop |>
          Option.map begin function [ty] -> ty | _ -> error ~at:op "Bad type annotation" end
        in
        let q =
          match b with
          | B.Eq -> Forall
          | B.Neq -> Exists
          | _ -> failwith ""
        in
        let v = Option.fold (fun v -> assign v Props.type_prop) ("x" %% []) oty in
        let mem_op = Option.fold (fun e ty -> assign e Props.targs_prop [ ty ]) (Internal B.Mem %% []) oty in
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

