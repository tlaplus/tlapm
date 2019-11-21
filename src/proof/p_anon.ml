(*
 * proof/anon.ml --- proofs (anonymization)
 * anonymization is the replacement of named bounded variables with de-bruijn
 * indicies
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

Revision.f "$Rev$";;

open Ext
open Property
open Expr.T
open Expr.Subst

open P_t

let bump = P_visit.bump
let badexp = Expr.Deref.badexp

let tuple_form sq =
  let nhyps = Deque.size sq.context in
  let facs = ref Deque.empty in
  let rec spin cx = match Deque.front cx with
    | None ->
        facs := Deque.snoc !facs (app_expr (shift 1) sq.active)
    | Some (h, cx) -> begin
        let shf = shift (nhyps - Deque.size !facs + 1) in
        match h.core with
          | Fact (f, _, _) ->
              facs := Deque.snoc !facs (app_expr shf f) ;
              spin cx
          | Fresh (_, _, _, Bounded (ran, _)) ->
              let f = Apply (Internal Builtin.Mem @@ ran, [
                               Ix 0 @@ ran ;
                               ran ;
                             ]) @@ ran
              in
              facs := Deque.snoc !facs (app_expr shf f) ;
              spin cx
          | _ ->
              facs := Deque.snoc !facs badexp ;
              spin cx
      end
  in
  spin sq.context ;
  match Deque.to_list !facs with
    | [f] -> f.core
    | facs -> Tuple facs


let citable st = match st.core with
  | Use _ | Hide _ | Define _ -> false
  | _ -> true


let push_name sn (stack, cx) = ((string_of_stepno sn) :: stack, cx);;

class anon = object (self : 'self)
  inherit [string list] P_visit.map as super
  inherit Expr.Anon.anon

  method proof scx prf = match prf.core with
    | Steps (inits, qed) ->
        let (scx, inits) = self#steps scx inits in
        let sn = get prf Props.step in
        (* add QED step name to warn list, because QED steps never have
           assumptions *)
        let scx = push_name sn scx in
        let qed_prf = self#proof scx (get_qed_proof qed) in
        Steps (inits, {qed with core = Qed qed_prf}) @@ prf
    | _ ->
        super#proof scx prf

  method step scx st =
    (* make all steps "named" for better reference *)
    let sn = match get st Props.step with
      | Unnamed (n, _) when citable st ->
          Named (n, "_a" ^ string_of_int (Std.unique ()), true)
      | sn -> sn in
    let st = assign st Props.step sn in
    let adj_step scx df =
      Expr.Visit.adj scx (Defn (Operator (string_of_stepno sn @@ st, df) @@ st,
                                Proof Always, Visible, Local) @@ st)
    in
    match st.core with
      | Assert (sq, prf) ->
          let (_, sq) = self#sequent scx sq in
          let prf =
            (* assumptions *)
            let scx = Expr.Visit.adjs scx (Deque.to_list sq.context) in
            (* negation of old goal *)
            let scx = bump scx 1 in
            (* tuplified form of assertion *)
            let tup = tuple_form sq @@ st in
            let scx = adj_step scx tup in
            (* hidden assertion that the tuple is true *)
            let scx = bump scx 1 in
            (* Add name to warn list if assumptions are empty *)
            let scx =
              if Deque.size sq.context = 0 then push_name sn scx else scx
            in
            self#proof scx prf
          in
          let st = Assert (sq, prf) @@ st in
          (* step name defn. *)
          let scx = adj_step scx (exprify_sequent sq @@ st) in
          (* fact that it is true *)
          let scx = bump scx 1 in
          (scx, st)
      | Pcase (e, prf) ->
          let e = self#expr scx e in
          let prf =
            (* negation of old goal + new assumption *)
            let scx = bump scx 2 in
            (* assertion *)
            let tup = Tuple [app_expr (shift 2) e] @@ st in
            let scx = adj_step scx tup in
            (* hidden assertion that the tuple is true *)
            let scx = bump scx 1 in
            self#proof scx prf
          in
          let st = Pcase (e, prf) @@ st in
          (* step name defn *)
          let scx = adj_step scx (Tuple [e] @@ st) in
          (* fact that it is true *)
          let scx = bump scx 1 in
          (scx, st)
      | Suffices (sq, prf) ->
          let (_, sq) = self#sequent scx sq in
          let prf =
            (* step name definition *)
            let fac = Tuple [exprify_sequent sq @@ st] @@ st in
            let scx = adj_step scx fac in
            (* step name fact *)
            let scx = bump scx 1 in
            self#proof scx prf in
          let st = Suffices (sq, prf) @@ st in
          (* assumptions *)
          let scx = Expr.Visit.adjs scx (Deque.to_list sq.context) in
          (* negation of old goal *)
          let scx = bump scx 1 in
          (* tuplified form of assertion *)
          let tup = Tuple [tuple_form sq @@ st] @@ st in
          let scx = adj_step scx tup in
          (* hidden assertion that the tuple is true *)
          let scx = bump scx 1 in
          (scx, st)
      | Have e ->
          let e = self#expr scx e in
          let st = Have e @@ st in
          (* new assumption + negation of old goal *)
          let scx = bump scx 2 in
          (* tuplified form of assertion *)
          let tup = Tuple [app_expr (shift 2) e] @@ st in
          let scx = adj_step scx tup in
          (* hidden assertion that the tuple is true *)
          let scx = bump scx 1 in
          (scx, st)
      | Take bs ->
          (* new declarations *)
          let (scx, bs) = self#bounds scx bs in
          let st = Take bs @@ st in
          (* negation of old goal *)
          let scx = bump scx 1 in
          (* equivalent universal for naming *)
          let unv = Quant (Forall, bs, badexp) @@ st in
          let scx = adj_step scx unv in
          (* hidden assertion that the tuple is true *)
          let scx = bump scx 1 in
          (scx, st)
      | Witness es ->
          let es = List.map (self#expr scx) es in
          let st = Witness es @@ st in
          (* no new assumptions *)
          (* negation of old goal *)
          let scx = bump scx 1 in
          (* tuplified form of assumption *)
          let tup = Tuple es @@ st in
          let scx = adj_step scx tup in
          (* hidden assertion that the tuple is true *)
          let scx = bump scx 1 in
          (scx, st)
      | Pick (bs, e, prf) ->
          let (bs, e) =
            let (scx, bs) = self#bounds scx bs in
            let e = self#expr scx e in
            (bs, e)
          in
          let prf =
            (* I only have a faint idea of what I'm doing here -- Damien *)
            let scx = bump scx 1 in
            let ex = Quant (Exists, bs, e) @@ st in
            let scx = adj_step scx ex in
            let scx = bump scx 1 in
            let scx = push_name sn scx in
            self#proof scx prf
          in
          let st = Pick (bs, e, prf) @@ st in
          (* step name + fact for existential *)
          let scx = bump scx 2 in
          (* there is a SUFFICES here *)
          (*    ... so add assumptions for the new identifiers *)
          let hyps = List.map begin
            fun (v, k, _) -> Fresh (v, Shape_expr, k, Unbounded) @@ v
          end bs in
          let scx = Expr.Visit.adjs scx hyps in
          (*    ... then add assumption about the body of the PICK *)
          (*    ... then add the negation of the old goal *)
          let scx = bump scx 2 in
          (*    ... then the step name definition for the SUFFICES *)
          let ex = app_expr (shift (4 + List.length bs)) (Quant (Exists, bs, e) @@ st) in
          let scx = adj_step scx ex in
          (*    ... then the conjunction of the nondom facts in the SUFFICES *)
          let scx = bump scx 1 in
          (* finally, we are in the next step *)
          (scx, st)
      | _ ->
          super#step scx st
end

let anon = new anon
