(*
 * proof/visit.ml --- default visitor for proofs
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

(** default visitors for proofs *)

open Ext

open Property

module Dq = Deque

open Expr.T

open P_t

let dummy = At false @@ nowhere
let dummy_fact = Fact (dummy, Visible, Always) @@ nowhere

let rec bump scx = function
  | 0 -> scx
  | n -> bump (Expr.Visit.adj scx dummy_fact) (n - 1)

class virtual ['hyp] map = object (self : 'self)
  inherit ['hyp] Expr.Visit.map

  method proof scx pf = match pf.core with
    | Obvious | Omitted _ | Error _ -> pf
    | By (us, onl) ->
        By (self#usable scx us, onl) @@ pf
    | Steps (inits, qed) ->
        let (scx, inits) = self#steps scx inits in
        let qed_prf = self#proof scx (get_qed_proof qed) in
        Steps (inits, {qed with core = Qed qed_prf}) @@ pf

  method steps scx = function
    | [] -> (scx, [])
    | st :: sts ->
        let (scx, st) = self#step scx st in
        let (scx, sts) = self#steps scx sts in
        (scx, st :: sts)

  method step scx st =
    let stepnm = string_of_stepno (Property.get st Props.step) in
    let adj_step scx =
      Expr.Visit.adj scx (Defn (Operator (stepnm @@ st, dummy) @@ st, Proof
      Always, Visible, Local) @@ st)
    in
    match st.core with
      | Forget k ->
          (scx, Forget k @@ st)
      | Hide us ->
          (scx, Hide (self#usable scx us) @@ st)
      | Use (us, onl) ->
          let us = self#usable scx us in
          (bump scx (List.length us.facts), Use (us, onl) @@ st)
      | Define dfs ->
          let (scx, dfs) = self#defns scx dfs in
          (scx, Define dfs @@ st)
      | Assert (sq, prf) ->
          let (_, sq) = self#sequent scx sq in
          let prf =
            (* assumptions *)
            let scx = Expr.Visit.adjs scx (Deque.to_list sq.context) in
            (* negation of old goal *)
            let scx = bump scx 1 in
            (* tuplified form of assertion *)
            let scx = adj_step scx in
            (* hidden assertion that the tuple is true *)
            let scx = bump scx 1 in
            self#proof scx prf
          in
          let st = Assert (sq, prf) @@ st in
          (* step name defn. *)
          let scx = adj_step scx in
          (* fact that it is true *)
          let scx = bump scx 1 in
          (scx, st)
      | Pcase (e, prf) ->
          let e = self#expr scx e in
          let prf =
            (* negation of old goal + new assumption *)
            let scx = bump scx 2 in
            (* assertion *)
            let scx = adj_step scx in
            (* hidden assertion that the tuple is true *)
            let scx = bump scx 1 in
            self#proof scx prf
          in
          let st = Pcase (e, prf) @@ st in
          (* step name defn *)
          let scx = adj_step scx in
          (* fact that it is true *)
          let scx = bump scx 1 in
          (scx, st)
      | Suffices (sq, prf) ->
          let (_, sq) = self#sequent scx sq in
          let prf =
            (* step name definition *)
            let scx = adj_step scx in
            (* step name fact *)
            let scx = bump scx 1 in
            self#proof scx prf in
          let st = Suffices (sq, prf) @@ st in
          (* assumptions *)
          let scx = Expr.Visit.adjs scx (Deque.to_list sq.context) in
          (* negation of old goal *)
          let scx = bump scx 1 in
          (* tuplified form of assertion *)
          let scx = adj_step scx in
          (* hidden assertion that the tuple is true *)
          let scx = bump scx 1 in
          (scx, st)
      | Have e ->
          let e = self#expr scx e in
          let st = Have e @@ st in
          (* new assumption + negation of old goal *)
          let scx = bump scx 2 in
          (* tuplified form of assertion *)
          let scx = adj_step scx in
          (* hidden assertion that the tuple is true *)
          let scx = bump scx 1 in
          (scx, st)
      | Take bs ->
          (* new declarations *)
          let (scx, bs) = self#bounds scx bs in
          let st = Take bs @@ st in
          (* negation of old goal *)
          let scx = bump scx 1 in
          (* tuplified form of assertion *)
          let scx = adj_step scx in
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
          let scx = adj_step scx in
          (* hidden assertion that the tuple is true *)
          let scx = bump scx 1 in
          (scx, st)
      | Pick (bs, e, prf) ->
          let prf = self#proof (bump scx 3) prf in
          let (bs, e) =
            let (scx, bs) = self#bounds scx bs in
            let e = self#expr scx e in
            (bs, e) in
          let st = Pick (bs, e, prf) @@ st in
          (* equivalent existential for subexps *)
          let scx = adj_step scx in
          (* fact that it is true *)
          let scx = bump scx 1 in
          (* there is a SUFFICES here *)
          (*    ... so add assumptions for the new identifiers *)
          let hyps = List.map begin
            fun (v, k, _) -> Fresh (v, Shape_expr, k, Unbounded) @@ v
          end bs in
          let scx = Expr.Visit.adjs scx hyps in
          (*    ... then add assumption about the body of the PICK *)
          (*    ... then add the negation of the old goal *)
          (*    ... then the step name definition for the SUFFICES *)
          (*    ... then the conjunction of the nondom facts in the SUFFICES *)
          let scx = bump scx 4 in
          (* finally, we are in the next step *)
          (scx, st)

  method usable scx us =
    let usdef dw =
      match dw.core with
      | Dvar v ->
         begin match self#expr scx { dw with core = Opaque v } with
         | { core = Ix n } -> [{dw with core = Dx n}]
         | _ ->
            Errors.warn ~at:dw "Ignored unexpandable identifier %S in BY DEF."
                        v;
            []
         end
      | Dx n -> [{dw with core = Dx n}]
    in
    { facts = List.map (self#expr scx) us.facts ;
      defs = List.flatten (List.map usdef us.defs);
    }

end

class virtual ['hyp] iter = object (self : 'self)
  inherit ['hyp] Expr.Visit.iter

  method proof scx pf = match pf.core with
    | Obvious | Omitted _ | Error _ -> ()
    | By (us, onl) ->
        self#usable scx us
    | Steps (inits, qed) ->
        let scx = self#steps scx inits in
        self#proof scx (get_qed_proof qed)

  method steps scx = function
    | [] -> scx
    | st :: sts ->
        let scx = self#step scx st in
        let scx = self#steps scx sts in
        scx

  method step scx st =
    let stepnm = string_of_stepno (Property.get st Props.step) in
    let adj_step scx =
      Expr.Visit.adj scx (Defn (Operator (stepnm @@ st, dummy) @@ st, Proof
      Always, Visible, Local) @@ st)
    in
    match st.core with
      | Forget k ->
          scx
      | Hide us ->
          self#usable scx us ;
          scx
      | Use (us, onl) ->
          self#usable scx us ;
          bump scx (List.length us.facts)
      | Define dfs ->
          self#defns scx dfs
      | Assert (sq, prf) ->
          ignore (self#sequent scx sq) ;
          let () =
            let scx = Expr.Visit.adjs scx (Deque.to_list sq.context) in
            let scx = bump scx 1 in
            let scx = adj_step scx in
            let scx = bump scx 1 in
            self#proof scx prf
          in
          let scx = adj_step scx in
          bump scx 1
      | Pcase (e, prf) ->
          self#expr scx e ;
          let () =
            let scx = bump scx 2 in
            let scx = adj_step scx in
            let scx = bump scx 1 in
            self#proof scx prf
          in
          let scx = adj_step scx in
          bump scx 1
      | Suffices (sq, prf) ->
          ignore (self#sequent scx sq) ;
          let () =
            let scx = adj_step scx in
            let scx = bump scx 1 in
            self#proof scx prf
          in
          let scx = Expr.Visit.adjs scx (Deque.to_list sq.context) in
          let scx = bump scx 1 in
          let scx = adj_step scx in
          bump scx 1
      | Have e ->
          self#expr scx e ;
          let scx = bump scx 2 in
          let scx = adj_step scx in
          bump scx 1
      | Take bs ->
          let scx = self#bounds scx bs in
          let scx = bump scx 1 in
          let scx = adj_step scx in
          bump scx 1
      | Witness es ->
          List.iter (self#expr scx) es ;
          let scx = bump scx 1 in
          let scx = adj_step scx in
          bump scx 1
      | Pick (bs, e, prf) ->
          self#proof scx prf ;
          let () =
            let scx = self#bounds scx bs in
            self#expr scx e in
          let scx = adj_step scx in
          let scx = bump scx 1 in
          let scx = List.fold_left begin
            fun scx (v, k, _) ->
              Expr.Visit.adj scx (Fresh (v, Shape_expr, k, Unbounded) @@ v)
          end scx bs in
          bump scx 4

  method usable scx us  =
    let usdef dw = match dw.core with
      | Dvar v ->
          self#expr scx (Opaque v @@ dw)
      | Dx n ->
          ()
    in
    List.iter (self#expr scx) us.facts ;
    List.iter usdef us.defs

end


let bump1 scx = bump scx 1
let bump2 scx = bump scx 2
let bump3 scx = bump scx 3
let bump4 scx = bump scx 4


let format_qed proof =
    "{\"QED\": " ^ proof ^ "}"


class virtual ['hyp] json_map =
    object (self: 'self)
    inherit ['hyp] Expr.Visit.json_map

    method proof scx pf = match pf.core with
        | Obvious ->
            "{\"BY\": \"OBVIOUS\"}"
        | Omitted _ ->
            "{\"BY\": \"OMITTED\"}"
        | By (usables, only) ->
            let usables = self#usable
                scx usables in
            let only = string_of_bool only in
            ("{\"BY\": {" ^
                "\"Usables\": " ^
                    usables ^ ", " ^
                "\"ONLY\": " ^ only ^
            "}}")
        | Steps ([], qed) ->
            let qed_proof = self#proof
                scx (get_qed_proof qed) in
            let qed_json = format_qed
                qed_proof in
            ("{\"Steps\": [" ^
                qed_json ^
            "]}")
        | Steps (inits, qed) ->
            let scx, inits = self#steps
                scx inits in
            let qed_proof = self#proof
                scx (get_qed_proof qed) in
            let qed_json = format_qed
                qed_proof in
            ("{\"Steps\": [" ^
                inits ^ ", " ^
                qed_json ^ "]")
        | Error _ ->
            assert false

    method steps scx = function
        | [] -> (scx, "")
        | step :: rest ->
            let scx, step = self#step
                scx step in
            let scx, rest = self#steps
                scx rest in
            let steps =
                step ^ ", " ^ rest in
            (scx, steps)

    method step scx step_ =
        let stepnm = string_of_stepno
            (Property.get step_ Props.step) in
        let adj_step scx =
          Expr.Visit.adj
            scx (
                Defn (
                    Operator (
                            stepnm @@ step_, dummy)
                        @@ step_,
                    Proof
                    Always,
                    Visible,
                    Local) @@ step_) in
        match step_.core with
        | Forget k ->
            let k = string_of_int k in
            let json =
                "{\"FORGET\": " ^ k ^ "}" in
            (scx, json)
        | Hide usables ->
            let usables = self#usable
                scx usables in
            let hide = (
                "{\"HIDE\": " ^ usables ^ "}") in
            (scx, hide)
        | Use (usables, only) ->
            let n_facts = List.length
                usables.facts in
            let usables = self#usable
                scx usables in
            let scx = bump scx n_facts in
            let use = (
                "{\"USE\": " ^ usables ^ "}") in
            (scx, use)
        | Define defs ->
            let (scx, defs) = self#defns scx defs in
            (scx, defs)
        | Assert (sq, proof) ->
            let sq_json = self#sequent scx sq in
            let proof =
                let scx = scx
                    (* assumptions *)
                    |> fun scx ->
                        Expr.Visit.adjs
                        scx (Deque.to_list sq.context)
                    (* negation of old goal *)
                    |> bump1
                    (* tuplified form of assertion *)
                    |> adj_step
                    (* hidden assertion that
                    the tuple is true *)
                    |> bump1 in
                self#proof scx proof in
            let assertion = (
                "{\"Assert\": {" ^
                    "\"SEQUENT\": " ^ sq_json ^ ", " ^
                    "\"PROOF\": " ^ proof ^
                "}}") in
            let scx = scx
                (* step name defn. *)
                |> adj_step
                (* fact that it is true *)
                |> bump1 in
            (scx, assertion)
        | Pcase (expr, proof) ->
            let expr = self#expr scx expr in
            let proof =
                let scx = scx
                    (* negation of old goal +
                    new assumption *)
                    |> bump2
                    (* assertion *)
                    |> adj_step
                    (* hidden assertion that
                    the tuple is true *)
                    |> bump1 in
                self#proof scx proof in
            let pcase = (
                "{\"PROOF_CASE\": {" ^
                    "\"Expr\": " ^ expr ^ ", " ^
                    "\"PROOF\": " ^ proof ^
                "}}") in
            (* update context *)
            let scx = scx
                (* step name defn *)
                |> adj_step
                (* fact that it is true *)
                |> fun x -> bump1 x in
            (scx, pcase)
        | Suffices (sq, proof) ->
            let sq_json = self#sequent
                scx sq in
            let proof =
                let scx = scx
                    (* step name definition *)
                    |> adj_step
                    (* step name fact *)
                    |> bump1 in
                self#proof scx proof in
            let suffices = (
                "{\"SUFFICES\": {" ^
                    "\"Sequent\": " ^ sq_json ^ ", " ^
                    "\"PROOF\": " ^ proof ^
                "}}") in
            let scx = scx
                (* assumptions *)
                |> fun scx ->
                    Expr.Visit.adjs
                    scx (Deque.to_list sq.context)
                (* negation of old goal *)
                |> bump1
                (* tuplified form of assertion *)
                |> adj_step
                (* hidden assertion that
                the tuple is true *)
                |> bump1 in
            (scx, suffices)
        | Have expr ->
            let expr = self#expr scx expr in
            let have = (
                "{\"HAVE\": " ^ expr ^ "}") in
            let scx = scx
                (* new assumption +
                negation of old goal *)
                |> bump2
                (* tuplified form of assertion *)
                |> adj_step
                (* hidden assertion that
                the tuple is true *)
                |> bump1 in
            (scx, have)
        | Take bounds ->
            (* new declarations *)
            let (scx, bounds) = self#bounds
                scx bounds in
            let take = (
                "{\"TAKE\": " ^ bounds ^ "}") in
            let scx =
                scx
                (* negation of old goal *)
                |> bump1
                (* tuplified form of assertion *)
                |> adj_step
                (* hidden assertion that
                the tuple is true *)
                |> bump1 in
            (scx, take)
        | Witness exprs ->
            let exprs = List.map
                (self#expr scx) exprs in
            let exprs = Fmtutil.comma exprs in
            let witness = (
                "{\"WITNESS\": " ^ exprs ^ "}") in
            let scx = scx
                (* no new assumptions *)
                (* negation of old goal *)
                |> bump1
                (* tuplified form of assumption *)
                |> adj_step
                (* hidden assertion that
                the tuple is true *)
                |> bump1 in
            (scx, witness)
        | Pick (bounds, expr, proof) ->
            let proof = self#proof
                (bump3 scx) proof in
            let (bounds_json, expr) =
                let (scx, bounds_json) = self#bounds
                    scx bounds in
                let expr = self#expr scx expr in
                (bounds_json, expr) in
            let pick = (
                "{\"PICK\": {" ^
                    "\"Bounds\": " ^ bounds_json ^
                        ", " ^
                    "\"Expr\": " ^ expr ^
                        ", " ^
                    "\"PROOF\": " ^ proof ^
                "}}") in
            let hyps = Expr.Visit.hyps_of_bounds
                bounds in
            let scx = scx
                (* equivalent existential
                for subexprs *)
                |> adj_step
                (* fact that it is true *)
                |> bump1
                (* there is a SUFFICES here
                ... so add assumptions for
                the new identifiers *)
                |> fun scx ->
                    Expr.Visit.adjs scx hyps
                (*
                ... then add assumption about
                    the body of the `PICK`
                ... then add the negation of
                    the old goal
                ... then the step name definition
                    for the `SUFFICES`
                ... then the conjunction of the
                    nondom facts in the `SUFFICES`
                *)
                |> bump4 in
            (* finally, we are in the next step *)
            (scx, pick)

    method usable ((_, cx) as scx) usables =
        let facts = usables.facts
            |> List.map (self#expr scx)
            |> Fmtutil.comma in
        let mapper def =
            match def.core with
            | Dvar v -> v
            | Dx n ->
                let hyp = Expr.T.get_val_from_id cx n in
                begin match hyp.core with
                | Flex name -> name.core
                | Fresh (name, _, _, _) -> name.core
                | Defn (defn, _, _, _) ->
                    begin match defn.core with
                    | Recursive (name, _)
                    | Operator (name, _)
                    | Instance (name, _)
                    | Bpragma (name, _, _) ->
                        name.core
                    end
                | Fact (expr, _, _) ->
                    let scx = Expr.T.scx_front scx n in
                    self#expr scx expr
                end in
        let defs = usables.defs
            |> List.map mapper
            |> Fmtutil.comma in
        ("{\"Facts\": [" ^ facts ^ "], " ^
         "\"DEF\": [" ^ defs ^ "]}")
end
