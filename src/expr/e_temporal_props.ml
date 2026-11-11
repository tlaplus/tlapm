(* Functions for checking temporal properties.

Copyright (C) 2013  INRIA and Microsoft Corporation
*)
open Property
open Ext
open E_t
open E_visit

module B = Builtin


let visitor = object (self : 'self)
  inherit [bool ref * bool] iter as super

  method expr ((closure, is_box), cx as scx) oe =
    if (!closure = false) then ()
    else match oe.core with
    (* constant expressions are closed *)
    (* temporal declarations are closed as well *)
    | _ when (E_constness.is_const oe) -> () (* closed if constant *)
    (* is_const is missing on some constant symbols like equality *)
    | Internal(B.Eq | B.Neq | B.UNCHANGED) -> () (* should be is_const but is not *)
    (* propositions - TRUE/FALSE  *)
    | Internal (B.TRUE | B.FALSE) -> ()
    (* unary closed operators *)
    | Apply ({core = Internal (B.Box _)}, _) when is_box -> ()
    | Apply ({core = Internal B.Diamond}, _) when (not is_box) -> ()
    (* unary operators *)
    | Apply ({core = Internal ((B.Box _) | B.Diamond | B.Prime)}, [e]) -> self#expr scx e
    | Apply ({core = Internal B.Neg}, [e]) -> self#expr ((closure, not is_box),
    cx) e
    (* binary operators *)
    | Apply ({core = Internal ((B.Conj | B.Disj | B.Implies) as tp)}, [e1;e2]) ->
        let closure1 = ref !closure in
        let closure2 = ref !closure in
        let () = match tp with
        | B.Conj | B.Disj -> self#expr ((closure1, is_box), cx) e1; self#expr ((closure2, is_box), cx) e2
        | B.Implies -> self#expr ((closure1, not is_box), cx) e1; self#expr ((closure2, is_box), cx) e2
        | _ -> assert false
        in
        closure := !closure1 && !closure2
    | Apply ({core = Internal B.Equiv}, [e1;e2]) ->
        let closure1 = ref !closure in
        let closure2 = ref !closure in
        let closure3 = ref !closure in
        let closure4 = ref !closure in
        let () = self#expr ((closure1, not is_box), cx) e1; self#expr ((closure2,
        is_box), cx) e2; self#expr ((closure3, is_box), cx) e1; self#expr
        ((closure4, not is_box), cx) e2
        in
        closure := !closure1 && !closure2 && !closure3 && !closure4
    (* lists *)
    | List (_, ls) ->
        let cls = ref !closure in
        let f e = let () = self#expr ((cls, is_box), cx) e in
        !cls in
        closure := (List.for_all f ls)
    (* decomposing formulas for confirming all are constants *)
    | Apply _ ->
        super#expr scx oe
    (* sequents should be converted to implications for computing is_box *)
    | Sequent sq ->
        (* let closure1 = ref true in
        let closure2 = ref true in
        let _ = self#hyps ((closure1, not is_box), cx) sq.context in
        let () = self#expr ((closure2, is_box), cx) sq.active in
        closure := !closure1 && !closure2 *)
        self#expr ((closure, is_box), cx) sq.active
    (* unexpended temporal operators *)
    | f ->
        closure := false
end

let box_closure cx e =
  let good = ref true in
  visitor#expr ((good,true), cx) e ;
  !good

let diamond_closure cx e =
  let good = ref true in
  visitor#expr ((good,false), cx) e ;
  !good


(* we should generate box-level here using a expr-visitor and replacing
 * facts (with the known cost of duplicating the context for each
 * sequent. The steps are as follows:
   * 1) if it already has a level (i.e. theorem and axioms get a box level
   * without regard to the sequent in the fact) then we do nothing
   * 2) if the fact is a formula, then we apply Leslie’s algorithm to
   * decide its level.
   * 3) if the fact is a sequent, if all (visible) assumptions are
   * box-level, then the fact is box-level.
*)

let compute_time scx e =
  let e =
    let visitor = object (self: 'self)
      inherit E_constness.const_visitor
    end
    in
    visitor#expr ((), scx) e in
  let e = E_tla_norm.expand_unchanged ((),scx) e in
  let e = E_tla_norm.expand_action ((),scx) e in
  let e = E_tla_norm.expand_fairness ((),scx) e in
  let e = E_tla_norm.expand_leadsto ((),scx) e in
  match e.core with
| _ -> match box_closure scx e with
  | true -> Always
  | _ -> Now

let check_time_change ctx tm = match tm with
| Now -> Now
| Always -> Deque.fold_left begin
  fun acc a -> match a.core with
  | Fact(_,_,Now) -> Now
  | _ -> acc
  end Always ctx
| _ -> failwith "error"

let%test_module "compute_time" = (module struct
  (* Resolve variable names to indices before classifying the sequent.
     E_anon itself calls compute_time, so it cannot be used here. *)
  let resolve_variables = object
    inherit [unit] E_visit.map as super

    method expr ((_, cx) as scx) e =
      match e.core with
      | Opaque name ->
          let declares_name h =
            match h.core with
            | Flex v -> v.core = name
            | _ -> false
          in
          begin match Deque.find ~backwards:true cx declares_name with
          | Some (i, _) -> Ix (i + 1) @@ e
          | None -> failwith ("Undeclared test variable: " ^ name)
          end
      | _ -> super#expr scx e
  end

  let classify ?(variables = []) input =
    let open Tla_parser in
    let source, _ = Alexer.lex_string input in
    let parse_sequent = locate (P.use (E_parser.sequent true)) in
    match P.run parse_sequent ~init:Tla_parser.init ~source with
    | Some sq ->
        let cx = Deque.of_list (List.map (fun name -> Flex (name @@ sq) @@ sq) variables) in
        let e = resolve_variables#expr ((), cx) (Sequent sq.core @@ sq) in
        compute_time cx e
    | None -> failwith ("Cannot parse test sequent: " ^ input)

  let%test "state assumption with constant conclusion is Now" [@tags "disabled"] =
    classify "ASSUME NEW VARIABLE x, x = 0 PROVE FALSE" = Now

  let%test "diamond assumption with boxed conclusion is Always" =
    classify "ASSUME NEW VARIABLE x, NEW VARIABLE y, <>(x = 0) PROVE [](y = 0)"
    = Always

  let%test "boxed assumption with boxed conclusion is Now" [@tags "disabled"] =
    classify "ASSUME NEW VARIABLE x, NEW VARIABLE y, [](x = 0) PROVE [](y = 0)"
    = Now

  let%test "diamond assumption with state conclusion is Now" =
    classify "ASSUME NEW VARIABLE x, <>(x = 0) PROVE x = 1" = Now

  let%test "a later assumption that is not diamond-closed makes the sequent Now" [@tags "disabled"] =
    classify "ASSUME NEW VARIABLE x, <>(x = 0), x = 1 PROVE FALSE" = Now

  (* Supply the fixtures' module-level VARIABLES x, y as outer context
     so the inner sequents can be tested verbatim. *)
  let%test "box_closure_sequent_multiple_assumptions_stest" [@tags "disabled"] =
    classify ~variables:["x"; "y"] "ASSUME x = 0, y = 1 PROVE [](x = y)" = Now

  let%test "box_closure_sequent_false_conclusion_stest" [@tags "disabled"] =
    classify ~variables:["x"] "ASSUME x = 0 PROVE FALSE" = Now

  let%test "box_closure_sequent_boxed_assumption_stest" [@tags "disabled"] =
    classify ~variables:["x"; "y"] "ASSUME [](x = 0) PROVE [](y = 0)" = Now

  let%test "multiple assumptions with NEW VARIABLE declarations are Now" [@tags "disabled"] =
    classify
      "ASSUME NEW VARIABLE x, NEW VARIABLE y, x = 0, y = 1 PROVE [](x = y)"
    = Now

  let%test "false conclusion with NEW VARIABLE declarations is Now" [@tags "disabled"] =
    classify "ASSUME NEW VARIABLE x, x = 0 PROVE FALSE" = Now
end)
