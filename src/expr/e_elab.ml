(* Expression elaborater.

Copyright (C) 2008-2010  INRIA and Microsoft Corporation
*)
open Property

module B = Builtin

open E_t
open E_subst

module Visit = E_visit
module Constness = E_constness
module Fmt = E_fmt


let current_at = ref None

let desugar self_expr super_expr scx e =
  match e.core with
  | At true ->
    begin match !current_at with
    | Some (e, dep) ->
      let shf = Deque.size (snd scx) - dep in
      if shf = 0 then e else app_expr (shift shf) e
    | None -> e
    end
  | Except (f, xs) ->
    let f = self_expr scx f in
    List.fold_left begin
      fun f (trail, bod) ->
        let (trail, at) =
          List.fold_left begin
            fun (trail, f) ex ->
              match ex with
              | Except_dot x ->
                (Except_dot x :: trail, {f with core = Dot (f, x)})
              | Except_apply k ->
                let k = self_expr scx k in
                (Except_apply k :: trail, {f with core = FcnApp (f, [k])})
          end ([], f) trail
        in
        let at_save = !current_at in
        current_at := Some (at, Deque.size (snd scx));
        let bod = self_expr scx bod in
        current_at := at_save;
        {e with core = Except (f, [(List.rev trail, bod)])}
    end f xs
  | _ -> super_expr scx e

let non_temporal =
  let visitor = object (self : 'self)
    inherit [bool ref] Visit.iter as super
    method hyp (good, _ as scx) h = match h.core with
      | Defn (_, _, Hidden, _)
      | Fact (_, Hidden,_) -> scx
      | _ -> super#hyp scx h
    method expr (good, _ as scx) oe = match oe.core with
      | ( Apply ({core = Internal (B.Box _ | B.Diamond | B.Actplus |
            B.Leadsto | B.Cdot
            )}, _)
        | Tsub _ | Fair _
        ) ->
          good := false
      | _ ->
          super#expr scx oe
  end in
  fun e ->
    let good = ref true in
    visitor#expr (good, Deque.empty) e ;
    !good

let rec box e = match e.core with
  | Sequent sq ->
      Sequent { sq with active = box sq.active } @@ e
  | _ ->
      if non_temporal e then
        Apply (Internal (Builtin.Box false) @@ e, [e]) @@ e
      else e

let fake_box =
  let visitor = object (self : 'self)
    inherit [unit] Visit.map as super
    method sequent scx sq =
      if non_temporal sq.active then
        super#sequent scx sq
      else  (*begin Errors.set sq.active ("TLAPM does not handle yet temporal logic");failwith "temporal logic" end*)
        let sqcx = Deque.map begin
          fun _ h -> match h.core with
            | Fact (f, Visible, tm) ->
                Fact (box f, Visible, tm) @@ f
            | _ ->
                h
        end sq.context in
          super#sequent scx { sq with context = sqcx }
  end in
  fun e -> visitor#expr ((), Deque.empty) e

let except_normalize =
  let visitor = object (self : 'self)
    inherit [unit] Visit.map as super

    method expr scx e = match e.core with
      | Except (f, xs) ->
          (* Fold [f EXCEPT p1 = b1, ...] into [f] left-to-right, materialising
             each shared prefix once, to avoid the multiplicative blow-up of the
             naive desugaring (test/regression_tests/
             record_except_explosion_test.tla).  Soundness of each reduction --
             fold into a record constructor only on an existing field (its
             DOMAIN), never push a selection/update through IF, group only
             *adjacent* same-prefix updates and only on provably equal keys
             (so opaque/CONSTANT keys are never merged or reordered) -- is
             pinned by the [let%test_module] below.  Precondition: [@]/[At] are
             already resolved by [Elab.desugar]. *)
          let access b hd =
            match hd with
            | Except_dot x -> { b with core = Dot (b, x) }
            | Except_apply k -> { b with core = FcnApp (b, [k]) }
          in
          let head_eq a b =
            match a, b with
            | Except_dot x, Except_dot y -> x = y
            | Except_apply e1, Except_apply e2 -> E_eq.expr e1 e2
            | _, _ -> false
          in
          let sel r hd =
            match r.core, hd with
            | Record fs, (Except_dot h | Except_apply {core = String h})
              when List.mem_assoc h fs -> List.assoc h fs
            | _ -> access r hd
          in
          let set b hd v =
            match b.core, hd with
            | Record fs, (Except_dot h | Except_apply {core = String h})
              when List.mem_assoc h fs ->
                { b with core =
                    Record (List.map (fun (k, x) -> if k = h then (k, v) else (k, x)) fs) }
            | _ -> { e with core = Except (b, [[hd], v]) }
          in
          let rec apply base subs =
            match subs with
            | [] -> base
            | ([], bod) :: rest ->
                apply bod rest
            | (tr, _) :: _ ->
                let hd = List.hd tr in
                let same t = match t with h :: _ -> head_eq h hd | [] -> false in
                let rec span acc = function
                  | (t, b) :: tl when same t -> span ((List.tl t, b) :: acc) tl
                  | rest -> (List.rev acc, rest)
                in
                let subtails, rest = span [] subs in
                let v = apply (sel base hd) subtails in
                apply (set base hd v) rest
          in
          let f = self#expr scx f in
          let xs = List.map (self#exspec scx) xs in
          apply f xs
      (* No top-level "collapse a selection over a record constructor" case:
         that rewrite is equality-preserving but NOT proof-stable -- it would
         collapse a hand-cited fact like [m2b.acc = self] to [self = self] and
         drop it, erasing a term a backend needs (regressed
         examples/ByzPaxos/BPConProof.tla).  It is also unnecessary: the fold
         above already collapses every selection EXCEPT desugaring itself
         produces.  See "a field selection over a record constructor is left
         intact" in the [let%test_module] below. *)
      | _ -> super#expr scx e
  end in
  fun scx e -> visitor#expr scx e

let let_normalize =
  let visitor = object (self : 'self)
    inherit [unit] Visit.map as super
    method expr scx e =
      let dest = e in
      match e.core with
        | Let ([], e) -> self#expr scx e
        | Let (d :: ds, e) -> begin
            match d.core with
              | Operator (n, nexp)
              | Bpragma (n, nexp, _) ->
                  let op = self#expr scx nexp in
                  let e = Let (ds, e) @@ dest in
                  let e = app_expr (scons op (shift 0)) e in
                  self#expr scx e
              | Instance (name, _) ->
                  Errors.bug ~at:d (
                      "Found INSTANCE in Expr.Elab.let_normalize, " ^
                      "all INSTANCE statements have been replaced " ^
                      "with definitions in Module.Elab ")
              | _ ->
                  Errors.bug ~at:d "Expr.Elab.let_normalize"
          end
        | _ -> super#expr scx e
  end in
  fun scx e -> visitor#expr scx e

let normalize cx e =
  let scx = ((), cx) in
  let nte = non_temporal e in
  (* moved to action frontend *)
  (* let e = if nte then action_normalize scx e else e in *)
  (* let_normalize before except_normalize: refinement mappings bind the
     updated state to LET operators, so inlining them first exposes the record
     constructors that except_normalize folds into.  With the opposite order
     the bases stay opaque LET variables and get re-embedded (and then
     multiplied out) per path component. *)
  let e = let_normalize scx e in
  let e = if nte then except_normalize scx e else e in
  (* moved to action frontend *)
  (* let e = if nte then unchanged_normalize scx e else e in
  let e = prime_normalize cx e in
  let e = fake_box e in
  let e = if nte then e else strong_prime e in *)
  e

let get_at e =
let error () =
(*  Errors.set e "the top-level operator of this expression is not an infix operator hence you cannot use @ reference in the next proof-step";*)
  (*Util.eprintf ~at:e "the top-level operator of this expression is not an infix operator hence you cannot use @ reference in the next proof-step";*)
  failwith "Expr.Elab.get_at"
in
  match e.core with
    | Apply (e,l) ->
        if List.length l <> 2
        then error ()
        else List.nth l 1
  | _ -> error ()


let will_replace : expr_ option ref = ref None

let replace_at_aux =
   let visitor = object (self : 'self)
    inherit [unit] Visit.map as super
    method expr scx e =
      match e.core with
        | At false -> (match !will_replace with Some c -> c | _ -> assert false) @@ e
        | _ -> super#expr scx e
  end in
  fun scx e -> visitor#expr scx e

let replace_at scx e r =
  will_replace := Some r.core;
  let res = replace_at_aux scx e in
  will_replace := None; res


let%test_module _ = (module struct
  let sexp_of_string = Sexplib.Std.sexp_of_string
  let compare_string = Base.compare_string

  let parse_expr = Tla_parser.P.use (E_parser.expr true)
  let nullctx = (Deque.empty, Ctx.dot)

  let create_expression str =
    let (flex, _) = Alexer.lex_string str in
    match Tla_parser.P.run parse_expr ~init:Tla_parser.init ~source:flex with
      | Some e -> e
      | None -> failwith "cannot parse test string"

  let prn_exp exp =
    Tla_parser.Fu.pp_print_minimal
    Format.str_formatter (E_fmt.fmt_expr nullctx exp);
    Format.flush_str_formatter ()

  let prn_str str = str

  let%test_unit "test_case_1" =
    let (flex, _) = Alexer.lex_string "[f EXCEPT ![0] = 0, ![1] = 1][0] = f[0]" in
      match Tla_parser.P.run parse_expr ~init:Tla_parser.init ~source:flex with
      | Some e -> ()
      | None -> failwith "cannot parse test string"

  let%test_unit "t1" =
    let test_case = create_expression "[f EXCEPT ![0] = 0, ![1] = 1]" in
    let target_case = create_expression "[[f EXCEPT ![0] = 0] EXCEPT ![1] = 1]" in
      [%test_eq: string] (prn_exp target_case) (prn_exp (normalize Deque.empty test_case))

  let%test_unit "t2" =
    (* Only *adjacent* same-prefix updates are grouped, so the two updates to
       key [0] are not merged and left-to-right order is preserved.  Keys are
       compared by provable equality only, so opaque/CONSTANT keys are never
       assumed equal and hence never merged or reordered. *)
    let test_case = create_expression "[[f EXCEPT ![0] = 10, ![1] = 1] EXCEPT ![0] = 0]" in
    let target_case = create_expression "[[[f EXCEPT ![0] = 10] EXCEPT ![1] = 1] EXCEPT ![0] = 0]" in
      [%test_eq: string] (prn_exp target_case) (prn_exp (normalize Deque.empty test_case))

  let%test_unit "t3" =
    let test_case = create_expression "[f EXCEPT ![0] = ([f EXCEPT ![0] = 1, ![1] = 0][1])]" in
    let target_case = create_expression "[f EXCEPT ![0] = ([[f EXCEPT ![0] = 1] EXCEPT ![1] = 0][1])]" in
      [%test_eq: string] (prn_exp target_case) (prn_exp (normalize Deque.empty test_case))

  let%test_unit "t4" =
    let test_case = create_expression "[f EXCEPT ![([f EXCEPT ![0] = 1, ![1] = 0][1])] = 2]" in
    let target_case = create_expression "[f EXCEPT ![([[f EXCEPT ![0] = 1] EXCEPT ![1] = 0][1])] = 2]" in
      [%test_eq: string] (prn_exp target_case) (prn_exp (normalize Deque.empty test_case))

  let%test_unit "t5" =
    let test_case = create_expression "[f EXCEPT !.a = 3, !.b = 2, !.c = 1]" in
    let target_case = create_expression "[[[f EXCEPT !.a = 3] EXCEPT !.b = 2] EXCEPT !.c = 1]" in
      [%test_eq: string] (prn_exp target_case) (prn_exp (normalize Deque.empty test_case))

  let%test_unit "t6" =
    let test_string = "[[arr EXCEPT ![x][y] = foo] EXCEPT ![u][v] = bar]" in
    let test_case = create_expression test_string in
    let target_case = create_expression
      "[[arr EXCEPT ![x] = [arr[x] EXCEPT ![y] = foo]] EXCEPT ![u] = \
      [[arr EXCEPT ![x] = [arr[x] EXCEPT ![y] = foo]][u] EXCEPT ![v] = bar]]" in
        [%test_eq: string] (prn_exp target_case) (prn_exp (normalize Deque.empty test_case))

  let%test_unit "except does not add a record field" =
    (* EXCEPT preserves the domain of its base function.  Since [b] is not in
       the domain of this record, selecting [.b] cannot be reduced to the
       replacement value. *)
    let test_case =
      create_expression "[[a |-> 1] EXCEPT !.b = 2].b"
    in
    let target_case =
      create_expression "[[a |-> 1] EXCEPT !.b = 2].b"
    in
    [%test_eq: string]
      (prn_exp target_case)
      (prn_exp (normalize Deque.empty test_case))

  let%test_unit "projection does not distribute through a non-Boolean IF" =
    (* TLA+ is untyped.  IF is guaranteed to select a branch only when its
       condition is Boolean, so this projection cannot be distributed without
       first establishing that condition. *)
    let conditional =
      create_expression "IF 0 THEN [a |-> 1] ELSE [a |-> 2]"
    in
    (* Parentheses are retained explicitly by the parser and would hide the
       [If] node from this normalization rule, so construct the projection AST
       directly. *)
    let test_case = Dot (conditional, "a") @@ conditional in
    let target_case = Dot (conditional, "a") @@ conditional in
    [%test_eq: string]
      (prn_exp target_case)
      (prn_exp (normalize Deque.empty test_case))

  let%test_unit "matching EXCEPT over an opaque base needs field membership" =
    (* Unlike a record literal, an opaque base has an unknown domain.
       [r EXCEPT !.b = 2].b] equals 2 only when [b \in DOMAIN r], which cannot
       be assumed here, so the selection must not be reduced to 2. *)
    let test_case = create_expression "[r EXCEPT !.b = 2].b" in
    let target_case = create_expression "[r EXCEPT !.b = 2].b" in
    [%test_eq: string]
      (prn_exp target_case)
      (prn_exp (normalize Deque.empty test_case))

  let%test_unit "nonmatching EXCEPT over an opaque base is not the base selection" =
    (* [[r EXCEPT !.a = 2].b] is not provably [r.b]: when [b \notin DOMAIN r]
       both sides are unspecified but need not be the same unspecified value
       (their function arguments differ).  With an opaque, unknown-domain base
       this reduction is therefore unsound. *)
    let test_case = create_expression "[r EXCEPT !.a = 2].b" in
    let target_case = create_expression "[r EXCEPT !.a = 2].b" in
    [%test_eq: string]
      (prn_exp target_case)
      (prn_exp (normalize Deque.empty test_case))

  let%test_unit "projection does not distribute through an unknown-condition IF" =
    (* Even when the condition is not a manifest non-Boolean, its Boolean-ness
       is unknown for an opaque [p]; distributing the projection over the
       branches is unsound unless [p \in BOOLEAN] has been established. *)
    let conditional =
      create_expression "IF p THEN [a |-> 1] ELSE [a |-> 2]"
    in
    let test_case = Dot (conditional, "a") @@ conditional in
    let target_case = Dot (conditional, "a") @@ conditional in
    [%test_eq: string]
      (prn_exp target_case)
      (prn_exp (normalize Deque.empty test_case))

  (* Positive counterparts of the guard tests above.  The blow-up in
     test/regression_tests/record_except_explosion_test.tla is defused by
     *folding* EXCEPT updates into the record constructor they update, so a wide
     base is materialised once instead of being re-embedded per path component
     -- NOT by collapsing field selections.  We deliberately do not collapse
     selections (see the note in [except_normalize]): that is equality-
     preserving but not proof-stable. *)

  let%test_unit "EXCEPT over a record constructor folds the update in place" =
    (* [b \in DOMAIN [a |-> 1, b |-> 2]], so the update is folded into the
       constructor, keeping the result linear in the record's width. *)
    let test_case = create_expression "[[a |-> 1, b |-> 2] EXCEPT !.b = 3]" in
    let target_case = create_expression "[a |-> 1, b |-> 3]" in
    [%test_eq: string]
      (prn_exp target_case)
      (prn_exp (normalize Deque.empty test_case))

  let%test_unit "multiple EXCEPT updates fold into a single constructor" =
    let test_case =
      create_expression "[[a |-> 1, b |-> 2] EXCEPT !.a = 3, !.b = 4]"
    in
    let target_case = create_expression "[a |-> 3, b |-> 4]" in
    [%test_eq: string]
      (prn_exp target_case)
      (prn_exp (normalize Deque.empty test_case))

  let%test_unit "a field selection over a record constructor is left intact" =
    (* Proof-stability: even though [[a |-> 1, b |-> 2].b = 2] is provable, we
       must not rewrite it, since the same collapse applied to a hand-cited fact
       (e.g. [m2b.acc = self]) erases the term a backend needs.  Folding keeps
       the obligation linear without touching the selection. *)
    let test_case = create_expression "[a |-> 1, b |-> 2].b" in
    let target_case = create_expression "[a |-> 1, b |-> 2].b" in
    [%test_eq: string]
      (prn_exp target_case)
      (prn_exp (normalize Deque.empty test_case))

  (*
  let%test_unit "t7" [@tags "disabled"] = (* doesnt work because we need to anonimie the created expressions from the parser*)
    let test_string = "f[x]'" in
    let test_case = create_expression test_string in
    let target_case = create_expression "f'[x']" in
    (* let x = normalize Deque.empty test_case in
       Printf.eprintf "compare: %d\n" (Stdlib.compare x target_case); *)
      [%test_eq: string] (prn_exp target_case) (prn_exp (normalize Deque.empty test_case))
  *)

end)
