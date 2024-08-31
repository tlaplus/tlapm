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
          let rec simplify f x =
            match x with
            | [[tr], bod] -> { e with core = Except (f, [[tr], self#expr scx bod]) }
            | [tr :: trs, bod] ->
                let g = match tr with
                  | Except_dot x -> { f with core = Dot (f, x) }
                  | Except_apply e -> { f with core = FcnApp (f, [self#expr scx e]) }
                in
                { e with core = Except (f, [[tr], simplify g [trs, self#expr scx bod]]) }
            | x :: xs ->
                let ex = simplify f [x] in
                simplify ex xs
(*
                let exs = simplify ex xs in
                begin match exs.core with
                  | Except (f, xs) ->
                      { ex with core = Except (f, xs) }
                  | _ ->
                      Errors.bug ~at:ex "Expr.Elab.desugar: simplify/except/1"
                end
*)
            | _ ->
                Errors.bug ~at:f "Expr.Elab.desugar: simplify/except/2"
          in
          let f = self#expr scx f in
          let xs = List.map (self#exspec scx) xs in
          simplify f xs
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
  let e = if nte then except_normalize scx e else e in
  let e = let_normalize scx e in
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
