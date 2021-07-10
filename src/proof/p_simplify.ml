(*
 * proof/simplify.ml --- simplify proofs
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

open Ext
open Property

open Expr.T
open Expr.Subst

open P_t

let at_nowhere = At false @@ nowhere

let hyps_of bs =
  let hyps = Expr.Visit.hyps_of_bounds_unditto bs in
  Deque.of_list hyps

(* the following at_expand function is not efficient because it reparses the proof tree *)
exception Gac

let get_assert_active step =
  match step.core with
    | Assert (s,_) -> s.active
    | _ -> raise Gac

let replace_in_core step f =
  match step.core with
    | Assert (s,p) ->
        let newcore = (f s.active).core in
        let s = {s with active = (newcore @@ s.active)} in
              Assert(s,p) @@ step
    | _ -> raise Gac

let empty = ((),Deque.empty)

let rec replace_at l prev prf =
  match l with
    | [] -> List.rev prev
    | st::ll ->
        let replaced = begin
          try (replace_in_core st (fun e -> Expr.Elab.replace_at empty e (Expr.Subst.app_expr (shift 2) (Expr.Elab.get_at (get_assert_active (List.hd prev))))))
                   (* shift 2 comes from the fact that both the previous proof-step and the negation of the current proof-step have been added to the context *)
          with _ -> st end
        in replace_at ll (replaced::prev) prf


let at_expand prf =
  match prf.core with
    | Obvious | Omitted _  | By _ | Error _ -> prf
    | Steps (inits, qed) -> (Steps ((replace_at inits [] prf), qed)) @@ prf


let rec simplify cx goal prf time_flag =
  Util.eprintf ~debug:"simpl" ~at:prf
    "simplify@.  %a@.  @[%a@]@.@."
    (Expr.Fmt.pp_print_expr (cx, Ctx.dot)) goal
    (P_fmt.pp_print_proof (cx, Ctx.dot)) prf ;

  let prf = at_expand prf in

  let sprf = match prf.core with
    | Obvious | Omitted _  | Error _ -> prf
    | By (us, onl) ->
        let use_defs =
          if us.defs = [] then [] else [
            Use ({ facts = [] ; defs = us.defs }, false) @@ prf
          ] in
        let suppress = has prf Props.supp in
        let use_facts = List.mapi begin
          fun n f ->
            let fact = app_expr (shift n) f in
            let fact = assign fact Props.use_location (Util.get_locus prf) in
            let st = Use ({facts = [fact]; defs = []}, false) @@ f in
            if suppress then assign st Props.supp () else st
        end us.facts in
        let forget =
          if onl then
            [ Forget (List.length us.facts) @@ prf ]
          else [] in
        let inits = use_defs @ use_facts @ forget in
        let qed_prf = Obvious @@ prf in
        let sn =
          match get prf Props.step with
          | Unnamed (n, _) | Named (n, _, _) -> n
        in
        let assign_number thing =
          assign thing Props.step (Named (sn, "_a" ^ string_of_int (Std.unique ()), true)) in
        let inits = List.map assign_number inits in
        let qed_prf = assign_number (qed_prf) in
          assign (Steps (inits, {core = Qed qed_prf; props = qed_prf.props}) @@ prf) Props.orig_proof prf
    | Steps (inits, qed) ->
        let (cx, goal, inits, time_flag) = simplify_steps cx goal inits
        time_flag in
        let qed_prf = simplify cx goal (get_qed_proof qed) time_flag in
        Steps (inits, {qed with core = Qed qed_prf}) @@ prf
  in
  Util.eprintf ~debug:"simpl" ~at:prf
    "simplify (result)@\n@[<hv2>%a@ --> %a@]@.@."
    (P_fmt.pp_print_proof (cx, Ctx.dot)) prf
    (P_fmt.pp_print_proof (cx, Ctx.dot)) sprf ;
  sprf

and simplify_steps cx goal inits time_flag = match inits with
  | [] -> (cx, goal, [], time_flag)
  | st :: inits ->
      let (cx, goal, st, time_flag) = simplify_step cx goal st time_flag in
      let (cx, goal, inits, time_flag) = simplify_steps cx goal inits time_flag in
      (cx, goal, st @ inits, time_flag)

and simplify_step cx goal st time_flag =
  Util.eprintf ~debug:"simpl" ~at:st
    "simplify_step@.  %a@.  @[%t@]@.@."
    (Expr.Fmt.pp_print_expr (cx, Ctx.dot)) goal
    (fun ff -> ignore (P_fmt.pp_print_step (cx, Ctx.dot) ff st)) ;
  let stepno = get st Props.step in
  (* let anonymize x = assign x Props.step (Named (step_number stepno, "_a" ^ string_of_int (Std.unique ()), true)) in *)
  let salt nacl x = assign x Props.step begin match stepno with
    | Named (sn, sl, _) -> Named (sn, sl ^ nacl ^ string_of_int (Std.unique ()), false)
    | Unnamed (sn, sx) -> Named (sn, "_a" ^ nacl ^ string_of_int (Std.unique ()), false)
  end in
  let assume ?(vis=Visible) cx _ =
    Deque.snoc cx (Fact (at_nowhere, vis, time_flag) @@ st)
  in
  let set_vis vis cx ud = match ud.core with
    | Dx n ->
        Deque.alter ~backwards:true cx (n - 1) begin
          fun h -> match h.core with
            | Defn (df, wd, _, ex) -> Defn (df, wd, vis, ex) @@ st
            | _ ->
                let hn = hyp_name h in
                  Errors.set ud ("USE DEF "^hn^" invalid because "^hn^" is not a defined operator");   (* not necessary -> already handled by SANY from the Toolbox*)
                  Util.eprintf ~at:ud
                  "USE DEF %s invalid because %s is not a defined operator\n%!"
                  hn hn ;
                failwith "Proof.Simplify.set_visibility"
        end
    | _ -> Errors.bug ~at:st "set_vis"
  in
  let disable = set_vis Hidden in
  let (scx, sgoal, sts, time_flag) = match st.core with
    | Forget _ ->
        (cx, goal, [st], time_flag)
    | Assert (sq, prf) ->
        let prf =
          let (cx, goal, time_flag1) =
            P_gen.prove_assertion ~suffices:false cx goal (sq @@ st) time_flag
          in
          simplify cx goal prf time_flag1
        in
        let st = Assert (sq, prf) @@ st in
        let (cx, goal) =
          P_gen.use_assertion ~suffices:false cx goal (sq @@ st) time_flag
        in
        (cx, goal, [st], time_flag)
    | Suffices (sq, prf) ->
        let prf =
          let (cx, goal) =
            P_gen.use_assertion ~suffices:true cx goal (sq @@ st) time_flag
          in
          simplify cx goal prf time_flag
        in
        let st = Suffices (sq, prf) @@ st in
        let (cx, goal, time_flag1) =
          P_gen.prove_assertion ~suffices:true cx goal (sq @@ st) time_flag
        in
        (cx, goal, [st], time_flag1)
    | Use (us, onl) ->
        let sts = match (simplify cx goal (By (us, onl) @@ st) time_flag).core with
          | Steps (inits, _) ->
              (* List.map (renumber_step (step_number stepno)) inits *)
              inits
          | _ ->
              Errors.bug ~at:st
                         "simplifying BY does not produce a non-leaf proof!"
        in
        let cx = List.fold_left assume cx us.facts in
        (cx, app_expr (shift (List.length us.facts)) goal, sts, time_flag)
    | Hide us ->
        let cx = List.fold_left disable cx us.defs in
        (cx, goal, [Hide us @@ st], time_flag)
    | Define dfs ->
        let cx = List.fold_left begin
          fun cx df ->
            Deque.snoc cx (Defn (df, Proof time_flag, Visible, Local) @@ st)
        end cx dfs in
        (cx, app_expr (shift (List.length dfs)) goal, [Define dfs @@ st],
        time_flag)
    | Have e ->
        let (sq, qed, time_flag) =
          match expose_connective cx goal with
          | {core = Apply ({core = Internal Builtin.Implies}, [a ; b])} ->
              let sq = {
                context = Deque.of_list [ Fact (e, Visible,
                time_flag)  @@ st ] ;
                active = app_expr (shift 1) b ;
              } in
              let qed = By ({ facts = [Ix 2 @@ st] ; defs = [] }, true) @@ st in
              (sq, qed, time_flag)
          | gl ->
              let sq = {
                context = Deque.of_list [ Fact (e, Visible,
                time_flag)  @@ st ];
                active = gl ;
              } in
              let msg =
                Util.sprintf "@.@[<v2>@[%s@ %s@]@,%a@]@."
                    "Error: this HAVE step is applied to the following goal,"
                    "which is not an implication:"
                    (Expr.Fmt.pp_print_expr (cx, Ctx.dot)) goal
              in
              (sq, Error msg @@ st, time_flag)
        in
        let st = assign st Props.orig_step st in
        let suff = Suffices (sq, qed) @@ st in
        let suff = renumber_step (step_number stepno) suff in
        (* let suff = remove suff Props.orig_step in *)
        simplify_step cx goal suff time_flag

    | Take bs ->
        let oldgoal = goal in
        let bs = expand_dittoes bs in
        let rec strip shf aux goal = function
          | [] -> (aux, goal)
          | b :: bs -> begin
              match expose_connective cx goal with
              | {core = Quant (Forall, gb :: gbs, ge)} as goal ->
                  let gbs = List.tl (expand_dittoes (gb :: gbs)) in
                  let aux =
                    match b, gb with
                    | (_, _, No_domain), (_, _, No_domain) -> aux
                    | (v, _, Domain dom),
                      (_, _, Domain gdom) ->
                        if Expr.Eq.expr dom gdom then aux else
                          let sub =
                            Apply (Internal Builtin.Subseteq @@ v, [
                                     gdom ; dom
                                   ]) @@ v
                          in sub :: aux
                    | (v, _, No_domain),
                      (gv, _, Domain gdom) ->
                        let msg = Util.sprintf
                           "@.@[<b0>%s (%s)@ %s (%s \\in %a)@]@."
                           "Error: the TAKE argument" v.core
                           "does not match the pattern" gv.core
                           (Expr.Fmt.pp_print_expr (cx, Ctx.dot)) gdom
                         in
                         failwith msg
                    | (v, _, Domain dom),
                      (gv, _, No_domain) ->
                        let msg =
                          Util.sprintf "@.@[<b0>%s (%s \\in %a)@ %s (%s)@]@."
                              "Error: the TAKE argument" v.core
                              (Expr.Fmt.pp_print_expr (cx, Ctx.dot)) dom
                              "does not match the pattern" gv.core
                         in
                         failwith msg
                     | _ -> assert false (* cannot have a Ditto here *)
                  in
                  let (goal, shf) = match gbs with
                    | [] -> (ge, 1)
                    | _ ->
                        let gbs = match bs with
                          | [] -> List.map begin
                              fun b ->
                                snd (app_bound (shift shf) b)
                            end gbs
                          | _ -> gbs
                        in
                        (Quant (Forall, gbs, ge) @@ goal, shf + 1)
                  in
                  strip shf aux goal bs
              | _ ->
                  let msg =
                    Util.sprintf "@.@[<v2>@[<b0>%s@ %s@]@,%a@]@."
                      "Error: this TAKE step is applied to the following goal,"
                      "which is not a universal formula:"
                      (Expr.Fmt.pp_print_expr (cx, Ctx.dot)) goal
                  in
                  failwith msg
            end
        in
        let suff =
          try
            let (aux, goal) = strip 1 [] goal bs in
            let aux = List.unique ~cmp:Expr.Eq.expr aux in
            let bcx = hyps_of bs in
            let sq = { context = bcx ; active = goal } in
            let aux = (Ix 2 @@ st) :: List.map (app_expr (shift 2)) aux in
            let sprf = By ({ facts = aux ; defs = [] }, true) @@ st in
            Suffices (sq, sprf) @@ st
          with Failure msg ->
            let sq =
              {context = Deque.of_list [Fact (Internal Builtin.TRUE @@ oldgoal,
                                              Visible, Now ) @@ st ];
               active = oldgoal}
            in
            Suffices (sq, Error msg @@ st) @@ st
        in
        let suff = renumber_step (step_number stepno) suff in
        let suff = assign suff Props.orig_step st in
        (* let suff = anonymize suff in *)
        simplify_step cx oldgoal suff time_flag
    | Witness es ->
        let oldgoal = goal in
        let rec instantiate aux err goal = function
          | [] -> (aux, err, goal)
          | e :: es -> begin
              match expose_connective cx goal with
              | {core = Quant (Exists, (x, _, dom) :: bs, ge)} ->
                  let goal =
                    match bs with
                    | [] -> ge
                    | _ -> begin
                        let (_, bs) = app_bounds (shift 1) bs in
                        let bs =
                          match bs with
                          | (v, k, Ditto) :: bs ->
                              (v, k, app_bdom (shift 1) dom) :: bs
                          | _ -> bs
                        in
                        Quant (Exists, bs, ge) @@ goal
                      end
                  in
                  let (e, aux, err) = match dom with
                    | No_domain -> (e, aux, err)
                    | Domain dom ->
                        begin match expose_connective cx e with
                        | {core = Apply ({core = Internal Builtin.Mem},
                                         [t ; tdom])} as e ->
                            let aux =
                              if Expr.Eq.expr tdom dom then aux else
                                (Apply (Internal Builtin.Subseteq @@ tdom,
                                        [tdom ; dom]) @@ tdom)
                                :: aux
                            in
                            (t, e :: aux, err)
                        | e ->
                            let cx = (cx, Ctx.dot) in
                            let msg =
                              Util.sprintf
                                  "@.@[<b0>%s (%a)@ %s (%s \\in %a)@]@."
                                  "Error: the WITNESS argument"
                                  (Expr.Fmt.pp_print_expr cx) e
                                  "does not match the pattern"
                                  x.core (Expr.Fmt.pp_print_expr cx) dom
                            in
                            (e, aux, if err = "" then msg else err)
                        end
                    | _ -> assert false (* first domain can't be Ditto *)
                  in
                  let e = Apply (Internal Builtin.Unprimable @@ e, [e]) @@ e in
                  let goal = app_expr (scons e (shift 0)) goal in
                  instantiate aux err goal es
              | goal ->
                  let msg =
                    Util.sprintf "@.@[<v2>@[<b0>%s@ %s@]@,%a@]@."
                      "Error: this WITNESS step is applied to the following \
                       goal,"
                      "which is not an existential formula:"
                      (Expr.Fmt.pp_print_expr (cx, Ctx.dot)) goal
                  in
                  (aux, (if err = "" then msg else err), goal)
            end
        in
        let (aux, err, goal) = instantiate [] "" goal es in
        let aux = List.rev aux in
        let aux_len = List.length aux in
        let sprf = match query st Props.supp, aux with
          | _ when err <> "" -> (Error err) @@ st
          | ( Some _, _ | None, [] ) -> Obvious @@ st
          | _ ->
              let inits = List.mapi begin
                fun n e ->
                  let ass = {
                    context = Deque.empty ;
                    active = app_expr (shift (2 * n + 2)) e ;
                  } in
                  let prf =
                    By ({facts = [app_expr (shift 3) ass.active]; defs = []},
                        false) @@ e
                  in
                  let prf = match query st Props.meth with
                    | Some meth -> assign prf Props.meth meth
                    | _ -> prf in
                  let stp = Assert (ass, prf) @@ e in
                  stp
              end aux in
              let qed_prf =
                let facts = List.mapi begin
                  fun n _ -> Ix (2 * (aux_len - n)) @@ st
                end aux in
                let facts = (Ix (2 * aux_len + 2) @@ st) :: facts in
                let qed_prf = By ({facts = facts ; defs = []}, true) @@ st in
                let qed_prf = remove qed_prf Props.meth in
                qed_prf
                (* assign qed Props.step (Unnamed (sn + 1, Std.unique ())) *)
              in
              let stp = Steps (inits, {core = Qed qed_prf; props = qed_prf.props}) @@ st in
              stp
              (* assign stp Props.step (Named (sn, string_of_int (aux_len + 1), false)) *)
        in
        let suff =
          let cx = {
            context = Deque.empty ;
            active = goal ;
          } in
          Suffices (cx, sprf) @@ st
        in
        let suff = renumber_step (step_number stepno) suff in
        let suff = assign suff Props.orig_step st in
        (* let suff = anonymize suff in *)
        simplify_step cx oldgoal suff time_flag
    | Pcase (e, prf) ->
        let ass = Assert ({ context = Deque.of_list [ Fact (e, Visible,
        time_flag)  @@ st ] ;
                            active = app_expr (shift 1) goal }, prf) @@ st in
        let ass = assign ass Props.orig_step st in
        let ass = renumber_step (step_number stepno) ass in
        simplify_step cx goal ass time_flag
    | Pick (bs, e, prf) ->
        let ex = Quant (Exists, bs, e) @@ st in
        let (cx, goal, asst, time_flag) =
          let ass = Assert ({ context = Deque.empty ;
                              active = ex }, prf) @@ st in
          simplify_step cx goal (salt "ex" ass) time_flag
        in
        let (cx, goal, suffst, time_flag) =
          let (bs, e) = match (app_expr (shift 2) ex).core with
            | Quant (_, bs, e) -> (bs, e)
            | _ -> assert false
          in
          let scx = hyps_of bs in
          let scx = Deque.snoc scx (Fact (e, Visible, time_flag)  @@ e) in
          let ssq = { context = scx ;
                      active = app_expr (shift (Deque.size scx)) goal } in
          let sprf = Omitted (Elsewhere (Util.get_locus st)) @@ st in
          let suff = Suffices (ssq, sprf) @@ st in
          simplify_step cx goal suff time_flag
        in
        let nsts = match asst @ suffst with
          | nst :: nsts ->
              assign nst Props.orig_step st :: nsts
          | _ -> Errors.bug ~at:st "Proof.Simplify.simplify_step/PICK"
        in
        (cx, goal, nsts, time_flag)
  in
  Util.eprintf ~debug:"simpl" ~at:st
    "simplify_step (result)@\n@[<hv2>%t@ --> %t@]@.@."
    (fun ff -> ignore (P_fmt.pp_print_step (cx, Ctx.dot) ff st))
    (fun ff ->
       ignore (P_fmt.pp_print_proof (cx, Ctx.dot) ff (Steps (sts, {core = Qed (Omitted Implicit @@ st); props = st.props}) @@ st))) ;
  (scx, sgoal, sts, time_flag)

and expose_connective cx goal = match goal.core with
    | Apply ({ core = Ix n }, args) -> begin
        match Deque.nth ~backwards:true cx (n - 1)  with
          | Some {core = Defn ({ core = Operator (_, bod) }, _, _, _)} ->
              let op = app_expr (shift n) bod in
              let op = Util.set_locus op (Util.get_locus goal) in
              let goal = normalize ~cx:cx op args @@ op in
              expose_connective cx goal
          | Some h -> goal
          | _ ->
              Errors.bug ~at:goal "expose_connective"
      end
    | Ix n -> begin
        match Deque.nth ~backwards:true cx (n - 1) with
          | Some {core = Defn ({ core = Operator (_, bod) }, _, _, _)} ->
              let goal = app_expr (shift n) bod in
              expose_connective cx goal
          | Some h -> goal
          | _ ->
              Errors.bug ~at:goal "expose_connective"
      end
   (* we do prime normalization in the action frontend now
      and this feature does not seem useful.
      in case it is an important feature, it would be best to check if
      the connective is either exposed or primed than to normalize
      the primes as the transformation introduces new symbols for non-Leibniz
      operators and can cause a problem *)
   (* | Apply ({ core = Internal Builtin.Prime }, [pe]) ->
        let pe = Apply (Internal Builtin.Prime @@ goal, [expose_connective cx pe]) @@ goal in
        Expr.Elab.prime_normalize cx pe *)

   (* NOTE: it is important to push the prime one step down because we want
      to do this kind of thing:
      <1> (A => B)'
        <2> HAVE A'
      But indeed we should not call prime_normalize here, so we do it with
      direct pattern-matching instead. *)
    | Apply ({ core = Internal Builtin.Prime }, [pe]) ->
        let pe = expose_connective cx pe in
        let prime x = Apply (Internal Builtin.Prime @@ x, [x]) @@ x in
        let prime_bound ((h, k, dom) as e) =
          match dom with
          | Domain ee -> (h, k, Domain (prime ee))
          | _ -> e
        in
        begin match pe.core with
        | Quant (q, b, expr) ->
            Quant (q, List.map prime_bound b, prime expr) @@ goal
        | Apply ({core = Internal (Builtin.Implies | Builtin.Mem)} as op,
                 [a; b]) ->
            Apply (op, [prime a; prime b]) @@ goal
        (* We are only dealing with => \E \A \in. There are many more
           that we could do, but none of the uses of expose_connective is
           ever looking for them.*)
        | _ -> prime pe
        end
    | Parens (goal, _) ->
        expose_connective cx goal
    | _ ->
        goal

and renumber k prf =
  let sn = match query prf Props.step with
    | Some (Named (_, l, an)) -> Named (k, l, an)
    | _ -> Named (k, "_a" ^ string_of_int (Std.unique ()), true)
  in
  (* let sn = Named (k, "_a" ^ string_of_int (Std.unique ()), true) in *)
  let prf = assign prf Props.step sn in
  match prf.core with
    | Steps (inits, qed) ->
        let inits = List.map (renumber_step k) inits in
        let qed_prf = renumber (k + 1) (get_qed_proof qed) in
        Steps (inits, {qed with core = Qed qed_prf}) @@ prf
    | _ -> prf

and renumber_step k stp =
  let sn = match query stp Props.step with
    | Some (Named (_, l, an)) -> Named (k, l, an)
    | _ -> Named (k, "_a" ^ string_of_int (Std.unique ()), true)
  in
  let stp = assign stp Props.step sn in
  match stp.core with
    | Assert (sq, prf) ->
        Assert (sq, renumber (k + 1) prf) @@ stp
    | Suffices (sq, prf) ->
        Suffices (sq, renumber (k + 1) prf) @@ stp
    | Pcase (e, prf) ->
        Pcase (e, renumber (k + 1) prf) @@ stp
    | Pick (bs, e, prf) ->
        Pick (bs, e, renumber (k + 1) prf) @@ stp
    | _ -> stp

and expand_dittoes bs =
  let cdom = ref No_domain in
  List.map begin
    fun (v, k, d) -> match d with
      | Ditto -> (v, k, !cdom)
      | _ ->
          cdom := d ;
          (v, k, d)
  end bs
