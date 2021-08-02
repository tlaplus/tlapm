(*
 * proof/gen.ml --- proofs (generating obligations)
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

open Ext

open Property

open Expr.T
open Expr.Subst

open P_t

(* let glog = new Log.logger ~lev:Log.DEBUG ~pat:"%p%m" ~apps:[Log.out] *)

module Stats = struct
  let total      : int ref = ref 0
  let checked    : int ref = ref 0
  let absent     : Loc.locus list ref = ref []
  let omitted    : Loc.locus list ref = ref []
  let suppressed : Loc.locus list ref = ref []
end

let reset_stats () =
  Stats.total      := 0 ;
  Stats.checked    := 0 ;
  Stats.absent     := [] ;
  Stats.omitted    := [] ;
  Stats.suppressed := [] ;

type stats = {
  total      : int ;
  checked    : int ;
  absent     : Loc.locus list ;
  omitted    : Loc.locus list ;
  suppressed : Loc.locus list ;
}

let get_stats () = {
  total      = !Stats.total ;
  checked    = !Stats.checked ;
  absent     = List.rev !Stats.absent ;
  omitted    = List.rev !Stats.omitted ;
  suppressed = List.rev !Stats.suppressed ;
}

let set_defn vis l df =
  let rec doit n l = match n with
    | 0 -> begin
        match Deque.front l with
          | Some ({core = Defn (d, wd, _, ex)} as h, l) -> Deque.cons (Defn (d, wd, vis, ex) @@ h) l
          | Some (e, _) ->
              if !Params.verbose then
                Util.eprintf ~at:df "Indicated point is not a definition, but %t!\n%!"
                  (fun ff -> ignore (Expr.Fmt.pp_print_hyp (l, Ctx.dot) ff e)) ;
              failwith "Proof.Gen.set_defn/doit" ;
          | None -> l
      end
    | n -> begin match Deque.front l with
        | Some (h, l) -> Deque.cons h (doit (n - 1) l)
        | _ -> Errors.bug ~at:df "set_defn for empty context"
      end
  in
    doit
      (match df.core with
            | Dx n -> Deque.size l - n
            | Dvar v ->
                if !Params.verbose then
                  Util.eprintf ~at:df "Unknown definition %S\n" v ;
                failwith "Proof.Gen.set_defn")
      l

let domain_match f hran = match f.core with
  | Apply ({core = Internal Builtin.Mem}, [{core = Ix 0} ; ran])
      when Expr.Eq.expr hran ran ->
      true
  | _ -> false

let set_expr vis f cx =
  let succ = ref false in
  let rec doit f hs = match Deque.front hs with
    | None -> Deque.empty
    | Some (h, hs) ->
        let f = app_expr (shift (-1)) f in
        let h = begin match h.core with
          | Fact (hf, hv, tm) when Expr.Eq.expr hf f ->
              succ := true ;
              Fact (hf, vis, tm)
          | Fresh (hx, shp, hk, Bounded (hran, hv)) when domain_match f hran ->
              succ := true ;
              Fresh (hx, shp, hk, Bounded (hran, vis))
          | h -> h
        end @@ h
        in Deque.cons h (doit f hs)
  in
  let cx = Deque.rev (doit f (Deque.rev cx)) in
    if !succ then cx else begin
      Util.eprintf ~at:f "This expression does not appear in the context and cannot be hidden.\n" ;
      failwith "proof.Gen.set_expr"
    end

let obligate sq kind =
  incr Stats.total;
  {
   id = None;
   obl = sq;
   fingerprint = None;
   kind = kind;
  }

let exprify sq =
  if Deque.null sq.context then sq.active.core else Sequent sq

let assumed_facts offset sq =
  let exprs : expr list ref = ref [] in
  let rec scan offset hs = match Deque.rear hs with
    | None -> ()
    | Some (hs, h) -> begin
        match h.core with
          | Fact (e, Visible, _) ->
              exprs := app_expr (shift offset) e :: !exprs ;
              scan (offset + 1) hs
          | _ ->
              scan (offset + 1) hs
      end in
  scan offset sq.context ;
  List (Refs, !exprs)

(* The following is the core of the PM. Understand it, and you've
   understood pretty much everything about the proof language. *)

let prove_assertion ~suffices cx goal asq time_flag =
  let stepno = Property.get asq Props.step in
  let is_anon = match stepno with Named (_, _, true) -> true | _ -> false in
  let stepnm = string_of_stepno stepno @@ asq in
  let vis =
    if suffices then
      (* for the next sibling step of a SUFFICES step *)
      if is_anon then Visible else Hidden
    else
      (* for the subproof of an assertion step *)
      if is_anon then
        (* anon assertions can't be named, so this is visible *)
        Visible
      else Hidden
  in
  (* we need to compute the new time_flag based on the hyps of the sequent (asq)
   * *)
  let hyps = Deque.map begin
    fun _ h -> match h.core with
      | Fact (f, _, tm) ->
          Fact (f, vis, tm) @@ h
      | _ -> h
  end asq.core.context in
  (* here we add the asserted sequent assumptions to the context and they are
   * visible if they are anon *)
  (* the time is taken to be the flag because sequents get the time of the flag
   * always *)
  let cx = Deque.append cx hyps in
  (*
   * The above is commented out in order to fix the soundness bug with regard
   * to not being able to approximate boxing correctly when adding the negation
   * of goals to the hyps
   *)
    (*let f = Apply (Internal Builtin.Neg @@ asq, [
    app_expr (shift (Deque.size hyps)) goal
  ]) @@ asq in
  *)
  let f = Internal Builtin.TRUE @@ asq in
  let noldfac = Fact (f, Hidden, time_flag) @@ asq in
  let cx = Deque.snoc cx noldfac in

  let stbod = assumed_facts 2 asq.core @@ asq in
  let time_flag = Expr.Temporal_props.check_time_change asq.core.context time_flag in
  let stdef = Defn (Operator (stepnm, stbod) @@ asq,
                    Proof time_flag , Visible, Local) @@ asq in
  let cx = Deque.snoc cx stdef in
  let f = Ix 1 @@ asq in
  let cx = Deque.snoc cx (Fact (f, Hidden, time_flag) @@ asq) in
   let goal = app_expr (shift 3) asq.core.active in
  (cx, goal, time_flag)

let use_assertion ~suffices cx goal asq time_flag =
  let stepno = Property.get asq Props.step in
  let is_anon = match stepno with Named (_, _, true) -> true | _ -> false in
  let stepnm = string_of_stepno stepno @@ asq in
  let stbod = exprify asq.core @@ asq in
  let stdef = Defn (Operator (stepnm, stbod) @@ asq,
                    Proof time_flag, Visible, Local) @@ asq in
  let cx = Deque.snoc cx stdef in
  let vis =
    if suffices then
      (* for the subproof of a SUFFICES step *)
      (* Current semantics per Leslie's proposal in e-mail thread titled
       * "SUFFICES doesn't work with --explicit" *)
      Visible
    else
      (* for the subsequent sibling step of an assertion step *)
      if is_anon then
        (* anonymous steps can't be named, so thse are usable *)
        Visible
      else Hidden
  in
  (* here we add the assertion as a fact in order to prove the goal *)
  let f = Ix 1 @@ asq in
  let cx = Deque.snoc cx (Fact (f, vis, time_flag) @@ asq) in
  let goal = app_expr (shift 2) goal in
  (cx, goal)


(********************************************************)

let rec get_steps_proof prf =
  match prf.core with
    | Steps (inits, _) ->
        inits @ (List.fold_left (fun x s -> x@(get_steps_step s)) [] inits)
    | By _ | Obvious | Omitted _ | Error _ -> []


and get_steps_step stp =
  match stp.core with
    | Assert (_, prf) -> stp::(get_steps_proof prf)
    | Suffices (_, prf) -> stp::(get_steps_proof prf)
    | _ -> [stp]

(********************************************************)

let rec generate (sq : sequent) prf time_flag =
  let prf = assign prf Props.goal sq in
  let loc = Util.get_locus prf in
  let file_basename = Filename.basename loc.Loc.file in
  if !Params.verbose then
    Util.printf "Deciding whether to generate \
        proof obligations for a proof in \
        a file with basename `%s` \
        (inside `Proof.Gen`)\n"
        file_basename;
  if not (List.mem file_basename !Params.input_files)
     || Loc.line loc.Loc.stop < !Params.tb_sl
     || Loc.line loc.Loc.start > !Params.tb_el
  then begin
    if !Params.verbose then
    Util.printf "Skipping generation of \
        proof obligations for this particular proof, \
        because no path from those given to `tlapm` \
        has basename `%s`\n"
        file_basename;
    prf
  end else begin
    if !Params.verbose then
    Util.printf "Will generate proof obligations for \
        a proof in a file with basename `%s`\n"
        file_basename;
    match prf.core with
      | Obvious ->
          let ob = obligate (sq @@ prf) Ob_main in
          assign prf Props.obs [ob]
      | Omitted h ->
          begin match h with
            | Explicit ->
                Stats.omitted := (Util.get_locus prf) :: !Stats.omitted
            | Implicit ->
                Stats.absent := (Util.get_locus prf) :: !Stats.absent
            | Elsewhere _ ->
                ()
          end;
          prf
      | Steps (inits, qed) ->
          let (sq, inits, time_flag) = List.fold_left gen_step (sq, [], time_flag) inits in
          let inits = List.rev inits in
          let qed_prf = generate sq (get_qed_proof qed) time_flag in
          Steps (inits, {core = Qed qed_prf; props = qed_prf.props}) @@ prf
      | By _ ->
          Errors.bug ~at:prf "Proof.Gen.generate"
      | Error msg ->
          let ob = obligate (sq @@ prf) (Ob_error msg) in
          assign prf Props.obs [ob]
  end

and gen_step (sq, inits, time_flag) stp =
  let stp = assign stp Props.goal sq in
  match stp.core with
    | Forget k ->
        let nfacts = Deque.size sq.context in
        let sq = { sq with context = Deque.map begin
                     fun n h -> match h.core with
                       | Fact (e, Visible, tm) when k + n < nfacts ->
                           Fact (e, Hidden, tm) @@ h
                       | _ -> h
                   end sq.context }
        in
        (sq, stp :: inits, time_flag)
    | Use ({defs = []; facts = [f]}, _) ->
        let fob = obligate ({sq with active = f} @@ stp) Ob_support in
        (* since we might be in a Now scope but the fact from an earlier Always
         * scope, we must search for it in the context and take the right scope
         * *)
        let tm = match f.core with
        | Ix n ->
            assert (n <= Deque.size sq.context && n > 0);
            begin match Deque.nth ~backwards:true sq.context (n - 1) with
            | Some {core = (Fact (_,_,tm) | Defn (_,Proof tm,_,_))} -> tm
            | e -> Always (* all other options are with Always scope*) end
        | _ -> time_flag (* the rest are expressions which get the current scope *) in
        let stp = assign stp Props.obs [fob] in
        let sq = {context = Deque.snoc sq.context (Fact (f, Visible, tm) @@ f);
                  active = app_expr (shift 1) sq.active}
        in
        (sq, stp :: inits, time_flag)
    | Use ({facts = []} as us, _) ->
        let sq = { sq with context = begin
                     List.fold_left (set_defn (Visible)) sq.context us.defs
                   end } in
        (sq, stp :: inits, time_flag)
    | Use (_, _) -> assert false
    | Hide us ->
        let cx = List.fold_left (set_defn Hidden) sq.context us.defs in
        let cx = List.fold_right (set_expr Hidden) us.facts cx in
        ({ sq with context = cx }, stp :: inits, time_flag)
    | Define dfs ->
        let sq = {
          context = Deque.append_list sq.context
            (List.map (fun d -> Defn (d, User, Visible, Local) @@ d) dfs) ;
          active = app_expr (shift (List.length dfs)) sq.active ;
        } in (sq, stp :: inits, time_flag)
    | Assert (asq, prf) ->
        let prf =
          let (cx, goal, time_flag1) = prove_assertion ~suffices:false sq.context
          sq.active (asq @@ stp) time_flag in
          generate { context = cx ; active = goal } prf time_flag1
        in
        let stp = { stp with core = Assert (asq, prf) } in
        let (cx, goal) = use_assertion ~suffices:false sq.context
        sq.active (asq @@ stp) time_flag in
        ({ context = cx ; active = goal }, stp :: inits, time_flag)
    | Suffices (asq, prf) ->
        let prf =
          let (cx, goal) = use_assertion ~suffices:true sq.context
          sq.active (asq @@ stp) time_flag in
          generate { context = cx ; active = goal } prf time_flag
        in
        let stp = Suffices (asq, prf) @@ stp in
        let (cx, goal, time_flag1) = prove_assertion ~suffices:true sq.context
        sq.active (asq @@ stp) time_flag in
        ({ context = cx ; active = goal }, stp :: inits, time_flag1)
    | Pcase _
    | Have _
    | Take _
    | Witness _
    | Pick _ ->
        Errors.bug ~at:stp "Proof.Gen.gen_step"

(* FIXME this function must split the list of facts into
   its elements and pass them one by one to gen_step *)
(* also, set the use_location property on each fact *)
let mutate_one cx uh us time_flag =
  let stp = match uh with
    | `Use false -> Use (us.core, false) @@ us
    | `Use true -> assign (Use (us.core, false) @@ us) Props.supp ()
    | `Hide -> Hide us.core @@ us
  in
  let stp = assign stp Props.step (Unnamed (0, 0)) in
  match gen_step ({context = cx ; active = (At false) @@ us}, [], time_flag) stp with
    | (sq, st :: _, time_flag) ->
        let obs = Option.default [] (query st Props.obs) in
        (sq.context, obs, time_flag)
    | _ -> Errors.bug ~at:us "Proof.Gen.mutate"

let rec mutate cx uh us time_flag =
  match us.core with
  | {defs = h::t; facts = ff} ->
      let (cx1, obs1, time_flag) = mutate_one cx uh ({defs = h::t; facts = []} @@ us)
      time_flag in
      let (cx2, obs2) = mutate cx1 uh ({defs = []; facts = ff} @@ us) time_flag in
      (cx2, obs1 @ obs2)
  | {defs = []; facts = h::t} ->
      let f = assign h Props.use_location (Util.get_locus us) in
      let (cx1, obs1, time_flag) = mutate_one cx uh ({defs = []; facts = [f]} @@ us)
      time_flag in
      let ff = List.map (app_expr (shift 1)) t in
      let (cx2, obs2) = mutate cx1 uh ({defs = []; facts = ff} @@ us)
      time_flag in
      (cx2, obs1 @ obs2)
  | {defs = []; facts = []} -> (cx, [])
;;

let collect prf =
  let coll = ref [] in
  let emit obs = coll := List.rev obs @ !coll in
  let obgetter = object (self : 'self)
    inherit [unit] P_visit.map as super
    method proof scx prf =
      let prf = match prf.core with
        | Obvious | By _ | Error _ ->
            let () = match query prf Props.obs, query prf Props.supp with
              | Some obs, None ->
                  Stats.checked := List.length obs + !Stats.checked ;
                  emit obs
              | Some obs, _ ->
                  List.iter begin fun ob ->
                    Stats.suppressed := (Util.get_locus ob.obl)
                                        :: !Stats.suppressed
                  end obs
              | _ -> () in
            prf
        | Omitted _ ->
            prf
        | Steps (sts, qed) ->
            let qed_prf = self#proof scx (get_qed_proof qed) in
            let (_, sts) = self#steps scx sts in
            let prf = Steps (sts, {qed with core = Qed qed_prf}) @@ prf in
            prf
      in
      (* prf *)
      Property.remove prf Props.obs

    method step scx st =
      let () = match st.core with
        | Use _ -> begin
            match query st Props.obs, query st Props.supp with
              | Some obs, None ->
                  Stats.checked := List.length obs + !Stats.checked ;
                  emit obs
              | Some obs, _ ->
                  List.iter begin fun ob ->
                    Stats.suppressed := (Util.get_locus ob.obl) :: !Stats.suppressed
                  end obs
              | _ -> ()
          end
        | _ -> ()
      in
      let (scx, st) = super#step scx st in
      (scx, st)
      (*scx, Property.remove st Props.obs*)
  end in
  let prf = obgetter#proof ((), Deque.empty) prf in
  (List.rev !coll, prf)
