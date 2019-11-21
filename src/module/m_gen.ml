(*
 * module/gen.ml --- generation of obligations
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

Revision.f "$Rev$";;

open Ext
open Property

open Expr.T
open Expr.Subst
open Proof.T

open M_t

(*let debug = Printf.eprintf;;*)

let rec generate cx m =
  let obs : obligation list ref = ref [] in
  let emit ob = obs := ob :: !obs in
  let rsumm : summary ref = ref empty_summary in
  let fincx = ref Deque.empty in
  let rec visit cx mus = match mus with
    | [] ->
        fincx := cx ; []
    | mu :: mus -> begin
        match mu.core with
          | Theorem (nm, sq, naxs, prf, prf_orig, _) ->
             let cx = match nm with
                | Some nm ->
                    Deque.snoc cx (Defn (Operator (nm, exprify_sequent sq @@ nm)
                    @@ mu, Proof Always , Visible, Export) @@ mu)
                | _ ->
                    cx
              in
              let prf, summ =
                let psq = if nm = None then sq else app_sequent (shift 1) sq in
                (* the addition of the sequent context to the global context
                 * might invalidate the later generality. I.e. the added
                 * assumptions from the sequent might prevent the boxifying of
                 * all assumptions *)
                let psq = { psq with context = Deque.append cx psq.context } in
                let time_flag = Expr.Temporal_props.check_time_change
                psq.context Always in
                Proof.Gen.reset_stats () ;
                let prf = Proof.Gen.generate psq prf time_flag in
                let (obs, prf) = Proof.Gen.collect prf in
                (*let obs =
                  let process_ob ob =
                    let visitor1 = object (self: 'self)
                      inherit Expr.Constness.const_visitor
                    end in
                    let visitor2 = object (self: 'self)
                      inherit Expr.Leibniz.leibniz_visitor
                    end in
                    let ob1 =  visitor1#expr ((),cx) ((Sequent
                    ob.obl.core) @@ ob.obl) in
                    let ob2 =  visitor2#expr ((),cx) ob1 in
                    match ob2.core with
                      | Sequent sq -> { ob with obl = { ob.obl with core = sq } }
                      | _ -> failwith "Proof_prep.normalize"
                  in
                  List.map process_ob obs in *)
                let sts = Proof.Gen.get_stats () in
                let summ = { sum_total = sts.Proof.Gen.total
                           ; sum_absent = (List.length sts.Proof.Gen.absent, sts.Proof.Gen.absent)
                           ; sum_omitted = (List.length sts.Proof.Gen.omitted, sts.Proof.Gen.omitted)
                           ; sum_suppressed = (List.length sts.Proof.Gen.suppressed, sts.Proof.Gen.suppressed)
                           } in
                  List.iter emit obs ;
                  prf, summ in
                rsumm := cat_summary !rsumm summ ;
                let mu = { mu with core = Theorem (nm, sq, naxs, prf, prf_orig, summ) } in
                let he = if nm = None then exprify_sequent sq else Ix 1 in
                let cx = Deque.snoc cx (Fact (he @@ mu, Hidden, Always) @@ mu) in
                  mu :: visit cx mus
          | Submod m ->
              let (m, obs, summ) = generate cx m in
                List.iter emit obs ;
                rsumm := cat_summary !rsumm summ ;
                (Submod m @@ mu) :: visit cx mus
          | Mutate (uh, us) ->
              let (cx, obs) = Proof.Gen.mutate cx uh (us @@ mu) Always in
                List.iter emit obs ;
                mu :: visit cx mus
          | Anoninst _ ->
              Errors.bug ~at:mu "Module.Gen.generate: unnamed INSTANCE"
          | _ ->
              let cx = Deque.append_list cx (hyps_of_modunit mu) in
                mu :: visit cx mus
      end
  in
  let body = visit cx m.core.body in
    ({ m with core = { m.core with body = body } }, List.rev (!obs), !rsumm)

(****************************************************************************)

let step_name x = match Property.query x Props.step with
  | None -> 0,""
  | Some (Named (sn, sl, _)) -> (sn,sl)
  | Some (Unnamed (sn, sid)) -> (sn,"")

let toolbox_consider prf =
  let loc = Option.get (Util.query_locus prf) in
    (!Params.tb_sl-1 < (Loc.line loc.Loc.start))
  && ((Loc.line loc.Loc.stop) < !Params.tb_el+1)

let p_collect_usables prf : Proof.T.usable list =
  let coll = ref [] in
  let main_step = ref (0,"") in
  let toolbox_main n = (!Params.tb_sl = n) in
  let visitor = object (self : 'self)
    inherit [unit] Proof.Visit.iter as super
    method step scx st =
      let loc = Option.get (Util.query_locus st) in
      if toolbox_main (Loc.line loc.Loc.start) 
				then main_step := (step_name st) else ();
      super#step scx st
    method proof scx prf =
      match prf.core with
      | By (u,_) when toolbox_consider prf -> 
          let ff = List.filter (fun e -> 
            match e.core with 
            | Opaque s when s.[0] = '<' -> 
                let parse_step s = 
									if Str.string_match (Str.regexp "<\\([0-9].*\\)>\\(.*\\)") s 0 then
                  (int_of_string (Str.matched_group 1 s), Str.matched_group 2 s) 
									else (0,"") 
								in
                let sn,sl = parse_step s in
                if sn < (fst !main_step) then true else
                   sn = (fst !main_step) && String.compare sl (snd !main_step) <= 0
            | _ -> true
            ) u.facts in
          let u = {u with facts = ff} in
          if u.facts = [] && u.defs = [] then () else coll := u :: !coll
      | Steps (inits, ({core = Qed pq} as q)) ->
          let scx = self#steps scx inits in
          let loc = Option.get (Util.query_locus pq) in
          if toolbox_main ((Loc.line loc.Loc.start) - 1) 
						then main_step := (step_name q) else ();
          self#proof scx pq
      | _ ->
          super#proof scx prf
  end in
  visitor#proof ((), Deque.empty) prf;
  List.rev !coll

let collect_usables (m:mule) : Proof.T.usable option =
  let remove_repeated_ex es =
    let e_mem e es = List.exists (Expr.Eq.expr e) es in
    List.fold_left (fun r e -> if e_mem e r then r else e :: r) [] es
    |> List.rev
  in
  let remove_repeated_def (ds:use_def wrapped list) =
    let use_def_eq d e = 
      match d.core, e.core with
      | Dvar s, Dvar t when s = t -> true
      | Dx n, Dx m when n = m -> true
      | _ -> false
    in
    let e_mem x ds = List.exists (use_def_eq x) ds in
    List.fold_left (fun r e -> if e_mem e r then r else e :: r) [] ds
    |> List.rev
  in

  let mloc = Option.get (Util.query_locus m) in
  let rec visit (mus:modunit list) = 
    match mus with
    | [] -> []
    | mu :: mus -> begin
        match mu.core with
        | Theorem (nm, _, _, _, prf_orig, _) 
            when !Params.toolbox 
              (* && (not !Params.toolbox_all) *) ->
            let loc = Option.get (Util.query_locus prf_orig) in
            if loc.Loc.file = mloc.Loc.file 
            then begin
             (List.rev (p_collect_usables prf_orig)) @ visit mus
            end
            else visit mus
        | Submod _ ->
            visit mus
        | Mutate (_, us) -> (** more usables here *)
            visit mus
        | Anoninst _ ->
            Errors.bug ~at:mu "collect_usables: unnamed INSTANCE"
        | _ ->
            visit mus
      end
  in
  let us = visit m.core.body in
  let ffs,dds = List.fold_left (fun (fs,ds) u -> (u.facts @ fs, u.defs @ ds)) ([],[]) us in
  let ffs = remove_repeated_ex ffs in
  let dds = remove_repeated_def dds in
  if ffs = [] && dds = [] then None else Some { facts = ffs ; defs = dds }