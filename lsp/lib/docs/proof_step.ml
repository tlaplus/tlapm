open Util
open Prover

(** We categorize the proof steps just to make the presentation in the UI
    clearer. *)
module Kind = struct
  type t = Module | Struct | Leaf

  let to_string = function
    | Module -> "module"
    | Struct -> "struct"
    | Leaf -> "leaf"
end

type t = {
  kind : Kind.t;
      (** Kind/Type of this proof step. We want to show the proof steps
          differently based in its type. *)
  status_parsed : Proof_status.t option;
      (** Status derived at the parse time, if any. This is for the omitted or
          error cases. *)
  status_derived : Proof_status.t;
      (** Derived status. Here we sum-up the states from all the related
          obligations and sub-steps. *)
  step_loc : Range.t;
      (** Location of the entire step. It starts with a statement/sequent and
          ends with the BY keyword (inclusive), not including the listed facts
          and definitions. In the case of a structured proof, this ends with the
          BY keyword of the corresponding QED step. *)
  head_loc : Range.t;
      (** The location of the proof sequent. It is always contained within the
          [step_loc]. This is shown as a step in the UI. *)
  full_loc : Range.t;
      (** [step_loc] plus all the BY facts included. If an obligation is in
          [full_loc] but not in the [step_loc], we consider it supplementary
          (will be shown a bit more hidden). *)
  obs : Obl.t RangeMap.t;
      (** Obligations associated with this step. Here we include all the
          obligations fitting into [full_loc], but not covered by any of the
          [sub] steps. *)
  sub : t list; (* Sub-steps, if any. *)
}

(* Derived status is always a minimum of the parsed, the obligations and the sub-steps. *)
let derived_status parsed obs sub =
  let parsed = Option.value ~default:Proof_status.top parsed in
  let ps_min = Proof_status.min in
  let acc =
    RangeMap.fold (fun _ obl acc -> ps_min acc (Obl.status obl)) obs parsed
  in
  List.fold_left (fun acc sub -> ps_min acc sub.status_derived) acc sub

(* Takes step parameters and a set of remaining unassigned obligations,
   constructs the proof step and returns obligations that are left unassigned. *)
let make ~kind ?status_parsed ~step_loc ?head_loc ~full_loc ~sub obs_map =
  let intersects_with_full_loc obl_loc _ = Range.intersect obl_loc full_loc in
  let intersects_with_step_loc obl_loc = Range.intersect obl_loc step_loc in
  let obs, obs_map = RangeMap.partition intersects_with_full_loc obs_map in
  let obs =
    RangeMap.mapi
      (fun obl_range obl ->
        match intersects_with_step_loc obl_range with
        | true -> Obl.with_role Obl.Role.Main obl
        | false -> Obl.with_role Obl.Role.Aux obl)
      obs
  in
  let head_loc =
    (* Take the beginning of the first line, if header location is unknown. *)
    match head_loc with
    | Some head_loc -> head_loc
    | None -> Range.(of_points (from step_loc) (from step_loc))
  in
  let status_derived = derived_status status_parsed obs sub in
  let ps =
    {
      kind;
      status_parsed;
      status_derived;
      step_loc;
      head_loc;
      full_loc;
      obs;
      sub;
    }
  in
  (ps, obs_map)

let as_lsp_tlaps_proof_state_marker ps =
  let status = Proof_status.to_string ps.status_derived in
  let range = Range.as_lsp_range ps.head_loc in
  let hover = Proof_status.to_message ps.status_derived in
  Structs.TlapsProofStepMarker.make ~status ~range ~hover

let as_lsp_tlaps_proof_step_details uri ps =
  let kind = Kind.to_string ps.kind in
  let status = Proof_status.to_string ps.status_derived in
  let location =
    LspT.Location.create ~uri ~range:(Range.as_lsp_range ps.full_loc)
  in
  let obligations =
    List.map
      (fun (_, o) -> Obl.as_lsp_tlaps_proof_obligation_state o)
      (RangeMap.to_list ps.obs)
  in
  let sub_count =
    let proved, failed, omitted, missing, pending, progress =
      List.fold_left
        (fun (proved, failed, omitted, missing, pending, progress) sub_ps ->
          match sub_ps.status_derived with
          | Proved -> (proved + 1, failed, omitted, missing, pending, progress)
          | Failed -> (proved, failed + 1, omitted, missing, pending, progress)
          | Omitted -> (proved, failed, omitted + 1, missing, pending, progress)
          | Missing -> (proved, failed, omitted, missing + 1, pending, progress)
          | Pending -> (proved, failed, omitted, missing, pending + 1, progress)
          | Progress -> (proved, failed, omitted, missing, pending, progress + 1))
        (0, 0, 0, 0, 0, 0) ps.sub
    in
    Structs.CountByStepStatus.make ~proved ~failed ~omitted ~missing ~pending
      ~progress
  in
  Structs.TlapsProofStepDetails.make ~kind ~status ~location ~obligations
    ~sub_count

(* Recursively collect all the fingerprinted obligations.
   This is used to transfer proof state from the
   previous to the new document version. *)
let obl_by_fp ps =
  let tbl = Hashtbl.create 1024 in
  match ps with
  | None -> tbl
  | Some ps ->
      let rec traverse ps =
        let add_by_fp (o : Obl.t) =
          match Obl.fingerprint o with
          | None -> ()
          | Some fp -> Hashtbl.add tbl fp o
        in
        RangeMap.iter (fun _ o -> add_by_fp o) ps.obs;
        List.iter traverse ps.sub
      in
      traverse ps;
      tbl

(** Just make a flat list of all the proof steps. *)
let flatten ps =
  let rec traverse ps = ps :: List.flatten (List.map traverse ps.sub) in
  match ps with None -> [] | Some ps -> traverse ps

(** Iterate over the proof steps. *)
let fold f acc ps =
  let rec fold_rec acc ps =
    let acc = f acc ps in
    List.fold_left fold_rec acc ps.sub
  in
  match ps with None -> acc | Some ps -> fold_rec acc ps

(** Iterate over obligations of a particular proof step. *)
let fold_obs f acc ps = RangeMap.fold (fun _ obl acc -> f acc obl) ps.obs acc

module Acc = struct
  type t = { file : string; obs_map : Obl.t RangeMap.t }

  let some (x, acc) = (Some x, acc)
  let for_file file acc = file = acc.file
end

let if_in_file wrapped file fn =
  match Tlapm_lib.Util.query_locus wrapped with
  | Some loc when loc.file = file -> fn (Range.of_locus_must loc)
  | Some _ -> None
  | None -> None

let if_in_file_acc wrapped acc fn =
  match Tlapm_lib.Util.query_locus wrapped with
  | Some loc when Acc.for_file loc.file acc -> fn (Range.of_locus_must loc) acc
  | Some _ -> (None, acc)
  | None -> (None, acc)

let rec of_proof step_loc sq_range (proof : Tlapm_lib.Proof.T.proof) acc :
    t * Acc.t =
  let open Tlapm_lib in
  let kind, sub, status_parsed, suppl_loc, acc =
    match Property.unwrap proof with
    | Proof.T.Obvious -> (Kind.Leaf, [], None, None, acc)
    | Proof.T.Omitted omission ->
        let status_parsed =
          match omission with
          | Explicit -> Proof_status.Omitted
          | Implicit -> Proof_status.Missing
          | Elsewhere _loc -> Proof_status.Omitted
        in
        (Kind.Leaf, [], Some status_parsed, None, acc)
    | Proof.T.By (usable, _only) ->
        let wrapped_join_ranges base list =
          List.fold_left
            (fun acc d ->
              match Range.of_wrapped d with
              | None -> acc
              | Some r -> Range.join acc r)
            base list
        in
        let suppl_range = step_loc in
        let suppl_range = wrapped_join_ranges suppl_range usable.defs in
        let suppl_range = wrapped_join_ranges suppl_range usable.facts in
        (Kind.Leaf, [], None, Some suppl_range, acc)
    | Proof.T.Steps (steps, qed_step) ->
        let acc, sub =
          List.fold_left_map
            (fun acc s ->
              let s, acc = of_step s acc in
              (acc, s))
            acc steps
        in
        let sub = List.filter_map Fun.id sub in
        let qed, acc = of_qed_step qed_step acc in
        let sub = sub @ [ qed ] in
        let suppl_loc =
          List.fold_left
            (fun acc sub_ps -> Range.join acc sub_ps.full_loc)
            step_loc sub
        in
        (Kind.Struct, sub, None, Some suppl_loc, acc)
    | Proof.T.Error _ -> (Kind.Leaf, [], Some Proof_status.Failed, None, acc)
  in
  let head_loc =
    match sq_range with
    | Some sq_range -> Some Range.(of_points (from step_loc) (till sq_range))
    | None -> None
  in
  let full_loc =
    match suppl_loc with
    | None -> step_loc
    | Some suppl_loc -> Range.join step_loc suppl_loc
  in
  let st, obs_map =
    make ~kind ?status_parsed ~step_loc ?head_loc ~full_loc ~sub acc.obs_map
  in
  (st, { acc with obs_map })

and of_implicit_proof_step step_loc suppl_locs (acc : Acc.t) : t * Acc.t =
  let full_loc = List.fold_left Range.join step_loc suppl_locs in
  let st, obs_map =
    make ~kind:Kind.Leaf ~step_loc ~head_loc:step_loc ~full_loc ~sub:[]
      acc.obs_map
  in
  (st, { acc with obs_map })

(** USE generates aux proof obligations for the facts mentioned, so we create a
    step for presenting their state. *)
and of_usable (usable : Tlapm_lib.Proof.T.usable) step_loc (acc : Acc.t) :
    t option * Acc.t =
  match usable.facts with
  | [] -> (None, acc)
  | first_fact :: _ ->
      let facts_loc =
        List.fold_left Range.join
          (Range.of_wrapped_must first_fact)
          (List.map Range.of_wrapped_must usable.facts)
      in
      let full_loc = Range.join step_loc facts_loc in
      let st, obs_map =
        make ~kind:Kind.Leaf ~step_loc ~head_loc:step_loc ~full_loc ~sub:[]
          acc.obs_map
      in
      Acc.some (st, { acc with obs_map })

and of_step (step : Tlapm_lib.Proof.T.step) acc : t option * Acc.t =
  let open Tlapm_lib in
  match Property.unwrap step with
  | Proof.T.Hide _ -> (None, acc)
  | Proof.T.Define _ -> (None, acc)
  | Proof.T.Assert (sequent, proof) ->
      Acc.some
        (of_proof
           (Range.of_wrapped_must step)
           (Range.of_wrapped sequent.active)
           proof acc)
  | Proof.T.Suffices (sequent, proof) ->
      Acc.some
        (of_proof
           (Range.of_wrapped_must step)
           (Range.of_wrapped sequent.active)
           proof acc)
  | Proof.T.Pcase (expr, proof) ->
      Acc.some
        (of_proof
           (Range.of_wrapped_must step)
           (Range.of_wrapped expr) proof acc)
  | Proof.T.Pick (_bounds, expr, proof) ->
      Acc.some
        (of_proof
           (Range.of_wrapped_must step)
           (Range.of_wrapped expr) proof acc)
  | Proof.T.PickTuply (_, expr, proof) ->
      Acc.some
        (of_proof
           (Range.of_wrapped_must step)
           (Range.of_wrapped expr) proof acc)
  | Proof.T.Use (usable, _) -> of_usable usable (Range.of_wrapped_must step) acc
  | Proof.T.Have expr ->
      let suppl_locs = List.filter_map Range.of_wrapped [ expr ] in
      Acc.some
        (of_implicit_proof_step (Range.of_wrapped_must step) suppl_locs acc)
  | Proof.T.Take bounds ->
      let suppl_locs =
        List.filter_map (fun (hint, _, _) -> Range.of_wrapped hint) bounds
      in
      Acc.some
        (of_implicit_proof_step (Range.of_wrapped_must step) suppl_locs acc)
  | Proof.T.TakeTuply tuply_bounds ->
      let suppl_locs =
        List.concat
          (List.map
             (fun (tuply_name, _) ->
               match tuply_name with
               | Expr.T.Bound_name hint ->
                   List.filter_map Range.of_wrapped [ hint ]
               | Expr.T.Bound_names hints ->
                   List.filter_map Range.of_wrapped hints)
             tuply_bounds)
      in
      Acc.some
        (of_implicit_proof_step (Range.of_wrapped_must step) suppl_locs acc)
  | Proof.T.Witness exprs ->
      let suppl_locs = List.filter_map Range.of_wrapped exprs in
      Acc.some
        (of_implicit_proof_step (Range.of_wrapped_must step) suppl_locs acc)
  | Proof.T.Forget _ -> (None, acc)

and of_qed_step (qed_step : Tlapm_lib.Proof.T.qed_step) acc : t * Acc.t =
  match Tlapm_lib.Property.unwrap qed_step with
  | Tlapm_lib.Proof.T.Qed proof ->
      let open Tlapm_lib in
      let qed_loc = Property.query qed_step Proof.Parser.qed_loc_prop in
      let qed_range = Range.of_locus_opt qed_loc in
      of_proof (Range.of_wrapped_must qed_step) qed_range proof acc

(* This is internal function for traversing the modules and module units recursively. *)
let rec of_submod (mule : Tlapm_lib.Module.T.mule) (acc : Acc.t) :
    t option * Acc.t =
  let open Tlapm_lib in
  if_in_file_acc mule acc @@ fun step_loc acc ->
  let mule = Property.unwrap mule in
  let mu_step mu (sub, acc) =
    let st, acc = of_mod_unit mu acc in
    let sub = match st with None -> sub | Some st -> st :: sub in
    (sub, acc)
  in
  let sub, acc = List.fold_right mu_step mule.body ([], acc) in
  match sub with
  | [] -> (None, acc)
  | _ ->
      let st, obs_map =
        make ~kind:Kind.Module ~step_loc ~full_loc:step_loc ~sub acc.obs_map
      in
      (Some st, { acc with obs_map })

and of_mod_unit (mod_unit : Tlapm_lib.Module.T.modunit) acc : t option * Acc.t =
  let open Tlapm_lib in
  let open Tlapm_lib.Module.T in
  if_in_file_acc mod_unit acc @@ fun mod_unit_loc acc ->
  match Property.unwrap mod_unit with
  | Constants _ -> (None, acc)
  | Recursives _ -> (None, acc)
  | Variables _ -> (None, acc)
  | Definition _ -> (None, acc)
  | Axiom _ -> (None, acc)
  | Theorem (_name, sq, _naxs, _prf, prf_orig, _sum) ->
      Acc.some (of_proof mod_unit_loc (Range.of_wrapped sq.active) prf_orig acc)
  | Submod sm -> of_submod sm acc
  | Mutate (`Hide, _) -> (None, acc)
  | Mutate (`Use _, usable) -> of_usable usable mod_unit_loc acc
  | Anoninst _ -> (None, acc)

(* This is the entry point for creating proof steps from a module.
   It will return None, if the module has no provable statements.
   Otherwise it will return a proof step representing all the module
   with all the sub-steps for the theorems, and so on. *)
let of_module (mule : Tlapm_lib.Module.T.mule) prev : t option =
  match mule.core.stage with
  | Final fin ->
      let prev_obs = obl_by_fp prev in
      let file =
        match Tlapm_lib.Util.query_locus mule with
        | None -> failwith "of_module, has no file location"
        | Some m_locus -> m_locus.file
      in
      let mule_obl (o : Tlapm_lib.Proof.T.obligation) =
        (* Keep only the obligations from the current file. *)
        if_in_file o.obl file @@ fun o_range ->
        (* We will use the fingerprints to retain the
           proof status between the modifications. *)
        let o =
          match o.fingerprint with
          | None ->
              (* `Tlapm_lib.Backend.Prep.prepare_obligation o` works too slow here. *)
              Tlapm_lib.Backend.Fingerprints.write_fingerprint o
          | Some _ -> o
        in
        let o = Obl.of_parsed_obligation o in
        let o = Obl.with_proof_state_from o (Hashtbl.find_opt prev_obs) in
        Some (o_range, o)
      in
      let obs = fin.final_obs in
      let obs = List.filter_map mule_obl (Array.to_list obs) in
      let obs_map = RangeMap.of_list obs in
      let acc = Acc.{ file; obs_map } in
      let step_opt, acc = of_submod mule acc in
      assert (RangeMap.is_empty acc.obs_map);
      step_opt
  | Parsed -> failwith "of_module, parsed"
  | _ -> failwith "of_module, non final"

let with_prover_terminated (ps : t option) p_ref =
  let rec traverse ps =
    let sub = List.map traverse ps.sub in
    let obs = RangeMap.map (Obl.with_prover_terminated p_ref) ps.obs in
    let status_derived = derived_status ps.status_parsed obs sub in
    { ps with sub; obs; status_derived }
  in
  match ps with None -> None | Some ps -> Some (traverse ps)

let with_provers (ps : t option) p_ref obl_id prover_names =
  let rec traverse ps =
    let found = ref false in
    let try_obl obl =
      if (not !found) && Obl.is_for_obl_id obl p_ref obl_id then (
        found := true;
        Obl.with_prover_names p_ref obl_id prover_names obl)
      else obl
    in
    let try_sub ps =
      if not !found then (
        let ps, sub_found = traverse ps in
        if sub_found then found := true;
        ps)
      else ps
    in
    let obs = RangeMap.map try_obl ps.obs in
    let sub = List.map try_sub ps.sub in
    let ps = { ps with obs; sub } in
    (ps, !found)
  in
  match ps with
  | None -> None
  | Some ps ->
      let ps, _ = traverse ps in
      Some ps

let with_prover_result (ps : t option) p_ref (pr : Toolbox.Obligation.t) =
  let rec traverse (ps : t) (pr : Toolbox.Obligation.t) =
    if Range.intersect ps.full_loc pr.loc then
      let apply_to_sub acc sub_ps =
        match acc with
        | true -> (* Already found previously. *) (acc, sub_ps)
        | false -> (
            (* Not found yet, try the depth-first search. *)
            match traverse sub_ps pr with
            | None -> (acc, sub_ps)
            | Some sub_ps -> (true, sub_ps))
      in
      let found, sub = List.fold_left_map apply_to_sub false ps.sub in
      let ps =
        match found with
        | true -> { ps with sub }
        | false ->
            let upd o = Some (Obl.with_prover_obligation p_ref pr o) in
            let obs = RangeMap.update pr.loc upd ps.obs in
            { ps with obs }
      in
      let status_derived = derived_status ps.status_parsed ps.obs ps.sub in
      Some { ps with status_derived }
    else None
  in
  match ps with
  | None -> None
  | Some ps -> (
      match traverse ps pr with None -> Some ps | Some ps -> Some ps)

(* Find the deepest proof step that intersects line-wise with the specified position. *)
let locate_proof_step (ps : t option) (position : Range.Position.t) : t option =
  let rec traverse ps =
    if Range.line_covered ps.full_loc position then
      match List.find_map traverse ps.sub with
      | None -> Some ps
      | Some sub_ps -> Some sub_ps
    else None
  in
  match ps with None -> None | Some ps -> traverse ps

let locate_proof_range (ps : t option) (range : Range.t) : Range.t =
  let ps_from = locate_proof_step ps (Range.from range) in
  let ps_till = locate_proof_step ps (Range.till range) in
  match (ps_from, ps_till) with
  | None, None -> Range.of_all
  | Some ps_from, None -> ps_from.full_loc
  | None, Some ps_till -> ps_till.full_loc
  | Some ps_from, Some ps_till -> Range.join ps_from.full_loc ps_till.full_loc

let is_obl_final (ps : t option) p_ref obl_id =
  let rec traverse ps =
    let with_obl_id r =
      Obl.is_for_obl_id (RangeMap.find r ps.obs) p_ref obl_id
    in
    match RangeMap.find_first_opt with_obl_id ps.obs with
    | None -> List.find_map traverse ps.sub
    | Some (_, o) -> Some (Obl.is_final o)
  in
  match ps with None -> None | Some ps -> traverse ps

let%test_unit "determine proof steps" =
  let mod_file = "test_obl_expand.tla" in
  let mod_text =
    String.concat "\n"
      [
        "---- MODULE test_obl_expand ----";
        "EXTENDS FiniteSetTheorems";
        "THEOREM FALSE";
        "    <1>1. TRUE OBVIOUS";
        "    <1>2. TRUE";
        "    <1>3. TRUE";
        "    <1>q. QED BY <1>1, <1>2, <1>3";
        "THEOREM FALSE";
        "    <1>q. QED";
        "       <2>1. TRUE";
        "       <2>q. QED BY <2>1";
        "  ----- MODULE sub ------";
        "  VARIABLE X";
        "  LEMMA X = X";
        "  =======================";
        "====";
      ]
  in
  let mule =
    Result.get_ok
      (Parser.module_of_string ~content:mod_text ~filename:mod_file
         ~loader_paths:[])
  in
  let ps = of_module mule None in
  match flatten ps with
  | [
      _m_test_obl_expand;
      _th1;
      _th1_11;
      _th1_12;
      _th1_13;
      _th1_1q;
      _th2;
      _th2_1q;
      _th2_1q_21;
      _th2_1q_2q;
      _m_sub;
      _th3;
    ] as all -> (
      List.iteri
        (fun i ps ->
          Format.printf
            "Step[%d]: |obs|=%d, full_loc=%s, step_loc=%s head_loc=%s\n" i
            (RangeMap.cardinal ps.obs)
            (Range.string_of_range ps.full_loc)
            (Range.string_of_range ps.step_loc)
            (Range.string_of_range ps.head_loc))
        all;
      assert (RangeMap.cardinal _th2_1q_2q.obs = 2);
      assert (
        RangeMap.cardinal
          (RangeMap.filter
             (fun _ o -> Obl.role o = Obl.Role.Main)
             _th2_1q_2q.obs)
        = 1);
      let _, _th2_1q_2q_obl = RangeMap.choose _th2_1q_2q.obs in
      match Obl.text_normalized _th2_1q_2q_obl with
      | Some "ASSUME TRUE \nPROVE  FALSE" -> ()
      | Some s -> failwith (Format.sprintf "Unexpected %s" s)
      | None -> failwith "Unexpected none")
  | pss ->
      failwith
        (Format.sprintf "unexpected, number of steps=%d" (List.length pss))

let%test_unit "determine proof steps for USE statements" =
  let mod_file = "test_use.tla" in
  let mod_text =
    String.concat "\n"
      [
        "---- MODULE test_use ----";
        "op == TRUE";
        "USE DEF op";
        "USE TRUE";
        "USE FALSE";
        "HIDE TRUE";
        "THEOREM TRUE";
        "    <1> USE TRUE";
        "    <1> USE FALSE";
        "    <1> HIDE TRUE";
        "    <1> QED";
        "====";
      ]
  in
  let mule =
    Result.get_ok
      (Parser.module_of_string ~content:mod_text ~filename:mod_file
         ~loader_paths:[])
  in
  let ps = of_module mule None in
  match flatten ps with
  | [
      _m_test_use;
      _use_true;
      _use_false;
      _th;
      _th_use_true;
      _th_use_false;
      _th_qed;
    ] as all ->
      List.iteri
        (fun i ps ->
          Format.printf
            "Step[%d]: |obs|=%d, full_loc=%s, step_loc=%s head_loc=%s\n" i
            (RangeMap.cardinal ps.obs)
            (Range.string_of_range ps.full_loc)
            (Range.string_of_range ps.step_loc)
            (Range.string_of_range ps.head_loc))
        all;
      assert (RangeMap.cardinal _use_true.obs = 1);
      assert (RangeMap.cardinal _use_false.obs = 1)
  | pss ->
      failwith
        (Format.sprintf "unexpected, number of steps=%d" (List.length pss))

let%test_unit "check if parsing works with nested local instances." =
  let mod_file = "test_loc_ins.tla" in
  let mod_text =
    String.concat "\n"
      [
        (* Just to keep the items wrapped by line. *)
        "---- MODULE test_loc_ins ----";
        "LOCAL INSTANCE FiniteSets";
        "====";
      ]
  in
  let _mule =
    Result.get_ok
      (Parser.module_of_string ~content:mod_text ~filename:mod_file
         ~loader_paths:[])
  in
  ()
