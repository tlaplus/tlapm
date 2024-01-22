open Util
open Tlapm_lsp_prover
open Tlapm_lsp_prover.ToolboxProtocol
open Tlapm_lib.Backend

(** We categorize the proof steps just to make the presentation in the UI clearer. *)
module Kind = struct
  type t = Module | Struct | Leaf

  let to_string = function
    | Module -> "module"
    | Struct -> "struct"
    | Leaf -> "leaf"
end

type t = {
  kind : Kind.t;
      (** Kind/Type of this proof step.
          We want to show the proof steps differently based in its type. *)
  status_parsed : Proof_status.t option;
      (** Status derived at the parse time, if any.
          This is for the omitted or error cases. *)
  status_derived : Proof_status.t;
      (** Derived status.
          Here we sum-up the states from all the related obligations and sub-steps. *)
  step_loc : TlapmRange.t;
      (** Location if the entire step.
          This doesn't include the BY statement, but includes
          the sub-steps and the BY proof excluding the used facts. *)
  head_loc : TlapmRange.t;
      (** The location of the proof sequent.
          It is always contained within the [step_loc].
          This is shown as a step in the UI. *)
  full_loc : TlapmRange.t;
      (** [step_loc] plus all the BY facts included.
          If an obligation is in [full_loc] but not in the [step_loc],
          we consider it supplementary (will be shown a bit more hidden). *)
  obs : Obl.t RangeMap.t;
      (** Obligations associated with this step.
          Here we include all the obligations fitting into [full_loc],
          but not covered by any of the [sub] steps. *)
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
   constructs the proof step and returns obligations that left unassigned. *)
let make ~kind ?status_parsed ~step_loc ?head_loc ~full_loc ~sub obs_map =
  let intersects_with_full_loc obl_loc _ =
    TlapmRange.intersect obl_loc full_loc
  in
  let intersects_with_step_loc obl_loc =
    TlapmRange.intersect obl_loc step_loc
  in
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
    | None -> TlapmRange.(of_points (from step_loc) (from step_loc))
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
  let range = TlapmRange.as_lsp_range ps.head_loc in
  let state = Proof_status.to_string ps.status_derived in
  let hover = Proof_status.to_message ps.status_derived in
  Tlapm_lsp_structs.TlapsProofStateMarker.make ~range ~state ~hover

let as_lsp_tlaps_proof_step_details uri ps =
  let kind = Kind.to_string ps.kind in
  let location =
    LspT.Location.create ~uri ~range:(TlapmRange.as_lsp_range ps.full_loc)
  in
  let obligations =
    List.map
      (fun (_, o) -> Obl.as_lsp_tlaps_proof_obligation_state o)
      (RangeMap.to_list ps.obs)
  in
  Tlapm_lsp_structs.TlapsProofStepDetails.make ~kind ~location ~obligations

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

(* TODO: Make it more local? *)
let opt_range prop = TlapmRange.of_locus_opt (Tlapm_lib.Util.query_locus prop)
let get_range prop = Option.get (opt_range prop)

module Acc = struct
  type t = { file : string; obs_map : Obl.t RangeMap.t }

  let some (x, acc) = (Some x, acc)
  let for_file file acc = file = acc.file
end

let if_in_file wrapped file fn =
  match Tlapm_lib.Util.query_locus wrapped with
  | Some loc when loc.file = file -> fn (TlapmRange.of_locus_must loc)
  | Some _ -> None
  | None -> None

let if_in_file_acc wrapped acc fn =
  match Tlapm_lib.Util.query_locus wrapped with
  | Some loc when Acc.for_file loc.file acc ->
      fn (TlapmRange.of_locus_must loc) acc
  | Some _ -> (None, acc)
  | None -> (None, acc)

let rec of_proof step_loc sq_range (proof : Tlapm_lib.Proof.T.proof) acc :
    t * Acc.t =
  let open Tlapm_lib in
  let kind, sub, status_parsed, suppl_loc, acc =
    match Property.unwrap proof with
    | Proof.T.Obvious -> (Kind.Leaf, [], None, None, acc)
    | Proof.T.Omitted _omission ->
        (* TODO: Distinguish the implicit/explicit. *)
        (Kind.Leaf, [], Some Proof_status.Omitted, None, acc)
    | Proof.T.By (usable, _only) ->
        let join_ranges base list =
          List.fold_left
            (fun acc d ->
              match opt_range d with
              | None -> acc
              | Some r -> TlapmRange.join acc r)
            base list
        in
        let suppl_range = step_loc in
        let suppl_range = join_ranges suppl_range usable.defs in
        let suppl_range = join_ranges suppl_range usable.facts in
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
            (fun acc sub_ps -> TlapmRange.join acc sub_ps.full_loc)
            step_loc sub
        in
        (Kind.Struct, sub, None, Some suppl_loc, acc)
    | Proof.T.Error _ -> (Kind.Leaf, [], Some Proof_status.Failed, None, acc)
  in
  let head_loc =
    match sq_range with
    | Some sq_range ->
        Some TlapmRange.(of_points (from step_loc) (till sq_range))
    | None -> None
  in
  let full_loc =
    match suppl_loc with
    | None -> step_loc
    | Some suppl_loc -> TlapmRange.join step_loc suppl_loc
  in
  let st, obs_map =
    make ~kind ?status_parsed ~step_loc ?head_loc ~full_loc ~sub acc.obs_map
  in
  (st, { acc with obs_map })

and of_step (step : Tlapm_lib.Proof.T.step) acc : t option * Acc.t =
  let open Tlapm_lib in
  match Property.unwrap step with
  | Proof.T.Hide _ -> (None, acc)
  | Proof.T.Define _ -> (None, acc)
  | Proof.T.Assert (sequent, proof) ->
      Acc.some (of_proof (get_range step) (opt_range sequent.active) proof acc)
  | Proof.T.Suffices (sequent, proof) ->
      Acc.some (of_proof (get_range step) (opt_range sequent.active) proof acc)
  | Proof.T.Pcase (expr, proof) ->
      Acc.some (of_proof (get_range step) (opt_range expr) proof acc)
  | Proof.T.Pick (_bounds, expr, proof) ->
      Acc.some (of_proof (get_range step) (opt_range expr) proof acc)
  | Proof.T.Use (_, _) -> (None, acc)
  | Proof.T.Have _ -> (None, acc)
  | Proof.T.Take _ -> (None, acc)
  | Proof.T.Witness _ -> (None, acc) (* TODO: Form a step for this. *)
  | Proof.T.Forget _ -> (None, acc)

and of_qed_step (qed_step : Tlapm_lib.Proof.T.qed_step) acc : t * Acc.t =
  match Tlapm_lib.Property.unwrap qed_step with
  | Tlapm_lib.Proof.T.Qed proof ->
      let open Tlapm_lib in
      let qed_loc = Property.query qed_step Proof.Parser.qed_loc_prop in
      let qed_range = TlapmRange.of_locus_opt qed_loc in
      of_proof (get_range qed_step) qed_range proof acc

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
      Acc.some (of_proof mod_unit_loc (opt_range sq.active) prf_orig acc)
  | Submod sm -> of_submod sm acc
  | Mutate _ -> (None, acc)
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
          | None -> Fingerprints.write_fingerprint o
          | Some _ -> o
        in
        let o = Obl.of_parsed_obligation (Some o) Proof_status.Pending in
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

let with_prover_result (ps : t option) p_ref (pr : tlapm_obligation) =
  let rec traverse (ps : t) (pr : tlapm_obligation) =
    if TlapmRange.intersect ps.full_loc pr.loc then
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
let locate_proof_step (ps : t option) (position : TlapmRange.Position.t) :
    t option =
  let rec traverse ps =
    if TlapmRange.line_covered ps.full_loc position then
      match List.find_map traverse ps.sub with
      | None -> Some ps
      | Some sub_ps -> Some sub_ps
    else None
  in
  match ps with None -> None | Some ps -> traverse ps

let locate_proof_range (ps : t option) (range : TlapmRange.t) : TlapmRange.t =
  let ps_from = locate_proof_step ps (TlapmRange.from range) in
  let ps_till = locate_proof_step ps (TlapmRange.till range) in
  match (ps_from, ps_till) with
  | None, None -> TlapmRange.of_all
  | Some ps_from, None -> ps_from.full_loc
  | None, Some ps_till -> ps_till.full_loc
  | Some ps_from, Some ps_till ->
      TlapmRange.join ps_from.full_loc ps_till.full_loc

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
  let mule = Result.get_ok (Tlapm_lib.module_of_string mod_text mod_file) in
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
            (TlapmRange.string_of_range ps.full_loc)
            (TlapmRange.string_of_range ps.step_loc)
            (TlapmRange.string_of_range ps.head_loc))
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
