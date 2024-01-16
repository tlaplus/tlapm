open Util
open Tlapm_lsp_prover
open Tlapm_lsp_prover.ToolboxProtocol

type s = Proved | Failed | Omitted | Missing | Pending | Progress

let s_of_tlapm_obl_state = function
  | ToolboxProtocol.ToBeProved -> Progress
  | ToolboxProtocol.BeingProved -> Pending
  | ToolboxProtocol.Normalized -> Progress
  | ToolboxProtocol.Proved -> Proved
  | ToolboxProtocol.Failed -> Failed
  | ToolboxProtocol.Interrupted -> Failed
  | ToolboxProtocol.Trivial -> Proved
  | ToolboxProtocol.Unknown _ -> Failed

let message_of_s = function
  | Failed -> "Proof failed."
  | Missing -> "Proof missing."
  | Omitted -> "Proof omitted."
  | Progress -> "Proving in progress."
  | Pending -> "Proof pending."
  | Proved -> "Proof checked successfully."

let order_of_s = function
  | Failed -> 0
  | Missing -> 1
  | Omitted -> 2
  | Progress -> 3
  | Pending -> 4
  | Proved -> 5

let s_of_order = function
  | 0 -> Failed
  | 1 -> Missing
  | 2 -> Omitted
  | 3 -> Progress
  | 4 -> Pending
  | 5 -> Proved
  | _ -> failwith "Impossible order"

let min_of_s a b = s_of_order (min (order_of_s a) (order_of_s b))

type t = {
  loc : TlapmRange.t option; (* Location if the entire step. *)
  hdr_loc : TlapmRange.t option; (* The location of the proof sequent.*)
  obl_loc : TlapmRange.t option; (* Where the obligation exists. *)
  obl_parsed : Obl_parsed.t; (* Obligation from the parser, if exist. *)
  obl_proofs : Obl_proofs.t option; (* The corresponding obligation info. *)
  state : s;
  sub : t list;
}

let min_s_of_t_list sub =
  match sub with
  | [] -> None
  | (first : t) :: _ ->
      let state =
        List.fold_left
          (fun st (sub : t) -> min_of_s st sub.state)
          first.state sub
      in
      Some state

let yojson_of_s = function
  | Proved -> `String "proved"
  | Failed -> `String "failed"
  | Omitted -> `String "omitted"
  | Missing -> `String "missing"
  | Pending -> `String "pending"
  | Progress -> `String "progress"

let yojson_of_t (t : t) =
  match t.hdr_loc with
  | None -> None
  | Some hdr_loc ->
      let obj =
        `Assoc
          [
            ("range", LspT.Range.yojson_of_t (TlapmRange.as_lsp_range hdr_loc));
            ("state", yojson_of_s t.state);
            ("hover", `String (message_of_s t.state));
          ]
      in
      Some obj

let tlaps_proof_obligation_state_of_t uri ps =
  let open Tlapm_lsp_structs in
  match ps.loc with
  | None -> None
  | Some ps_loc ->
      let some_str s = match s with None -> "?" | Some s -> s in
      let location =
        Location.make ~uri ~range:(TlapmRange.as_lsp_range ps_loc)
      in
      let obligation = some_str (Obl_parsed.text_normalized ps.obl_parsed) in
      let results =
        match ps.obl_proofs with
        | None -> []
        | Some oi ->
            List.map
              (fun (_, o) ->
                let prover = some_str o.prover in
                let status = message_of_s (s_of_tlapm_obl_state o.status) in
                let meth = some_str o.meth in
                let reason = o.reason in
                let obligation = o.obl in
                TlapsProofObligationResult.make ~prover ~meth ~status ~reason
                  ~obligation)
              (StrMap.to_list oi.by_prover)
      in
      Some (TlapsProofObligationState.make ~location ~obligation ~results)

let rec flatten pss =
  List.flatten (List.map (fun ps -> ps :: flatten ps.sub) pss)

let q_range prop = TlapmRange.of_locus_opt (Tlapm_lib.Util.query_locus prop)

type of_module_t = {
  file : string;
  obs_map : Tlapm_lib.Proof.T.obligation RangeMap.t;
}

let rec of_provable stm_range seq_range (proof : Tlapm_lib.Proof.T.proof) acc =
  (* Here we have to check the file of the proof. After the document was parsed and
     normalized, proofs from other documents are included here as well. *)
  match Tlapm_lib.Util.query_locus proof with
  | Some proof_loc when proof_loc.file = acc.file ->
      let sub, min_st, obl_loc = of_proof proof acc in
      let hdr_loc =
        match (stm_range, seq_range) with
        | Some stm_r, Some seq_r ->
            Some
              (TlapmRange.of_points (TlapmRange.from stm_r)
                 (TlapmRange.till seq_r))
        | Some stm_r, None -> Some stm_r
        | None, Some seq_r -> Some seq_r
        | None, None -> None
      in
      let obl_parsed =
        match obl_loc with
        | None -> Obl_parsed.make None
        | Some obl_loc ->
            Obl_parsed.make (RangeMap.find_opt obl_loc acc.obs_map)
      in
      [
        {
          loc = stm_range;
          hdr_loc;
          obl_loc;
          obl_parsed;
          obl_proofs = None;
          state = min_st;
          sub;
        };
      ]
  | _ -> []

and of_proof (proof : Tlapm_lib.Proof.T.proof) acc =
  let open Tlapm_lib in
  let obl_loc = q_range proof in
  match Property.unwrap proof with
  | Proof.T.Obvious -> ([], Pending, obl_loc)
  | Proof.T.Omitted _ -> ([], Omitted, obl_loc)
  | Proof.T.By (_, _) -> ([], Pending, obl_loc)
  | Proof.T.Steps (steps, qed_step) -> (
      let sub = List.map (fun s -> of_step s acc) steps in
      let qed = of_qed_step qed_step acc in
      let sub = List.flatten (sub @ [ qed ]) in
      match min_s_of_t_list sub with
      | None -> (sub, Failed, obl_loc)
      | Some min_s -> (sub, min_s, obl_loc))
  | Proof.T.Error _ -> ([], Failed, obl_loc)

and of_step (step : Tlapm_lib.Proof.T.step) acc =
  let open Tlapm_lib in
  match Property.unwrap step with
  | Proof.T.Hide _ -> []
  | Proof.T.Define _ -> []
  | Proof.T.Assert (sequent, proof) ->
      of_provable (q_range step) (q_range sequent.active) proof acc
  | Proof.T.Suffices (sequent, proof) ->
      of_provable (q_range step) (q_range sequent.active) proof acc
  | Proof.T.Pcase (expr, proof) ->
      of_provable (q_range step) (q_range expr) proof acc
  | Proof.T.Pick (_bounds, expr, proof) ->
      of_provable (q_range step) (q_range expr) proof acc
  | Proof.T.Use (_, _) -> []
  | Proof.T.Have _ -> []
  | Proof.T.Take _ -> []
  | Proof.T.Witness _ -> [] (* TODO: Form a step for this. *)
  | Proof.T.Forget _ -> []

and of_qed_step (qed_step : Tlapm_lib.Proof.T.qed_step) acc =
  match Tlapm_lib.Property.unwrap qed_step with
  | Tlapm_lib.Proof.T.Qed proof ->
      let open Tlapm_lib in
      let qed_loc = Property.query qed_step Proof.Parser.qed_loc_prop in
      let qed_range = TlapmRange.of_locus_opt qed_loc in
      of_provable (q_range qed_step) qed_range proof acc

and of_module (mule : Tlapm_lib.Module.T.mule) =
  match mule.core.stage with
  | Final fin ->
      let file =
        match Tlapm_lib.Util.query_locus mule with
        | None -> failwith "of_module, has no file location"
        | Some m_locus -> m_locus.file
      in
      let obs = fin.final_obs in
      let obs_map =
        RangeMap.of_list
          (List.filter_map
             (fun (o : Tlapm_lib.Proof.T.obligation) ->
               (* Keep only the obligations from the current file. *)
               match Tlapm_lib.Util.query_locus o.obl with
               | None -> None
               | Some o_locus -> (
                   match TlapmRange.of_locus o_locus with
                   | Some o_range ->
                       if o_locus.file = file then Some (o_range, o) else None
                   | None -> None))
             (Array.to_list obs))
      in
      let acc = { file; obs_map } in
      of_module_rec [] mule acc
  | Parsed -> failwith "of_module, parsed"
  | _ -> failwith "of_module, non final"

and of_module_rec pss (mule : Tlapm_lib.Module.T.mule) acc =
  let open Tlapm_lib in
  let mule_ = Property.unwrap mule in
  List.fold_left
    (fun pss mod_unit ->
      let open Tlapm_lib.Module.T in
      match Property.unwrap mod_unit with
      | Constants _ -> pss
      | Recursives _ -> pss
      | Variables _ -> pss
      | Definition _ -> pss
      | Axiom _ -> pss
      | Theorem (_name, sq, _naxs, _prf, prf_orig, _sum) ->
          let ps =
            of_provable (q_range mod_unit) (q_range sq.active) prf_orig acc
          in
          List.append pss ps
      | Submod sm -> of_module_rec pss sm acc
      | Mutate _ -> pss
      | Anoninst _ -> pss)
    pss mule_.body

let rec with_tlapm_obligation (pss : t list) (oi : Obl_proofs.t) =
  (* Here we derive a state for a structured proof step as a worst state of its steps. *)
  let with_opt_min_s ps opt_sub_min_s =
    match opt_sub_min_s with
    | None -> ps
    | Some sub_min_s -> { ps with state = sub_min_s }
  in
  let upd ps =
    let sub = with_tlapm_obligation ps.sub oi in
    let sub_min_s = min_s_of_t_list sub in
    let ps = { ps with sub } in
    match ps.obl_loc with
    | None -> with_opt_min_s ps sub_min_s
    | Some ps_obl_loc ->
        if TlapmRange.from ps_obl_loc = TlapmRange.from (Obl_proofs.loc oi) then
          let state = s_of_tlapm_obl_state (Obl_proofs.latest oi).status in
          with_opt_min_s { ps with state; obl_proofs = Some oi } sub_min_s
        else with_opt_min_s ps sub_min_s
  in
  List.map upd pss

let with_tlapm_obligations (pss : t list) (ois : Obl_proofs.t OblMap.t) =
  OblMap.fold (fun _ ob pss -> with_tlapm_obligation pss ob) ois pss

let locate_proof_range (pss : t list) (input : TlapmRange.t) : TlapmRange.t =
  let rec collect pss =
    let for_each_ps_with_loc ps ps_loc =
      match TlapmRange.lines_intersect ps_loc input with
      | true -> (
          match collect ps.sub with
          | [] -> Some [ ps_loc ]
          | first :: _ as sub_locs -> (
              match TlapmRange.(line_from input < line_from first) with
              | true -> Some [ ps_loc ]
              | false -> Some sub_locs))
      | false -> None
    in
    let for_each_ps ps =
      match ps.loc with
      | None -> None
      | Some ps_loc -> for_each_ps_with_loc ps ps_loc
    in
    List.flatten (List.filter_map for_each_ps pss)
  in
  let pss_locs = collect pss in
  TlapmRange.lines_covered_or_all input pss_locs

let find_proof_step (pss : t list) (input : TlapmRange.t) =
  let rec find_first pss =
    let for_each_ps_with_loc ps ps_loc =
      match TlapmRange.lines_intersect ps_loc input with
      | true -> (
          match find_first ps.sub with
          | None -> Some ps
          | Some first -> Some first)
      | false -> None
    in
    let for_each_ps ps =
      match ps.loc with
      | None -> None
      | Some ps_loc -> for_each_ps_with_loc ps ps_loc
    in
    List.find_map for_each_ps pss
  in
  find_first pss

let%test_module "experiment with visitors" =
  (module struct
    class p_visitor =
      object (self : 'self)
        inherit [string] Tlapm_lib.Proof.Visit.map as super

        val ps : t =
          {
            sub = [];
            loc = None;
            state = Omitted;
            hdr_loc = None;
            obl_loc = None;
            obl_proofs = None;
            obl_parsed = Obl_parsed.make None;
          }

        (* The entry point. *)
        method visit (prf : Tlapm_lib.Proof.T.proof) =
          let _ = self#proof ("-", Tlapm_lib.Util.Deque.empty) prf in
          ps

        method! private proof (ident, cx) prf =
          Format.printf "%sP_Visit.proof\n" ident;
          super#proof (ident ^ " ", cx) prf

        method! private step (ident, cx) st =
          Format.printf "%sP_Visit.step\n" ident;
          let (_, cx), st = super#step (ident ^ " ", cx) st in
          ((ident, cx), st)
      end

    class m_visitor mod_file =
      object (self : 'self)
        inherit Tlapm_lib.Module.Visit.map as super
        val mutable pss : t list = []

        (* The entry point. *)
        method visit (mule : Tlapm_lib.Module.T.mule) =
          let cx = Tlapm_lib.Util.Deque.empty in
          let _ = self#module_units cx mule.core.body in
          pss

        (* Only consider element form the current file. *)
        method! private module_unit cx mu =
          match Tlapm_lib.Util.query_locus mu with
          | None -> (cx, mu)
          | Some loc -> (
              match loc.file = mod_file with
              | true -> super#module_unit cx mu
              | false -> (cx, mu))

        (* Each theorem is a proof step, which might have other sub-steps. *)
        method! private theorem cx name sq naxs prf prf_orig summ =
          Format.printf "M_Visit.theorem s\n";
          let p_visitor = new p_visitor in
          let _ = p_visitor#visit prf_orig in
          super#theorem cx name sq naxs prf prf_orig summ

        (* Process modules recursively, collect steps into a single list. *)
        method! private submod cx tla_module =
          let _ = self#module_units cx tla_module.core.body in
          super#submod cx tla_module
      end

    (* TODO: Incomplete: Check if
       - Theorems are found.
       - steps are determined.
       - Submodules handled.
       - Extended modules not included.
    *)
    let%test_unit "determine proof steps" =
      let mod_file = "test_obl_expand.tla" in
      let mod_text =
        String.concat "\n"
          [
            "---- MODULE test_obl_expand ----";
            "EXTENDS FiniteSetTheorems";
            "THEOREM FALSE";
            "    <1>1. TRUE";
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
      Format.printf "\n\n";
      let mule = Result.get_ok (Tlapm_lib.module_of_string mod_text mod_file) in
      let m_visitor = new m_visitor mod_file in
      let _pss = m_visitor#visit mule in
      ()
  end)

let%test_unit "determine proof steps" =
  let mod_file = "test_obl_expand.tla" in
  let mod_text =
    String.concat "\n"
      [
        "---- MODULE test_obl_expand ----";
        "EXTENDS FiniteSetTheorems";
        "THEOREM FALSE";
        "    <1>1. TRUE";
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
  let pss = of_module mule in
  match flatten pss with
  | [
   _th1;
   _th1_11;
   _th1_12;
   _th1_13;
   _th1_1q;
   _th2;
   _th2_1q;
   _th2_1q_21;
   _th2_1q_2q;
   _th3;
  ] -> (
      match Obl_parsed.text_normalized _th2_1q_2q.obl_parsed with
      | Some "ASSUME TRUE \nPROVE  FALSE" -> ()
      | Some s -> failwith (Format.sprintf "Unexpected %s" s)
      | None -> failwith "Unexpected none")
  | pss ->
      failwith
        (Format.sprintf "unexpected, number of steps=%d" (List.length pss))
