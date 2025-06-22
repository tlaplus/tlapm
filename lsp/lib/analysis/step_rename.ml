(* cspell:words ints naxs stepno summ *)
open Tlapm_lib
module StepMap = Map.Make (String)

module StepInfo = struct
  type t = { name : string; label_offset : int; step_ranges : Range.t list }

  let make level suffix step_loc =
    let prefix_str = Printf.sprintf "<%d>" level in
    let step_str = Printf.sprintf "<%d>%s" level suffix in
    let range = Range.of_locus_must step_loc in
    let range = Range.of_len range (String.length step_str) in
    {
      name = step_str;
      label_offset = String.length prefix_str;
      step_ranges = [ range ];
    }

  let with_range si range = { si with step_ranges = range :: si.step_ranges }

  let matching_range si range =
    List.find_opt
      (fun r -> Range.intersect range r || Range.touches range r)
      si.step_ranges

  let step_label si =
    String.sub si.name si.label_offset (String.length si.name - si.label_offset)

  let step_label_range si range = Range.crop_line_prefix range si.label_offset
end

exception Found_the_step of StepInfo.t

class step_rename_visitor (at_loc : Range.t) =
  object (self : 'self)
    inherit Module.Visit.map as m_super
    inherit [unit] Proof.Visit.iter as p_super
    val mutable step_map : StepInfo.t StepMap.t = StepMap.empty

    (* Leaf at the `Module.Visit.map as m_super`.
       We will look at `orig_pf`, it is closer to the initial source code. *)
    method! theorem cx name sq naxs pf orig_pf summ =
      (if Range.lines_intersect at_loc (Range.of_wrapped_must orig_pf) then
         (* Only look for steps in proofs that intersects with the user selection. *)
         let pf = orig_pf in
         let ctx = Expr.Visit.empty () in
         self#proof ctx pf);
      m_super#theorem cx name sq naxs pf orig_pf summ

    (* After each proof drop new step names that were defined within the proof.
       But keep the collected ranges for already known steps. *)
    method! proof ctx pf : unit =
      let step_map_before = step_map in
      p_super#proof ctx pf;
      (* While QED steps should have no references, we still make them available
        for the renames to make the behaviour more predictable for the user. *)
      (match pf.core with
      | Steps (_sts, qed) ->
          let qed_stepno = Property.get qed Proof.T.Props.step in
          let qed_locus = Util.get_locus qed in
          self#add_step_opt qed_stepno qed_locus
      | _ -> ());
      (* If we are removing some step from the context, all its references
         are collected already. Check maybe we found what we were looking for. *)
      step_map <-
        StepMap.filter
          (fun step_str step_info ->
            if not (StepMap.mem step_str step_map_before) then
              match StepInfo.matching_range step_info at_loc with
              | None -> false
              | Some _ -> raise (Found_the_step step_info)
            else true)
          step_map

    (* For a step, we put its name to range mapping to the context. *)
    method! step ctx (st : Proof.T.step) =
      let st_stepno = Property.get st Proof.T.Props.step in
      let st_locus = Util.get_locus st in
      self#add_step_opt st_stepno st_locus;
      p_super#step ctx st

    (* Look for step references in all the expressions. *)
    method! expr ctx expr =
      (match expr.core with
      | Expr.T.Opaque step_name ->
          self#add_step_range_opt step_name (Util.get_locus expr)
      | _ -> ());
      p_super#expr ctx expr

    (* Private helper. *)
    method add_step_opt stepno_opt (step_loc : Loc.locus) =
      match stepno_opt with
      | Proof.T.Named (level, suffix, false) ->
          let si = StepInfo.make level suffix step_loc in
          step_map <- StepMap.add si.name si step_map
      | Proof.T.Named (_level, _suffix, true) -> ()
      | Proof.T.Unnamed (_, _) -> ()

    (* Private helper. *)
    method add_step_range_opt (step_name : string) (locus : Loc.locus) =
      match StepMap.find_opt step_name step_map with
      | None -> ()
      | Some si ->
          let si = StepInfo.with_range si (Range.of_locus_must locus) in
          step_map <- StepMap.add step_name si step_map
  end

let find_ranges (at_loc : Range.t) (mule : Module.T.mule) : StepInfo.t option =
  let visitor = new step_rename_visitor at_loc in
  try
    let _ = visitor#tla_module_root mule in
    None
  with Found_the_step si -> Some si

let%test_module "poc renames" =
  (module struct
    let mule =
      let filename = "test_rename_step.tla" in
      let content =
        String.concat "\n"
          [
            "---- MODULE test_rename_step ----";
            "THEOREM TestA == FALSE";
            "    <1>1. TRUE OBVIOUS";
            "    <1>2. TRUE";
            "    <1>q. QED BY <1>1, <1>1, <1>2";
            "====";
          ]
      in
      Result.get_ok
        (Parser.module_of_string ~content ~filename ~loader_paths:[])

    let%test_unit "find <1>1 by step name" =
      match find_ranges (Range.of_ints ~lf:3 ~cf:6 ~lt:3 ~ct:6) mule with
      | None -> assert false
      | Some si ->
          assert (si.name = "<1>1");
          assert (si.label_offset = 3);
          assert (List.length si.step_ranges = 3)

    let%test_unit "find <1>1 by step use" =
      match find_ranges (Range.of_ints ~lf:5 ~cf:18 ~lt:5 ~ct:18) mule with
      | None -> assert false
      | Some si ->
          assert (si.name = "<1>1");
          assert (si.label_offset = 3);
          assert (List.length si.step_ranges = 3)

    let%test_unit "find <1>2" =
      match find_ranges (Range.of_ints ~lf:4 ~cf:6 ~lt:4 ~ct:6) mule with
      | None -> assert false
      | Some si ->
          assert (si.name = "<1>2");
          assert (si.label_offset = 3);
          assert (List.length si.step_ranges = 2)

    let%test_unit "find <1>2 - start col" =
      match find_ranges (Range.of_ints ~lf:4 ~cf:5 ~lt:4 ~ct:5) mule with
      | None -> assert false
      | Some si -> assert (si.name = "<1>2")

    let%test_unit "find <1>2 - end col" =
      match find_ranges (Range.of_ints ~lf:4 ~cf:9 ~lt:4 ~ct:9) mule with
      | None -> assert false
      | Some si -> assert (si.name = "<1>2")

    let%test_unit "find <1>1 -- qed" =
      match find_ranges (Range.of_ints ~lf:5 ~cf:6 ~lt:5 ~ct:6) mule with
      | None -> assert false
      | Some si ->
          assert (si.name = "<1>q");
          assert (si.label_offset = 3);
          assert (List.length si.step_ranges = 1)

    let%test_unit "not found" =
      match find_ranges (Range.of_ints ~lf:2 ~cf:6 ~lt:2 ~ct:6) mule with
      | None -> ()
      | Some _si -> assert false
  end)
