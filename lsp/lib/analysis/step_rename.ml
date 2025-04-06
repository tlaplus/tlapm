(* cspell:words ints naxs stepno summ *)
open Tlapm_lib
module StepMap = Map.Make (String)

exception Found_the_step of string * int * Range.t list

class step_rename_visitor (at_loc : Range.t) =
  object (self : 'self)
    inherit Module.Visit.map as m_super
    inherit [unit] Proof.Visit.iter as p_super
    val mutable step_map : (int * Range.t list) StepMap.t = StepMap.empty

    (* Leaf at the `Proof.Visit.iter as p_super`.
       We will look at `orig_pf`, it is closer to the initial source code. *)
    method! theorem cx name sq naxs _pf orig_pf summ =
      let pf = orig_pf in
      let ctx = Expr.Visit.empty () in
      self#proof ctx pf;
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
      let matches range = Range.intersect range at_loc in
      step_map <-
        StepMap.filter
          (fun step_str (label_offset, step_ranges) ->
            if not (StepMap.mem step_str step_map_before) then (
              if List.exists matches step_ranges then
                raise (Found_the_step (step_str, label_offset, step_ranges));
              false)
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
          let prefix_str = Printf.sprintf "<%d>" level in
          let step_str = Printf.sprintf "<%d>%s" level suffix in
          let range = Range.of_locus_must step_loc in
          let range = Range.of_len range (String.length step_str) in
          let step_info = (String.length prefix_str, [ range ]) in
          step_map <- StepMap.add step_str step_info step_map
      | Proof.T.Named (_level, _suffix, true) -> ()
      | Proof.T.Unnamed (_, _) -> ()

    (* Private helper. *)
    method add_step_range_opt (step_name : string) (locus : Loc.locus) =
      match StepMap.find_opt step_name step_map with
      | None -> ()
      | Some (label_offset, ranges) ->
          let new_info = (label_offset, Range.of_locus_must locus :: ranges) in
          step_map <- StepMap.add step_name new_info step_map
  end

let find_ranges (at_loc : Range.t) (mule : Module.T.mule) :
    (string * int * Range.t list) option =
  let visitor = new step_rename_visitor at_loc in
  try
    let _ = visitor#tla_module_root mule in
    None
  with Found_the_step (step_str, label_offset, step_ranges) ->
    Some (step_str, label_offset, step_ranges)

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
      | Some (st_name, st_lb_o, st_ranges) ->
          assert (st_name = "<1>1");
          assert (st_lb_o = 3);
          assert (List.length st_ranges = 3);
          ()

    let%test_unit "find <1>1 by step use" =
      match find_ranges (Range.of_ints ~lf:5 ~cf:18 ~lt:5 ~ct:18) mule with
      | None -> assert false
      | Some (st_name, st_lb_o, st_ranges) ->
          assert (st_name = "<1>1");
          assert (st_lb_o = 3);
          assert (List.length st_ranges = 3);
          ()

    let%test_unit "find <1>2" =
      match find_ranges (Range.of_ints ~lf:4 ~cf:6 ~lt:4 ~ct:6) mule with
      | None -> assert false
      | Some (st_name, st_lb_o, st_ranges) ->
          assert (st_name = "<1>2");
          assert (st_lb_o = 3);
          assert (List.length st_ranges = 2);
          ()

    let%test_unit "find <1>1 -- qed" =
      match find_ranges (Range.of_ints ~lf:5 ~cf:6 ~lt:5 ~ct:6) mule with
      | None -> assert false
      | Some (st_name, st_lb_o, st_ranges) ->
          assert (st_name = "<1>q");
          assert (st_lb_o = 3);
          assert (List.length st_ranges = 1);
          ()

    let%test_unit "not found" =
      match find_ranges (Range.of_ints ~lf:2 ~cf:6 ~lt:2 ~ct:6) mule with
      | None -> ()
      | Some (_st_name, _st_lb_o, _st_ranges) -> assert false
  end)

let step_label step_name label_offset =
  String.sub step_name label_offset (String.length step_name - label_offset)

let step_label_range range label_offset =
  Range.crop_line_prefix range label_offset
