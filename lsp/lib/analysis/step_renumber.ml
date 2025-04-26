open Tlapm_lib

module StepInfo = struct
  type t = {
    name : string;
    target_name : string;
    prefix_len : int;
    ranges : Range.t list;
  }
  [@@deriving show]

  let make_opt stepno_opt (step_loc : Loc.locus) pos : t option =
    match stepno_opt with
    | Proof.T.Named (level, suffix, false) -> (
        let prefix_str = Printf.sprintf "<%d>" level in
        let target_str = Printf.sprintf "<%d>%d" level pos in
        let step_str = Printf.sprintf "<%d>%s" level suffix in
        match Range.of_locus step_loc with
        | None -> None
        | Some range ->
            let range = Range.of_len range (String.length step_str) in
            Some
              {
                name = step_str;
                target_name = target_str;
                prefix_len = String.length prefix_str;
                ranges = [ range ];
              })
    | Proof.T.Named (_level, _suffix, true) -> None
    | Proof.T.Unnamed (_, _) -> None

  let add_range_opt (sis : t list) (step_name : string) (locus : Loc.locus) =
    List.map
      (fun si ->
        if si.name = step_name then
          match Range.of_locus locus with
          | None -> si
          | Some si_range -> { si with ranges = si_range :: si.ranges }
        else si)
      sis
end

exception Found_it of StepInfo.t list

class step_renumber_visitor (at_loc : Range.t) =
  object (self : 'self)
    inherit Module.Visit.map as m_super
    inherit [unit] Proof.Visit.iter as p_super

    (* The nearest found range covering the step with its sub-steps to be re-numbered. *)
    val mutable steps_range : Range.t option = None

    (* Maps step position -> name + all the ranges where it was found.
       This is only set when we found already the steps to renumber. *)
    val mutable step_list : StepInfo.t list = []

    (* We don't have the range at the theorem, so we try to track it by inspecting module units. *)
    method! module_unit cx mu =
      (match Range.of_wrapped mu with
      | None -> ()
      | Some mu_range ->
          steps_range <-
            (match Range.lines_intersect mu_range at_loc with
            | true -> Some mu_range
            | false -> None));
      m_super#module_unit cx mu

    (* Leaf at the `Module.Visit.map as m_super`.
       We will look at `orig_pf`, it is closer to the initial source code. *)
    method! theorem cx name sq naxs pf orig_pf summ =
      (match steps_range with
      | None ->
          (* The [at_loc] is not in this theorem, thus avoid traversing it. *)
          ()
      | Some _ ->
          let ctx = Expr.Visit.empty () in
          self#proof ctx orig_pf);
      m_super#theorem cx name sq naxs pf orig_pf summ

    (* After each proof drop new step names that were defined within the proof.
       But keep the collected ranges for already known steps. *)
    method! proof ctx pf : unit =
      match pf.core with
      | Steps (sts, qed) -> (
          match Range.of_wrapped pf with
          | None -> p_super#proof ctx pf
          | Some pf_range ->
              let pf_at_loc = Range.lines_intersect pf_range at_loc in
              if
                List.is_empty step_list && Option.is_some steps_range
                && not pf_at_loc
              then (
                let sts_info =
                  List.mapi
                    (fun pos st ->
                      let st_stepno = Property.get st Proof.T.Props.step in
                      let st_locus = Util.get_locus st in
                      StepInfo.make_opt st_stepno st_locus (pos + 1))
                    sts
                in
                let qed_info =
                  let qed_stepno = Property.get qed Proof.T.Props.step in
                  let qed_locus = Util.get_locus qed in
                  StepInfo.make_opt qed_stepno qed_locus
                    (List.length sts_info + 1)
                in
                step_list <-
                  List.filter_map
                    (fun x -> x)
                    (List.append sts_info [ qed_info ]);
                p_super#proof ctx pf;
                raise (Found_it step_list))
              else p_super#proof ctx pf)
      | _ -> p_super#proof ctx pf

    (* For a step, we put its name to range mapping to the context. *)
    method! step ctx (st : Proof.T.step) =
      if List.is_empty step_list then
        (* Still looking for the steps to re-number. *)
        match Range.of_wrapped st with
        | None -> steps_range <- None
        | Some st_range ->
            if Range.lines_intersect st_range at_loc then
              steps_range <- Some st_range
            else steps_range <- None
      else
        (* Just looking for references to the steps. *)
        ();
      p_super#step ctx st

    (* Look for step references in all the expressions. *)
    method! expr ctx expr =
      (match expr.core with
      | Expr.T.Opaque step_name ->
          step_list <-
            StepInfo.add_range_opt step_list step_name (Util.get_locus expr)
      | _ -> ());
      p_super#expr ctx expr
  end

let find_ranges (at_loc : Range.t) (mule : Module.T.mule) : StepInfo.t list =
  let visitor = new step_renumber_visitor at_loc in
  try
    let _ = visitor#tla_module_root mule in
    []
  with Found_it step_info_list -> step_info_list

(* let make_renames (sts : StepInfo.t list) =
  let open StepInfo in
  let sts = List.filter (fun st -> st.name != st.target_name) sts in
  List.map (fun st -> ()) sts *)

let%test_module "renumber step tests" =
  (module struct
    let mule =
      let filename = "test_renumber_steps.tla" in
      let content =
        String.concat "\n"
          [
            "---- MODULE test_renumber_steps ----";
            "THEOREM TestA == FALSE";
            "    <1>1. TRUE OBVIOUS";
            "    <1>2. TRUE";
            "       <2>a. TRUE";
            "       <2>q. QED BY <1>1, <2>a";
            "    <1>q. QED BY <1>1, <1>1, <1>2";
            "====";
          ]
      in
      Result.get_ok
        (Parser.module_of_string ~content ~filename ~loader_paths:[])

    let%test_unit "renumber <1> level" =
      match find_ranges (Range.of_ints ~lf:2 ~cf:1 ~lt:2 ~ct:1) mule with
      | [] -> assert false
      | [ st1; st2; st3 ] ->
          assert (st1.prefix_len = 3);
          assert (st1.name = "<1>1");
          assert (st2.name = "<1>2");
          assert (st3.name = "<1>q");
          assert (List.length st1.ranges = 4);
          assert (List.length st2.ranges = 2);
          assert (List.length st3.ranges = 1);
          assert (st1.target_name = "<1>1");
          assert (st2.target_name = "<1>2");
          assert (st3.target_name = "<1>3");
          ()
      | sts ->
          Format.eprintf "sts=%a\n" (Format.pp_print_list StepInfo.pp) sts;
          assert false

    let%test_unit "renumber <1>2" =
      match find_ranges (Range.of_ints ~lf:4 ~cf:5 ~lt:4 ~ct:5) mule with
      | [] -> assert false
      | [ st1; st2 ] ->
          assert (st1.prefix_len = 3);
          assert (st1.name = "<2>a");
          assert (st2.name = "<2>q");
          assert (List.length st1.ranges = 2);
          assert (List.length st2.ranges = 1);
          assert (st1.target_name = "<2>1");
          assert (st2.target_name = "<2>2");
          ()
      | sts ->
          Format.eprintf "sts=%a\n" (Format.pp_print_list StepInfo.pp) sts;
          assert false

    let%test_unit "out of theorem" =
      match find_ranges (Range.of_ints ~lf:1 ~cf:1 ~lt:1 ~ct:1) mule with
      | [] -> ()
      | sts ->
          Format.eprintf "sts=%a\n" (Format.pp_print_list StepInfo.pp) sts;
          assert false

    let%test_unit "leaf step" =
      match find_ranges (Range.of_ints ~lf:3 ~cf:5 ~lt:3 ~ct:5) mule with
      | [] -> ()
      | sts ->
          Format.eprintf "sts=%a\n" (Format.pp_print_list StepInfo.pp) sts;
          assert false
  end)
