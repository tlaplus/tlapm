open Tlapm_lib

let explain_obl_direct (active : Expr.T.expr) (context : Expr.T.hyp Deque.dq) :
    string list =
  match Backend.Prep.have_fact context active with
  | true -> [ "Direct proof from assumptions" ]
  | false -> []

let explain_obl_conj_intro (active : Expr.T.expr)
    (context : Expr.T.hyp Deque.dq) : string list =
  match active.core with
  | Expr.T.Apply (op, args) -> (
      match op.core with
      | Expr.T.Internal Builtin.Conj -> (
          let all_found =
            List.for_all (fun arg -> Backend.Prep.have_fact context arg) args
          in
          match all_found with true -> [ "/\\-intro" ] | false -> [])
      | _ -> [])
  | _ -> []

let explain_obl_disj_intro (active : Expr.T.expr)
    (context : Expr.T.hyp Deque.dq) : string list =
  match active.core with
  | Expr.T.Apply (op, args) -> (
      match op.core with
      | Expr.T.Internal Builtin.Disj -> (
          let any_found =
            List.exists (fun arg -> Backend.Prep.have_fact context arg) args
          in
          match any_found with true -> [ "\\/-intro" ] | false -> [])
      | _ -> [])
  | _ -> []

let explain_obl (obl : Proof.T.obligation) : string list =
  let obl = Backend.Prep.expand_defs obl in
  let active = obl.obl.core.active in
  let context = obl.obl.core.context in
  List.flatten
    (List.map
       (fun f -> f active context)
       [ explain_obl_direct; explain_obl_conj_intro; explain_obl_disj_intro ])

let test_util_get_expl (theorem : string list) : string list =
  let filename = "test_step_explainer.tla" in
  let content =
    "---- MODULE test_step_explainer ----\n" ^ String.concat "\n" theorem
    ^ "===="
  in
  let mule =
    Result.get_ok (Parser.module_of_string ~content ~filename ~loader_paths:[])
  in
  match mule.core.stage with
  | Module.T.Special | Module.T.Parsed | Module.T.Flat -> []
  | Module.T.Final { final_obs; _ } -> explain_obl final_obs.(0)

let%test_unit "explain conj direct intro" =
  let theorem =
    [
      "THEOREM TestA == ASSUME NEW a, NEW b, a, b PROVE a /\\ b";
      "    <1>1. a /\\ b OBVIOUS";
      "    <1>q. QED BY <1>1";
    ]
  in
  match test_util_get_expl theorem with
  | list ->
      assert (String.concat ";" list = "Direct proof from assumptions;/\\-intro")

let%test_unit "explain conj intro" =
  let theorem =
    [
      "THEOREM TestA == ASSUME NEW a, NEW b, a, b PROVE a /\\ b";
      "    <1>1. a OBVIOUS";
      "    <1>2. b OBVIOUS";
      "    <1>q. QED BY <1>1, <1>2";
    ]
  in
  match test_util_get_expl theorem with
  | list -> assert (String.concat ";" list = "/\\-intro")

let%test_unit "explain disj direct intro" =
  let theorem =
    [
      "THEOREM TestA == ASSUME NEW a, NEW b, a, b PROVE a \\/ b";
      "    <1>1. a \\/ b OBVIOUS";
      "    <1>q. QED BY <1>1";
    ]
  in
  match test_util_get_expl theorem with
  | list ->
      assert (String.concat ";" list = "Direct proof from assumptions;\\/-intro")

let%test_unit "explain disj intro left" =
  let theorem =
    [
      "THEOREM TestA == ASSUME NEW a, NEW b, a PROVE a \\/ b";
      "    <1>1. a OBVIOUS";
      "    <1>q. QED BY <1>1";
    ]
  in
  match test_util_get_expl theorem with
  | list -> assert (String.concat ";" list = "\\/-intro")

let%test_unit "explain disj intro right" =
  let theorem =
    [
      "THEOREM TestA == ASSUME NEW a, NEW b, b PROVE a \\/ b";
      "    <1>1. b OBVIOUS";
      "    <1>q. QED BY <1>1";
    ]
  in
  match test_util_get_expl theorem with
  | list -> assert (String.concat ";" list = "\\/-intro")

(* let%test_module "poc: explain direct" =
  (module struct
    let mule =
      let filename = "test_rename_step.tla" in
      let content =
        String.concat "\n"
          [
            "---- MODULE test_rename_step ----";
            "THEOREM TestA == ASSUME NEW a, NEW b, a, b PROVE a /\\ b";
            "    <1>1. a /\\ b OBVIOUS";
            "    <1>q. QED BY <1>1";
            "====";
          ]
      in
      Result.get_ok
        (Parser.module_of_string ~content ~filename ~loader_paths:[])

    let%test_unit "experimenting" =
      let vpp = new Debug.visitor_pp in
      vpp#scope_str "test" (fun () ->
          let open Proof.T in
          match mule.core.stage with
          | Module.T.Special | Module.T.Parsed | Module.T.Flat -> ()
          | Module.T.Final { final_obs; _ } ->
              Array.iter
                (fun obl ->
                  let obl = Backend.Prep.expand_defs obl in
                  vpp#scope
                    (Format.dprintf "Obl[%a %a]{@[<hov>%t@]}"
                       Loc.pp_locus_compact_opt (Util.query_locus obl.obl)
                       Proof.T.pp_obligation_kind obl.kind)
                  @@ fun () ->
                  let active = obl.obl.core.active in
                  let context = obl.obl.core.context in
                  let act_in_ctx = Backend.Prep.have_fact context active in
                  vpp#add
                    (Format.dprintf "active{pp=%t,expr=%a,have=%b}"
                       (fun fmt ->
                         Expr.Fmt.pp_print_expr (context, Ctx.dot) fmt active)
                       Debug.pp_expr active act_in_ctx);
                  vpp#scope (Format.dprintf "context{@[<v>%t@]}") @@ fun () ->
                  Deque.iter
                    (fun hyp_i (hyp : Expr.T.hyp) ->
                      vpp#scope (Format.dprintf "Hyp-%d{@[%t@]}" hyp_i)
                      @@ fun () ->
                      vpp#add
                        (Format.dprintf "[loc=%a]" Loc.pp_locus_compact_opt
                           (Util.query_locus hyp));
                      vpp#add (Format.dprintf "[val=%a]" Debug.pp_hyp hyp);

                      let open Expr.T in
                      (* TODO: ix_hyp is incorrect, because we have to increse ix'es when pushing an expression upwards. *)
                      let ix_hyp =
                        match hyp.core with
                        | Fresh (_, _, _, _)
                        | FreshTuply (_, _)
                        | Flex _
                        | Defn (_, _, _, _) ->
                            None
                        | Fact (hyp_expr, _, _) -> (
                            match hyp_expr.core with
                            | Ix ix -> Deque.nth context (hyp_i - ix)
                            | _ -> None)
                      in
                      let hyp_at_active =
                        Expr.Subst.app_hyp
                          (Expr.Subst.shift (Deque.size context - hyp_i))
                          hyp
                      in
                      vpp#add
                        (Format.dprintf "[at_active=%a]" Debug.pp_hyp
                           hyp_at_active);
                      vpp#add
                        (Format.dprintf "[lookup_by_ix=%a]"
                           (Format.pp_print_option Debug.pp_hyp)
                           ix_hyp))
                    context)
                final_obs;
              ());
      Format.printf "@.%t@." vpp#as_fmt
  end) *)
