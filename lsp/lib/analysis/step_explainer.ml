open Tlapm_lib

(* TODO: Expand expandable definitions, when looking for facts.
  - prep.ml: let expand_defs
  - e_action.ml: let expand_definition hyp expr

*)

let%test_module "poc: explain direct" =
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
  end)
