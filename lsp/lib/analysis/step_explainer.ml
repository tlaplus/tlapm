open Tlapm_lib

(* TODO: Expand expandable definitions, when looking for facts. *)

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
                      vpp#add (fun fmt ->
                          Format.fprintf fmt "[%a,%a,%a]" Debug.pp_hyp hyp
                            Loc.pp_locus_compact_opt (Util.query_locus hyp)
                            (Format.pp_print_option Debug.pp_hyp)
                            ix_hyp))
                    context)
                final_obs;
              ());
      Format.printf "@.%t@." vpp#as_fmt
  end)
