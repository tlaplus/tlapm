open Tlapm_lib

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
                  vpp#add
                    (Format.dprintf "active{pp=%t,expr=%a}"
                       (fun fmt ->
                         Expr.Fmt.pp_print_expr (context, Ctx.dot) fmt active)
                       Debug.pp_expr active);
                  vpp#scope (Format.dprintf "context{@[<v>%t@]}") @@ fun () ->
                  Deque.iter
                    (fun hyp_i (hyp : Expr.T.hyp) ->
                      let open Expr.T in
                      let ix_hyp =
                        match hyp.core with
                        | Fresh (_, _, _, _)
                        | FreshTuply (_, _)
                        | Flex _
                        | Defn (_, _, _, _) ->
                            None
                        | Fact (hyp_expr, _, _) -> (
                            (* let xx = Deque.first_n *)
                            match hyp_expr.core with
                            | Ix ix -> Deque.nth context (hyp_i - ix)
                            | _ -> None)
                      in
                      let hyp_eq =
                        match hyp.core with
                        | Fresh (_, _, _, _)
                        | FreshTuply (_, _)
                        | Flex _
                        | Defn (_, _, _, _) ->
                            false
                        | Fact (hyp_expr, _, _) ->
                            (* let ix_hyp_opt =
                              match hyp_expr.core with
                              | Ix ix -> Deque.nth context (hyp_i - ix)
                              | _ -> None
                            in
                            let tmp =
                              match ix_hyp_opt with
                              | Some ix_hyp -> (
                                  match ix_hyp.core with
                                  | Fresh (_, _, _, _)
                                  | FreshTuply (_, _)
                                  | Flex _
                                  | Defn (_, _, _, _) ->
                                      false
                                  | Fact (ix_hyp_expr, _, _) ->
                                      Expr.Eq.expr active ix_hyp_expr)
                              | None -> false
                            in
                            tmp || *)
                            Expr.Eq.expr active hyp_expr
                      in
                      vpp#add (fun fmt ->
                          Format.fprintf fmt "[%a,%a,%a,%b]" Debug.pp_hyp hyp
                            Loc.pp_locus_compact_opt (Util.query_locus hyp)
                            (Format.pp_print_option Debug.pp_hyp)
                            ix_hyp hyp_eq))
                    context)
                final_obs;
              ());
      Format.printf "@.%t@." vpp#as_fmt
  end)
