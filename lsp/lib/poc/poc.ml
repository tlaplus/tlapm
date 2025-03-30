let%test_unit "experiment with proof names" =
  let filename = "test_obl_expand.tla" in
  let content =
    String.concat "\n"
      [
        "---- MODULE test_obl_expand ----";
        "EXTENDS FiniteSetTheorems";
        "THEOREM TestA == FALSE";
        "    <1>1. TRUE OBVIOUS";
        "    <1>2. TRUE";
        "    <1>3. TRUE";
        "    <1>q. QED BY <1>1, <1>1, <1>2, <1>3";
        "THEOREM TestB == FALSE";
        "    <1>q. QED";
        "       <2>1. TRUE";
        "       <2>q. QED BY <2>1";
        "====";
      ]
  in
  let mule =
    Result.get_ok (Parser.module_of_string ~content ~filename ~loader_paths:[])
  in
  (* let rec t_usable_fact (fact : Tlapm_lib__.Expr.T.expr) =
    let open Tlapm_lib in
    (* List.iter (fun (prop : Property.prop) -> ()) (Property.props_of fact); *)
    (* Property.print_all_props fact;
    Stdlib.flush_all (); *)
    let nm =
      match fact.core with
      | Expr.T.Ix _ -> "Ix"
      | Expr.T.Opaque s -> "Opaque-" ^ s
      | Expr.T.Internal _ -> "Internal"
      | Expr.T.Lambda (_, _) -> "Lambda"
      | Expr.T.Sequent _ -> "Sequent"
      | Expr.T.Bang (_, _)
      | Expr.T.Apply (_, _)
      | Expr.T.With (_, _)
      | Expr.T.If (_, _, _)
      | Expr.T.List (_, _)
      | Expr.T.Let (_, _)
      | Expr.T.Quant (_, _, _)
      | Expr.T.QuantTuply (_, _, _)
      | Expr.T.Tquant (_, _, _)
      | Expr.T.Choose (_, _, _)
      | Expr.T.ChooseTuply (_, _, _)
      | Expr.T.SetSt (_, _, _)
      | Expr.T.SetStTuply (_, _, _)
      | Expr.T.SetOf (_, _)
      | Expr.T.SetOfTuply (_, _)
      | Expr.T.SetEnum _ | Expr.T.Product _ | Expr.T.Tuple _
      | Expr.T.Fcn (_, _)
      | Expr.T.FcnTuply (_, _)
      | Expr.T.FcnApp (_, _)
      | Expr.T.Arrow (_, _)
      | Expr.T.Rect _ | Expr.T.Record _
      | Expr.T.Except (_, _)
      | Expr.T.Dot (_, _)
      | Expr.T.Sub (_, _, _)
      | Expr.T.Tsub (_, _, _)
      | Expr.T.Fair (_, _, _)
      | Expr.T.Case (_, _)
      | Expr.T.String _
      | Expr.T.Num (_, _)
      | Expr.T.At _
      | Expr.T.Parens (_, _) ->
          "???"
    in
    match Property.query fact Proof.T.Props.use_location with
    | None ->
        Eio.traceln "_______XXXXXXXXXX: Use fact ---, %s, %s %a" nm
          (Util.location fact)
          (Format.pp_print_option Proof.T.pp_stepno)
          (Property.query fact Proof.T.Props.step)
    | Some loc ->
        Eio.traceln "_______XXXXXXXXXX: Use fact, %s" (Loc.string_of_locus loc)
  (* Format.eprintf "%a" Expr.Fmt.pp_print_expr fact *)
  and t_step (st : Tlapm_lib.Proof.T.step) =
    match st.core with
    | Tlapm_lib.Proof.T.Assert (_sq, pf) -> t_proof pf
    | Tlapm_lib.Proof.T.Hide _ | Tlapm_lib.Proof.T.Define _
    | Tlapm_lib.Proof.T.Suffices (_, _)
    | Tlapm_lib.Proof.T.Pcase (_, _)
    | Tlapm_lib.Proof.T.Pick (_, _, _)
    | Tlapm_lib.Proof.T.PickTuply (_, _, _)
    | Tlapm_lib.Proof.T.Use (_, _)
    | Tlapm_lib.Proof.T.Have _ | Tlapm_lib.Proof.T.Take _
    | Tlapm_lib.Proof.T.TakeTuply _ | Tlapm_lib.Proof.T.Witness _
    | Tlapm_lib.Proof.T.Forget _ ->
        ()
  and t_qed_step (qs : Tlapm_lib.Proof.T.qed_step) =
    match qs.core with Tlapm_lib.Proof.T.Qed pf -> t_proof pf
  and t_proof (pf : Tlapm_lib.Proof.T.proof) =
    match pf.core with
    | Tlapm_lib.Proof.T.Steps (sts, qed) -> (
        let open Tlapm_lib in
        List.iter t_step sts;
        t_qed_step qed;
        match Property.query qed Proof.Parser.qed_loc_prop with
        | None -> Eio.traceln "_______XXXXXXXXXX: StepsLOC - none"
        | Some qed_loc ->
            Eio.traceln "_______XXXXXXXXXX: StepsLOC, %a, %s" Proof.T.pp_stepno
              (Property.get qed Proof.T.Props.step)
              (Loc.string_of_locus qed_loc))
    | Tlapm_lib.Proof.T.By (usable, _only) ->
        List.iter t_usable_fact usable.facts
    | Tlapm_lib.Proof.T.Obvious | Tlapm_lib.Proof.T.Omitted _
    | Tlapm_lib.Proof.T.Error _ ->
        ()
  and t_moduint (mu : Tlapm_lib.Module.T.modunit) =
    match mu.core with
    | Tlapm_lib.Module.T.Theorem (_nm, _sq, _naxs, _pf, pf_orig, _summ) ->
        (* t_proof pf; *)
        t_proof pf_orig (* Only the orig contains the qed_loc_prop*)
    | Tlapm_lib.Module.T.Constants _ | Tlapm_lib.Module.T.Recursives _
    | Tlapm_lib.Module.T.Variables _
    | Tlapm_lib.Module.T.Definition (_, _, _, _)
    | Tlapm_lib.Module.T.Axiom (_, _)
    | Tlapm_lib.Module.T.Submod _
    | Tlapm_lib.Module.T.Mutate (_, _)
    | Tlapm_lib.Module.T.Anoninst (_, _) ->
        ()
  and t_mule (m : Tlapm_lib.Module.T.mule) = List.iter t_moduint m.core.body in
  let () = t_mule mule in *)
  let visitor =
    object (self : 'self)
      inherit Tlapm_lib.Module.Visit.map as m_super
      inherit [unit] Tlapm_lib.Proof.Visit.iter as p_super

      (* inherit [unit] Tlapm_lib.Expr.Visit.iter as e_super *)
      val vpp = new Debug.visitor_pp

      method! theorem cx name sq naxs pf orig_pf summ =
        let scx = Tlapm_lib.Expr.Visit.empty () in
        (* let scx, sq = self#sequent scx sq in *)
        self#proof scx pf;
        let res =
          m_super#theorem cx name sq naxs orig_pf
            (* NOTE: Use pf_orig. *) orig_pf summ
        in

        Eio.traceln "Theorem %a {@[<v>%t@]}"
          (Format.pp_print_option Tlapm_lib.Util.pp_print_hint)
          name vpp#as_fmt;
        res

      method! proof ctx pf =
        vpp#scope (Format.dprintf "Proof{@[<v>%t@]}") @@ fun () ->
        let open Tlapm_lib in
        (match pf.core with
        | Steps (_sts, qed) -> (
            Eio.traceln "XXXXX  XXXXXXXXXX: Proof, %a, %s"
              (Format.pp_print_option Proof.T.pp_stepno)
              (Property.query pf Proof.T.Props.step)
              (Loc.string_of_locus (Util.get_locus pf));
            Eio.traceln "XXXXX  XXXXXXXXXX: StepsQED, %a, %s" Proof.T.pp_stepno
              (Property.get qed Proof.T.Props.step)
              (Loc.string_of_locus (Util.get_locus qed));
            let qqq = Proof.T.get_qed_proof qed in
            Eio.traceln "XXXXX  XXXXXXXXXX: StepsQQQ, %a, %s" Proof.T.pp_stepno
              (Property.get qqq Proof.T.Props.step)
              (Loc.string_of_locus (Util.get_locus qqq));
            match Property.query qed Proof.Parser.qed_loc_prop with
            | None -> Eio.traceln "XXXXX  XXXXXXXXXX: StepsLOC - none"
            | Some qed_loc ->
                Eio.traceln "XXXXX  XXXXXXXXXX: StepsLOC, %a, %s"
                  Proof.T.pp_stepno
                  (Property.get qed Proof.T.Props.step)
                  (Loc.string_of_locus qed_loc))
        | Obvious | Omitted _ | By (_, _) | Error _ -> ());
        p_super#proof ctx pf

      method! steps ctx sts =
        vpp#scope (Format.dprintf "Steps{@[<v>%t@]}") @@ fun () ->
        List.fold_left (fun ctx st -> self#step ctx st) ctx sts

      method! step ctx (st : Tlapm_lib.Proof.T.step) =
        vpp#scope (Format.dprintf "Step{@[<v>%t@]}") @@ fun () ->
        let open Tlapm_lib in
        let no = Property.get st Proof.T.Props.step in
        (match no with
        | Named (_, _, false) ->
            (* Eio.traceln "XXXXX  XXXXXXXXXX: step, %s" (Proof.T.string_of_stepno no); *)
            let loc =
              Util.get_locus st
              (* Property.get st Proof.T.Props.use_location *)
            in
            Eio.traceln "XXXXX  XXXXXXXXXX: step, %a, %s" Proof.T.pp_stepno no
              (Loc.string_of_locus loc)
        | Named (_, _, true) | Unnamed _ -> ());
        p_super#step ctx st

      method! usable ctx usable =
        let pp_use_def (fmt : Format.formatter)
            (ud : Tlapm_lib.Proof.T.use_def Tlapm_lib.Property.wrapped) : unit =
          match ud.core with
          | Dvar name -> Format.fprintf fmt "DEF[Dvar %s]" name
          | Dx idx -> Format.fprintf fmt "DEF[Dx %d]" idx
        in
        let pp_fact (fmt : Format.formatter) (fact : Tlapm_lib.Expr.T.expr) :
            unit =
          let fact_str = Tlapm_lib.Expr.Fmt.string_of_expr (snd ctx) fact in
          Format.fprintf fmt "FACT[%s=%a]" fact_str Debug.pp_expr fact
        in
        vpp#scope
          (Format.dprintf "Usable{@[<hv>defs=%t facts=%t@;sub=%t@]}"
             (fun fmt -> Format.pp_print_list pp_use_def fmt usable.defs)
             (fun fmt -> Format.pp_print_list pp_fact fmt usable.facts))
        @@ fun () ->
        (* vpp#add (fun fmt -> Format.pp_print_list pp_use_def fmt usable.defs);
        vpp#add (fun fmt -> Format.pp_print_list pp_fact fmt usable.facts); *)
        (* if usable.defs != [] then
          vpp#add
            (Format.dprintf "defs=[%t]" (fun fmt ->
                 Format.pp_print_list pp_use_def fmt usable.defs)); *)
        (* vpp#add (Format.dprintf "facts=[%d]" (List.length usable.facts)); *)
        p_super#usable ctx usable

      method! expr ctx expr =
        vpp#scope (Format.dprintf "E{@[<hv>%a|%t@]}" Debug.pp_expr expr)
        @@ fun () -> p_super#expr ctx expr
    end
  in
  let _ = visitor#tla_module_root mule in
  ()
