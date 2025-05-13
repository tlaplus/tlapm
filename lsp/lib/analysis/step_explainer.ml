open Tlapm_lib

type pred_expr_fun =
  Expr.T.expr -> Expr.T.hyp Deque.dq -> Expr.T.expr list -> Expr.T.expr -> bool

type pred_hyp_fun =
  Expr.T.expr -> Expr.T.hyp Deque.dq -> Expr.T.expr list -> string list

let find_in_ctx (active : Expr.T.expr) (context : Expr.T.hyp Deque.dq)
    (pred_expr' : pred_expr_fun) (match_op : Expr.T.expr) (arg : Expr.T.expr) :
    bool =
  let pred_expr ((bools, index, exp) : bool list * int * Expr.T.expr)
      (hyp : Expr.T.hyp) : bool list * int * Expr.T.expr =
    let hyp_at_active =
      Expr.Subst.app_hyp (Expr.Subst.shift (Deque.size context - index)) hyp
    in
    let new_bools =
      match hyp_at_active.core with
      | Fresh (_, _, _, _) | FreshTuply (_, _) | Flex _ | Defn (_, _, _, _) ->
          bools
      | Fact (hyp_expr, _, _) -> (
          match hyp_expr.core with
          | Apply (op, args) ->
              if op.core = match_op.core then
                if pred_expr' active context args arg then true :: bools
                else bools
              else bools
          | _ -> bools)
    in
    (new_bools, index + 1, exp)
  in
  let bools, _, _ = Deque.fold_left pred_expr ([], 0, arg) context in
  match bools with [] -> false | _ -> true

let iter_ctx (active : Expr.T.expr) (context : Expr.T.hyp Deque.dq)
    (pred_hyp' : pred_hyp_fun) (match_op : Expr.T.expr) : string list =
  let pred_hyp ((expls, index) : string list * int) (hyp : Expr.T.hyp) :
      string list * int =
    let hyp_at_active =
      Expr.Subst.app_hyp (Expr.Subst.shift (Deque.size context - index)) hyp
    in
    let new_expls =
      match hyp_at_active.core with
      | Fresh (_, _, _, _) | FreshTuply (_, _) | Flex _ | Defn (_, _, _, _) ->
          expls
      | Fact (hyp_expr, _, _) -> (
          match hyp_expr.core with
          | Apply (op, args) ->
              if op.core = match_op.core then
                pred_hyp' active context args @ expls
              else expls
          | _ -> expls)
    in
    (new_expls, index + 1)
  in
  let explanations, _ = Deque.fold_left pred_hyp ([], 0) context in
  explanations

let find_in_seq (_active : Expr.T.expr) (context : Expr.T.hyp Deque.dq)
    (pred_expr' : pred_expr_fun) (assums : Expr.T.expr list)
    (goal : Expr.T.expr) : bool =
  let pred_expr ((bools, index, exp) : bool list * int * Expr.T.expr)
      (hyp : Expr.T.hyp) : bool list * int * Expr.T.expr =
    let new_bools =
      match hyp.core with
      | Fresh (_, _, _, _) | FreshTuply (_, _) | Flex _ | Defn (_, _, _, _) ->
          bools
      | Fact (hyp_expr, _, _) -> (
          match hyp_expr.core with
          | Sequent seq ->
              let n_ctx =
                Deque.map
                  (fun i hyp ->
                    let shift_by = Deque.size context - index - i in
                    (* Eio.traceln "Shift:%d" shift_by; *)
                    Expr.Subst.app_hyp (Expr.Subst.shift shift_by) hyp)
                  seq.context
              in
              let n_active =
                Expr.Subst.app_expr
                  (Expr.Subst.shift
                     (Deque.size context - index - Deque.size seq.context))
                  seq.active
              in
              if pred_expr' n_active n_ctx assums goal then true :: bools
              else bools
          | _ -> bools)
    in
    (new_bools, index + 1, exp)
  in
  let bools, _, _ = Deque.fold_left pred_expr ([], 0, goal) context in
  match bools with [] -> false | _ -> true

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

let explain_obl_conj_elim (active : Expr.T.expr) (context : Expr.T.hyp Deque.dq)
    : string list =
  let pred_hyp_fun : pred_hyp_fun =
   fun active _context args ->
    List.fold_left
      (fun acc arg ->
        if Expr.Eq.expr arg active then "/\\-elim" :: acc else acc)
      [] args
  in
  iter_ctx active context pred_hyp_fun
    (Property.noprops (Expr.T.Internal Builtin.Conj))

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

let explain_obl_disj_elim (active : Expr.T.expr) (context : Expr.T.hyp Deque.dq)
    : string list =
  let pred_expr_fun : pred_expr_fun =
   fun _active _context args arg ->
    Expr.Eq.expr (List.nth args 0) arg && Expr.Eq.expr (List.nth args 1) active
  in
  let pred_hyp_fun : pred_hyp_fun =
   fun _active _context args ->
    let all_found =
      List.for_all
        (fun arg ->
          find_in_ctx active context pred_expr_fun
            (Property.noprops (Expr.T.Internal Builtin.Implies))
            arg)
        args
    in
    match all_found with true -> [ "\\/-elim" ] | false -> []
  in
  iter_ctx active context pred_hyp_fun
    (Property.noprops (Expr.T.Internal Builtin.Disj))

let explain_obl_disjunctive_syllogism (active : Expr.T.expr)
    (context : Expr.T.hyp Deque.dq) : string list =
  let pred_expr_fun : pred_expr_fun =
   fun _active _context args arg -> Expr.Eq.expr (List.nth args 0) arg
  in
  let pred_hyp_fun : pred_hyp_fun =
   fun active _context args ->
    let args_wo_goal =
      List.filter (fun arg -> not (Expr.Eq.expr arg active)) args
    in
    let exists = List.length args != List.length args_wo_goal in
    match exists with
    | true -> (
        let all_neg_found =
          List.for_all
            (fun arg ->
              find_in_ctx active context pred_expr_fun
                (Property.noprops (Expr.T.Internal Builtin.Neg))
                arg)
            args_wo_goal
        in
        match all_neg_found with
        | true -> [ "Disjunctive syllogism" ]
        | false -> [])
    | false -> []
  in
  iter_ctx active context pred_hyp_fun
    (Property.noprops (Expr.T.Internal Builtin.Disj))

let explain_obl_disjunctive_syllogism_seq (active : Expr.T.expr)
    (context : Expr.T.hyp Deque.dq) : string list =
  let pred_expr_fun : pred_expr_fun =
   fun active context args arg ->
    let res =
      match
        Deque.find context (fun hyp ->
            match hyp.core with
            | Fresh (_, _, _, _) | FreshTuply (_, _) | Flex _ | Defn (_, _, _, _)
              ->
                false
            | Fact (hyp_expr, _, _) -> (
                match hyp_expr.core with
                | Apply (op, args') ->
                    if
                      op.core
                      = (Property.noprops (Expr.T.Internal Builtin.Neg)).core
                    then
                      Expr.Eq.expr (List.nth args 0) (List.nth args' 0)
                      && Expr.Eq.expr active arg
                    else false
                | _ -> false))
      with
      | Some (_, _) -> true
      | None -> false
    in
    res
  in
  match active.core with
  | Expr.T.Apply (op, args) -> (
      match op.core with
      | Expr.T.Internal Builtin.Disj -> (
          let all_found =
            find_in_seq active context pred_expr_fun
              [ List.nth args 0 ]
              (List.nth args 1)
            || find_in_seq active context pred_expr_fun
                 [ List.nth args 1 ]
                 (List.nth args 0)
          in
          match all_found with
          | true -> [ "Disjunctive syllogism" ]
          | false -> [])
      | _ -> [])
  | _ -> []

let explain_obl_elim_modus_ponens (active : Expr.T.expr)
    (context : Expr.T.hyp Deque.dq) : string list =
  let pred_hyp_fun : pred_hyp_fun =
   fun active context args ->
    if
      Expr.Eq.expr (List.nth args 1) active
      && Backend.Prep.have_fact context (List.nth args 0)
    then [ "elim (modus ponens)" ]
    else []
  in
  iter_ctx active context pred_hyp_fun
    (Property.noprops (Expr.T.Internal Builtin.Implies))

let rec _t_usable_fact (fact : Tlapm_lib__.Expr.T.expr) =
  let open Tlapm_lib in
  let nm =
    match fact.core with
    | Expr.T.Ix n -> "Ix" ^ string_of_int n
    | Expr.T.Opaque s -> "Opaque-" ^ s
    | Expr.T.Internal i -> (
        match i with
        | TRUE -> "TRUE"
        | FALSE -> "FALSE"
        | Implies -> "Implies"
        | Equiv -> "Equiv"
        | Conj -> "Conj"
        | Disj -> "Disj"
        | Neg -> "Neg"
        | Eq -> "Eq"
        | Neq -> "Neq"
        | STRING -> "STRING"
        | BOOLEAN -> "BOOLEAN"
        | SUBSET -> "SUBSET"
        | UNION -> "UNION"
        | DOMAIN -> "DOMAIN"
        | Subseteq -> "Subseteq"
        | Mem -> "Mem"
        | Notmem -> "Notmem"
        | Setminus -> "Setminus"
        | Cap -> "Cap"
        | Cup -> "Cup"
        | Prime -> "Prime"
        | StrongPrime -> "StrongPrime"
        | Leadsto -> "Leadsto"
        | ENABLED -> "ENABLED"
        | UNCHANGED -> "UNCHANGED"
        | Cdot -> "Cdot"
        | Actplus -> "Actplus"
        | Box true -> "Box(true)"
        | Box false -> "Box(false)"
        | Diamond -> "Diamond"
        | Nat -> "Nat"
        | Int -> "Int"
        | Real -> "Real"
        | Plus -> "Plus"
        | Minus -> "Minus"
        | Uminus -> "Uminus"
        | Times -> "Times"
        | Ratio -> "Ratio"
        | Quotient -> "Quotient"
        | Remainder -> "Remainder"
        | Exp -> "Exp"
        | Infinity -> "Infinity"
        | Lteq -> "Lteq"
        | Lt -> "Lt"
        | Gteq -> "Gteq"
        | Gt -> "Gt"
        | Divides -> "Divides"
        | Range -> "Range"
        | Seq -> "Seq"
        | Len -> "Len"
        | BSeq -> "BSeq"
        | Cat -> "Cat"
        | Append -> "Append"
        | Head -> "Head"
        | Tail -> "Tail"
        | SubSeq -> "SubSeq"
        | SelectSeq -> "SelectSeq"
        | OneArg -> "OneArg"
        | Extend -> "Extend"
        | Print -> "Print"
        | PrintT -> "PrintT"
        | Assert -> "Assert"
        | JavaTime -> "JaveTime"
        | TLCGet -> "TLCGet"
        | TLCSet -> "TLCSet"
        | Permutations -> "Permutations"
        | SortSeq -> "SortSeq"
        | RandomElement -> "RandomElement"
        | Any -> "Any"
        | ToString -> "ToString"
        | Unprimable -> "Unprimable"
        | Irregular -> "Irregular")
    | Expr.T.Lambda (_, _) -> "Lambda"
    | Expr.T.Sequent _ -> "Sequent"
    | Expr.T.Bang (_, _) -> "Bang"
    | Expr.T.Apply (e, e_l) ->
        _t_usable_fact e;
        List.iter _t_usable_fact e_l;
        "Apply"
    | Expr.T.With (_, _) -> "With"
    | Expr.T.If (_, _, _) -> "If"
    | Expr.T.List (_, _) -> "List"
    | Expr.T.Let (_, _) -> "Let"
    | Expr.T.Quant (_, _, _) -> "Quant"
    | Expr.T.QuantTuply (_, _, _) -> "QuantTuply"
    | Expr.T.Tquant (_, _, _) -> "Tquant"
    | Expr.T.Choose (_, _, _) -> "Choose"
    | Expr.T.ChooseTuply (_, _, _) -> "ChooseTuply"
    | Expr.T.SetSt (_, _, _) -> "SetSt"
    | Expr.T.SetStTuply (_, _, _) -> "SetStTuply"
    | Expr.T.SetOf (_, _) -> "SetOf"
    | Expr.T.SetOfTuply (_, _) -> "SetOfTuply"
    | Expr.T.SetEnum _ -> "SetEnum"
    | Expr.T.Product _ -> "Product"
    | Expr.T.Tuple _ -> "Tuple"
    | Expr.T.Fcn (_, _) -> "Fcn"
    | Expr.T.FcnTuply (_, _) -> "FcnTuply"
    | Expr.T.FcnApp (_, _) -> "FcnApp"
    | Expr.T.Arrow (_, _) -> "Arrow"
    | Expr.T.Rect _ -> "Rect"
    | Expr.T.Record _ -> "Record"
    | Expr.T.Except (_, _) -> "Except"
    | Expr.T.Dot (_, _) -> "Dot"
    | Expr.T.Sub (_, _, _) -> "Sub"
    | Expr.T.Tsub (_, _, _) -> "Tsub"
    | Expr.T.Fair (_, _, _) -> "Fair"
    | Expr.T.Case (_, _) -> "Case"
    | Expr.T.String _ -> "String"
    | Expr.T.Num (_, _) -> "Num"
    | Expr.T.At _ -> "At"
    | Expr.T.Parens (_, _) -> "Parens"
  in
  match Property.query fact Proof.T.Props.use_location with
  | None -> Eio.traceln " Fact %s" nm
  | Some loc -> Eio.traceln "Loc %s" (Loc.string_of_locus loc)

and _t_hyp (_ : int) (hy : Tlapm_lib.Expr.T.hyp) =
  match hy.core with
  | Fresh (hint, _, _, hdom) -> (
      Eio.traceln "Fresh %s" hint.core;
      match hdom with
      | Unbounded -> Eio.traceln "Unbounded"
      | Bounded (expr, _) ->
          Eio.traceln "Bounded";
          _t_usable_fact expr)
  | FreshTuply (_, _) -> Eio.traceln "FreshTuply"
  | Flex _ -> Eio.traceln "Flex"
  | Defn (defn, _, _, _) -> (
      match defn.core with
      | Recursive (hint, _) ->
          (* hint * shape *)
          Eio.traceln "Defn Recursive %s" hint.core
      | Operator (hint, expr) ->
          (* hint * expr *)
          Eio.traceln "Defn Operator %s" hint.core;
          _t_usable_fact expr
      | Instance (hint, _) ->
          (* hint * instance *)
          Eio.traceln "Defn Instance %s" hint.core
      | Bpragma (hint, _, _) -> Eio.traceln "Defn Bpragma %s" hint.core)
  | Fact (fact, _, _) ->
      (* Eio.traceln "Fact"; *)
      _t_usable_fact fact

let _t_deq (context : Expr.T.hyp Deque.dq) = Deque.iter _t_hyp context

let explain_obl_impl_intro (active : Expr.T.expr)
    (context : Expr.T.hyp Deque.dq) : string list =
  let pred_expr_fun : pred_expr_fun =
   fun active context args arg ->
    (* if Expr.Eq.expr arg active then Eio.traceln "Yes" else Eio.traceln "No";
      Eio.traceln "Orig goal:";
      _t_usable_fact arg;
      Eio.traceln "Seq goal:";
      _t_usable_fact active;
      Eio.traceln "Seq ctx:";
      _t_deq context;
      Eio.traceln "Goal ctx:";
      _t_usable_fact (List.nth args 0); *)
    let res =
      match
        Deque.find context (fun hyp ->
            match hyp.core with
            | Fresh (_, _, _, _) | FreshTuply (_, _) | Flex _ | Defn (_, _, _, _)
              ->
                false
            | Fact (hyp_expr, _, _) -> Expr.Eq.expr hyp_expr (List.nth args 0))
      with
      | Some (_, _) -> true
      | None -> false
    in
    res && Expr.Eq.expr arg active
  in
  match active.core with
  | Expr.T.Apply (op, args) -> (
      match op.core with
      | Expr.T.Internal Builtin.Implies -> (
          let all_found =
            find_in_seq active context pred_expr_fun
              [ List.nth args 0 ]
              (List.nth args 1)
          in
          match all_found with true -> [ "=>-intro" ] | false -> [])
      | _ -> [])
  | _ -> []

let explain_obl (obl : Proof.T.obligation) : string list =
  let obl = Backend.Prep.expand_defs obl in
  let active = obl.obl.core.active in
  let context = obl.obl.core.context in
  List.flatten
    (List.map
       (fun f -> f active context)
       [
         explain_obl_direct;
         explain_obl_conj_intro;
         explain_obl_conj_elim;
         explain_obl_disj_intro;
         explain_obl_disj_elim;
         explain_obl_disjunctive_syllogism;
         explain_obl_disjunctive_syllogism_seq;
         explain_obl_elim_modus_ponens;
         explain_obl_impl_intro;
       ])

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

let%test_unit "explain conj elim Ix match" =
  let theorem =
    [
      "THEOREM TestA == ASSUME NEW a, NEW b, a /\\ b PROVE a";
      "    <1>1. a PROOF OBVIOUS";
      "    <1>q. QED BY <1>1";
    ]
  in
  match test_util_get_expl theorem with
  | list ->
      assert (String.concat ";" list = "Direct proof from assumptions;/\\-elim")

let%test_unit "explain conj elim Ix not match" =
  let theorem =
    [
      "THEOREM TestA == ASSUME NEW a, NEW b, NEW c, NEW d, c /\\ d PROVE a";
      "    <1>1. a PROOF OBVIOUS";
      "    <1>q. QED BY <1>1";
    ]
  in
  match test_util_get_expl theorem with
  | list -> assert (String.concat ";" list = "Direct proof from assumptions")

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

let%test_unit "explain disj elim" =
  let theorem =
    [
      "THEOREM TestA == ASSUME NEW a, NEW b, NEW c, NEW d, a => c, b => c, a \
       \\/ b PROVE c";
      "    <1>1. c PROOF OBVIOUS";
      "    <1>q. QED BY <1>1";
    ]
  in
  match test_util_get_expl theorem with
  | list ->
      assert (String.concat ";" list = "Direct proof from assumptions;\\/-elim")

let%test_unit "explain disj elim not full" =
  let theorem =
    [
      "THEOREM TestA == ASSUME NEW a, NEW b, NEW c, NEW d, a => c, b => d, a \
       \\/ b PROVE c";
      "    <1>1. c PROOF OBVIOUS";
      "    <1>q. QED BY <1>1";
    ]
  in
  match test_util_get_expl theorem with
  | list -> assert (String.concat ";" list = "Direct proof from assumptions")

let%test_unit "explain disjunctive syllogism" =
  let theorem =
    [
      "THEOREM TestA == ASSUME NEW a, NEW b, a \\/ b, ~a PROVE b";
      "    <1>1. b PROOF OBVIOUS";
      "    <1>q. QED BY <1>1";
    ]
  in
  match test_util_get_expl theorem with
  | list ->
      assert (
        String.concat ";" list
        = "Direct proof from assumptions;Disjunctive syllogism")

let%test_unit "explain disjunctive syllogism seq" =
  let theorem =
    [
      "THEOREM TestA == ASSUME NEW a, NEW b PROVE a \\/ b";
      "    <1>1. ASSUME ~a PROVE b PROOF OMITTED";
      "    <1>q. QED BY <1>1";
    ]
  in
  match test_util_get_expl theorem with
  | list -> assert (String.concat ";" list = "Disjunctive syllogism")

let%test_unit "explain disjunctive syllogism seq switched" =
  let theorem =
    [
      "THEOREM TestA == ASSUME NEW a, NEW b PROVE a \\/ b";
      "    <1>1. ASSUME ~b PROVE a PROOF OMITTED";
      "    <1>q. QED BY <1>1";
    ]
  in
  match test_util_get_expl theorem with
  | list -> assert (String.concat ";" list = "Disjunctive syllogism")

let%test_unit "explain elim (modus ponens)" =
  let theorem =
    [
      "THEOREM TestA == ASSUME NEW a, NEW b, a => b, a PROVE b";
      "    <1>1. b PROOF OBVIOUS";
      "    <1>q. QED BY <1>1";
    ]
  in
  match test_util_get_expl theorem with
  | list ->
      assert (
        String.concat ";" list
        = "Direct proof from assumptions;elim (modus ponens)")

let%test_unit "explain impl intro" =
  let theorem =
    [
      "THEOREM TestA == ASSUME NEW a, NEW b, NEW c, NEW d PROVE a => b";
      "    <1>1. ASSUME c, d, a PROVE b PROOF OMITTED";
      "    <1>q. QED BY <1>1";
    ]
  in
  match test_util_get_expl theorem with
  | list ->
      Eio.traceln "Res:%s" (String.concat ";" list);
      assert (String.concat ";" list = "=>-intro")

let%test_module "poc: explain direct" =
  (module struct
    let mule =
      let filename = "test_step_explainer.tla" in
      let content =
        String.concat "\n"
          [
            "---- MODULE test_step_explainer ----";
            (* "THEOREM ASSUME NEW P(_) PROVE \\A x: P(x)";
            "PROOF";
            "    <1> TAKE x";
            "    <1>1. P(x) PROOF OMITTED";
            "    <1>q. QED BY <1>1"; *)
            (* "THEOREM ProveImplicationDirect ==";
            "  ASSUME NEW A, NEW B PROVE A => B";
            "PROOF";
            "  <1> SUFFICES ASSUME A PROVE B OBVIOUS";
            "  <1>1. B PROOF OMITTED";
            "  <1>q. QED BY <1>1"; *)
            (* "THEOREM ASSUME NEW A, NEW B PROVE A => B";
            "  <1> HAVE A";
            "  <1>1. B PROOF OMITTED";
            "  <1>q. QED BY <1>1"; *)
            (* "THEOREM ProveDisjunctionByCases ==";
            "  ASSUME NEW A, NEW B PROVE A \\/ B";
            "PROOF";
            "  <1> SUFFICES ASSUME NEW C, NEW D, C \\/ D PROVE A \\/ B OBVIOUS";
            "  <1>a. ASSUME C PROVE A PROOF OMITTED";
            "  <1>b. ASSUME D PROVE B PROOF OMITTED";
            "  <1>q. QED BY <1>a, <1>b"; *)
            (* "THEOREM ProveForallSuffices ==";
            "  ASSUME NEW P(_) PROVE \\A x: P(x)";
            "PROOF";
            "  <1> SUFFICES ASSUME NEW a PROVE P(a) OBVIOUS";
            "  <1>1. P(a) PROOF OMITTED";
            "  <1>q. QED BY <1>1"; *)
            (* "THEOREM ProveForallTake ==";
            "  ASSUME NEW P(_) PROVE \\A x: P(x)";
            "PROOF";
            "  <1> TAKE x";
            "  <1>1. P(x) PROOF OMITTED";
            "  <1>q. QED BY <1>1"; *)
            (* "THEOREM ProveExistsAssume ==";
            "    ASSUME NEW P(_) PROVE \\E x: P(x)";
            "PROOF";
            "    <1>p. ASSUME NEW x, x = 123";
            "    PROVE P(x) PROOF OMITTED";
            "    <1>q. QED BY <1>p"; *)
            (* "THEOREM UseNegationReexpress ==";
            "    ASSUME NEW A, NEW B, NEW C, NEW P, ~P, P = (A \\/ B) PROVE C";
            "PROOF";
            "    <1>x. ~A /\\ ~B PROOF OBVIOUS";
            "    <1>q. QED OMITTED"; *)
            (* "THEOREM UseDisjunctionCases ==";
            "    ASSUME NEW A, NEW B, NEW C, A \\/ B PROVE C";
            "PROOF";
            "    <1>a. CASE A PROOF OMITTED";
            "    <1>b. CASE B PROOF OMITTED";
            "    <1>q. QED BY <1>a, <1>b"; *)
            (* "THEOREM UseForallSuffices ==";
            "    ASSUME NEW S, NEW P(_), NEW G,";
            "    \\A x \\in S : P(x),";
            "    S # {}";
            "    PROVE G";
            "PROOF";
            "    <1> SUFFICES ASSUME NEW a \\in S PROVE G OBVIOUS";
            "    <1>p. P(a) PROOF OBVIOUS";
            "    <1>q. QED PROOF OMITTED"; *)
            "THEOREM TestA == ASSUME NEW a, NEW b, NEW c, NEW d PROVE a => b";
            "    <1>1. ASSUME c, d, a PROVE b PROOF OMITTED";
            "    <1>q. QED BY <1>1";
            (* "THEOREM ProveExistsWitness ==";
            "    ASSUME NEW P(_) PROVE \\E x: P(x)";
            "PROOF";
            "    <1> WITNESS 123";
            "    <1>p. P(123) PROOF OMITTED";
            "    <1>q. QED BY <1>p"; *)
            (* "THEOREM UseForallPick ==";
            "    ASSUME NEW S, NEW P(_), NEW G,";
            "    \\A x \\in S : P(x),";
            "    S # {}";
            "    PROVE G";
            "PROOF";
            "    <1> PICK a : a \\in S OBVIOUS";
            "    <1>p. P(a) PROOF OBVIOUS"; *)
            (* "    <1>q. QED PROOF OMITTED"; *)
            (* "THEOREM UseExistsPick ==";
            "    ASSUME NEW S, NEW P(_), NEW G,";
            "    \\E x \\in S : P(x)";
            "    PROVE G";
            "PROOF";
            "    <1> PICK a \\in S : P(a) OBVIOUS";
            "    <1>p. P(a) PROOF OBVIOUS";
            "    <1>q. QED PROOF OMITTED"; *)
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
