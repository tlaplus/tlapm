(*  Title:      TLA+/simplifier_setup.ML
    Author:     Stephan Merz, Inria
    Copyright (C) 2008-2020 INRIA and Microsoft Corporation
    License:    BSD
    Version:    Isabelle2020

  Code for setting up the simplifier for TLA+.
  The code is essentially copied from FOL and HOL.
*)

structure Simpdata =
struct
  (* Turn theorems into (meta-)equations useful for rewriting, as follows:
     - meta-equalities are already okay
     - equations are turned into meta-equalities
     - a disequality $t \noteq u$ is turned into $(t=u) == FALSE$
     - any other theorem gives a rewrite "... == TRUE"
     Negation and equivalence will be handled later.
     The implicit operator below is Trueprop.
  *)
  fun mk_eq th = case Thm.concl_of th of
      Const(@{const_name \<open>Pure.eq\<close>},_) $ _ $ _  => th
    | _ $ (Const(@{const_name \<open>PredicateLogic.eq\<close>},_) $ _ $ _)    => th RS @{thm eq_reflection}
    | _ $ (Const(@{const_name \<open>PredicateLogic.not\<close>},_) $
              (Const(@{const_name \<open>PredicateLogic.eq\<close>},_) $ _ $ _)) =>
        th RS (@{thm neq_conv_eq_False} RS @{thm eq_reflection})
    | _ => (th RS @{thm eqTrueI}) RS @{thm eq_reflection}

  (* turn P into P == TRUE *)
  fun mk_eq_True (_: Proof.context) th =
    SOME ((th RS @{thm eqTrueI}) RS @{thm eq_reflection}) handle Thm.THM _ => NONE

  (* Produce theorems of the form
    (P1 =simp=> ... =simp=> Pn ==> x == y) ==> (P1 =simp=> ... =simp=> Pn ==> x = y)
  *)
  fun lift_meta_to_obj_eq ctxt i st =
    let
      fun count_imp (Const (@{const_name \<open>PredicateLogic.simp_implies\<close>}, _) $ _ $ Q) =
          1 + count_imp Q
        | count_imp _ = 0;
      val j = count_imp (Logic.strip_assums_concl (Thm.term_of (Thm.cprem_of st i)))
    in if j = 0 then @{thm meta_to_obj_eq}
       else
        let
          val Ps = map (fn k => Free ("P" ^ string_of_int k, propT)) (1 upto j);
          fun mk_simp_implies Q = fold_rev (fn R => fn S =>
            Const (@{const_name \<open>PredicateLogic.simp_implies\<close>}, propT --> propT --> propT) $ R $ S) Ps Q
        in Goal.prove_global (Proof_Context.theory_of ctxt) []
          [mk_simp_implies @{prop \<open>(x::c) == y\<close>}]
          (mk_simp_implies @{prop \<open>(x::c) = y\<close>})
          (fn {context = ctxt, prems} => EVERY
           [rewrite_goals_tac ctxt @{thms simp_implies_def},
            REPEAT (assume_tac ctxt 1 ORELSE
              resolve_tac ctxt
                (@{thm meta_to_obj_eq} ::
                  map (rewrite_rule ctxt @{thms simp_implies_def}) prems) 1)])
        end
    end

  (* Congruence rules expecting = instead of == *)
  fun mk_meta_cong ctxt rl =
      let val rl' = Seq.hd (TRYALL (fn i => fn st =>
        resolve_tac ctxt [lift_meta_to_obj_eq ctxt i st] i st) rl)
      in (rl' RS @{thm eq_reflection})
          handle THM _ =>
            if can Logic.dest_equals (Thm.concl_of rl') then rl'
            else error "Conclusion of congruence rules must use =-equality"
      end |> zero_var_indexes

  (* (string * (thm list * bool)) list
     The following list associates a list of theorems and a flag with
     operator names. Any premise whose outermost operator appears in the
     list will be resolved with the theorems in the list to determine the
     rewrite rules it generates. If the flag is true, the result is itself
     simplified before it is added to the set of rewrite rules. This
     allows us to discard "type-correctness" hypotheses in conditional
     rewrite rules that are added later on. *)
  val mksimps_pairs =
  [(@{const_name \<open>imp\<close>}, ([@{thm mp}], false)),
   (@{const_name \<open>conj\<close>}, ([@{thm conjD1}, @{thm conjD2}], false)),
   (@{const_name \<open>All\<close>}, ([@{thm spec}], false)),
   (@{const_name \<open>TRUE\<close>}, ([], false)),
   (@{const_name \<open>FALSE\<close>}, ([], false)),
   (@{const_name \<open>cond\<close>}, ([@{thm if_bool_equiv_conj} RS @{thm iffD1}], false))
  ];

  (* val mk_atomize:      (string * (thm list * bool)) list -> thm -> thm list *)
  fun mk_atomize ctxt pairs =
    let
      fun atoms thm =
        let
          fun res th = map (fn rl => th RS rl);  (* may raise exception THM *)
          val thm_ctxt = Variable.declare_thm thm ctxt
          fun res_fixed rls =
            if Thm.maxidx_of (Thm.adjust_maxidx_thm ~1 thm) = ~1 then res thm rls
            else Variable.trade (K (fn [thm'] => res thm' rls)) thm_ctxt [thm];
        in
          case Thm.concl_of thm of
             Const(@{const_name \<open>Trueprop\<close>},_) $ p =>
               (case head_of p of
                  Const(a,_) =>
                    (case AList.lookup (op =) pairs a of
                        SOME (rls, b) =>
                          let
                             val rrls = maps atoms (res_fixed rls) handle THM _ => [thm]
                          in
                             if b then map (simplify ctxt) rrls
                             else rrls
                          end
                     | NONE => [thm])
                | _ => [thm])
           | _ => [thm]
        end;
    in atoms end

  fun mksimps pairs ctxt =
    map_filter (try mk_eq) o mk_atomize ctxt pairs o Variable.gen_all ctxt

  fun unsafe_solver_tac ctxt =
  let
    val sol_thms =
      reflexive_thm :: @{thm trueI} :: @{thm refl} :: @{thm iff_refl} :: @{thm notFalseI}:: Simplifier.prems_of ctxt;
    fun sol_tac i =
      FIRST
       [resolve_tac ctxt sol_thms i,
        assume_tac ctxt i,
        eresolve_tac ctxt [@{thm falseE}, @{thm not_refl_False}] i] ORELSE
          (match_tac ctxt [@{thm conjI}]
      THEN_ALL_NEW sol_tac) i
  in
    (fn i => REPEAT_DETERM (match_tac ctxt @{thms simp_impliesI} i)) THEN' sol_tac
  end;

  val unsafe_solver = mk_solver "PredicateLogic unsafe" unsafe_solver_tac;

  (*No premature instantiation of variables during simplification*)
  fun safe_solver_tac ctxt =
    (fn i => REPEAT_DETERM (match_tac ctxt @{thms simp_impliesI} i)) THEN'
    FIRST' [match_tac ctxt (reflexive_thm :: @{thm trueI} :: @{thm refl} :: @{thm iff_refl} :: @{thm notFalseI} :: Simplifier.prems_of ctxt),
            eq_assume_tac, ematch_tac ctxt [@{thm falseE}, @{thm not_refl_False}]];
  val safe_solver = mk_solver "PredicateLogic safe" safe_solver_tac;

  (* Basic infrastructure for simplification *)
  val PL_basic_ss =
    empty_simpset @{context}
    setSSolver safe_solver
    setSolver unsafe_solver
    |> Simplifier.set_subgoaler asm_simp_tac
    |> Simplifier.set_mksimps (mksimps mksimps_pairs)
    |> Simplifier.set_mkeqTrue mk_eq_True
    |> Simplifier.set_mkcong mk_meta_cong
    |> simpset_of

  (* Combination of classical reasoning and simplifier. *)
  structure Splitter = Splitter (
      val context          = @{context}
      val mk_eq            = mk_eq
      val meta_eq_to_iff   = @{thm meta_eq_to_iff}
      val iffD             = @{thm iffD2}
      val disjE            = @{thm disjE}
      val conjE            = @{thm conjE}
      val exE              = @{thm exE}
      val contrapos        = @{thm contrapos}
      val contrapos2       = @{thm contrapos2}
      val notnotD          = @{thm notnotD}
      val safe_tac         = Classical.safe_tac
  );

  val split_tac = Splitter.split_tac;
  val split_inside_tac = Splitter.split_inside_tac;

  structure Clasimp = Clasimp (
    structure Simplifier = Simplifier
      and Splitter = Splitter
      and Classical = Classical
      and Blast = Blast
     val iffD1 = @{thm iffD1}
     val iffD2 = @{thm iffD2}
     val notE = @{thm notE}
  );
  open Clasimp;

  fun unfold_tac ctxt ths =
    ALLGOALS (full_simp_tac (clear_simpset (put_simpset PL_basic_ss ctxt) addsimps ths))

end;  (* structure Simpdata *)

structure Splitter = Simpdata.Splitter;
structure Clasimp = Simpdata.Clasimp;
