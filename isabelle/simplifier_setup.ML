(*  Title:      TLA+/simplifier_setup.ML
    Author:     Stephan Merz, LORIA
    Copyright (C) 2008-2011 INRIA and Microsoft Corporation
    License:    BSD
    Version:    Isabelle2009
    Time-stamp: <2011-10-11 14:59:15 merz>

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
  fun mk_eq th = case concl_of th of
      Const(@{const_name "=="},_) $ _ $ _  => th
    | _ $ (Const(@{const_name "eq"},_) $ _ $ _)    => th RS @{thm eq_reflection}
    | _ $ (Const(@{const_name "Not"},_) $ (Const(@{const_name "eq"},_) $ _ $ _)) => 
        th RS (@{thm eqBoolean} RS @{thm eq_reflection})
    | _ => (th RS @{thm eqTrueI}) RS @{thm eq_reflection};

  (* turn P into P == TRUE *)
  fun mk_eq_True (_: simpset) th =
    SOME ((th RS @{thm eqTrueI}) RS @{thm eq_reflection}) handle Thm.THM _ => NONE

  (* Produce theorems of the form
    (P1 =simp=> ... =simp=> Pn ==> x == y) ==> (P1 =simp=> ... =simp=> Pn ==> x = y)
  *)
  fun lift_meta_to_obj_eq i st =
    let
      fun count_imp (Const (@{const_name PredicateLogic.simp_implies}, _) $ _ $ Q) = 
          1 + count_imp Q
        | count_imp _ = 0;
      val j = count_imp (Logic.strip_assums_concl (List.nth (prems_of st, i - 1)))
    in if j = 0 then @{thm meta_to_obj_eq}
       else
        let
          val Ps = map (fn k => Free ("P" ^ string_of_int k, propT)) (1 upto j);
          fun mk_simp_implies Q = fold_rev (fn R => fn S =>
            Const (@{const_name PredicateLogic.simp_implies}, propT --> propT --> propT) $ R $ S) Ps Q
          val cT = Type ("c", []);
          val x = Free ("x", cT);
          val y = Free ("y", cT);
          val x_eq_y = Const (@{const_name Trueprop}, cT --> propT) $ (Const (@{const_name "eq"}, [cT, cT] ---> cT) $ x $ y)
        in Goal.prove_global (Thm.theory_of_thm st) []
          [mk_simp_implies (Logic.mk_equals (x, y))]
          (mk_simp_implies x_eq_y)
          (fn {prems, ...} => EVERY
           [rewrite_goals_tac @{thms simp_implies_def},
            REPEAT (ares_tac (@{thm meta_to_obj_eq} ::
              map (rewrite_rule @{thms simp_implies_def}) prems) 1)])
        end
    end;

  (* Congruence rules expecting = instead of == *)
  fun mk_meta_cong (_: simpset) rl = zero_var_indexes
      (let val rl' = Seq.hd (TRYALL (fn i => fn st => 
                                        rtac (lift_meta_to_obj_eq i st) i st) rl)
       in (rl' RS @{thm eq_reflection})
          handle THM _ =>
            if can Logic.dest_equals (concl_of rl') then rl'
            else error "Conclusion of congruence rules must use =-equality"
       end);

  (* (string * (thm list * bool)) list
     The following list associates a list of theorems and a flag with
     operator names. Any premise whose outermost operator appears in the
     list will be resolved with the theorems in the list to determine the
     rewrite rules it generates. If the flag is true, the result is itself
     simplified before it is added to the set of rewrite rules. This
     allows us to discard "type-correctness" hypotheses in conditional
     rewrite rules that are added later on. *)
  val mksimps_pairs =
  [(@{const_name imp}, ([@{thm mp}], false)), 
   (@{const_name conj}, ([@{thm conjD1}, @{thm conjD2}], false)),
   (@{const_name All}, ([@{thm spec}], false)), 
   (@{const_name TRUE}, ([], false)), 
   (@{const_name FALSE}, ([], false)),
   (@{const_name cond}, ([@{thm if_bool_eq_conj} RS @{thm iffD1}], false))
  ];

  (* val mk_atomize:      (string * (thm list * bool)) list -> thm -> thm list *)
  fun mk_atomize pairs =
    let
      fun atoms thm =
        let
          val simps = global_simpset_of (theory_of_thm thm);
          fun res th = map (fn rl => th RS rl);  (* may raise exception THM *)
          fun res_fixed rls =
            if Thm.maxidx_of (Thm.adjust_maxidx_thm ~1 thm) = ~1 then res thm rls
            else Variable.trade (K (fn [thm'] => res thm' rls)) (Variable.global_thm_context thm) [thm];
        in
          case concl_of thm of
             Const(@{const_name Trueprop},_) $ p =>
               (case head_of p of
                  Const(a,_) =>
                    (case AList.lookup (op =) pairs a of
                        SOME (rls, b) => 
                          let
                             val rls = maps atoms (res_fixed rls) handle THM _ => [thm]
                          in
                             if b then map (simplify simps) rls
                             else rls
                          end
                     | NONE => [thm])
                | _ => [thm])
           | _ => [thm]
        end;
    in atoms end;

  fun mksimps pairs (_: simpset) = 
    map_filter (try mk_eq) o mk_atomize pairs o gen_all

  fun unsafe_solver_tac ss = 
    (fn i => REPEAT_DETERM (match_tac @{thms simp_impliesI} i)) THEN'
    FIRST' [resolve_tac (reflexive_thm :: @{thm trueI} :: @{thm refl} :: @{thm iff_refl} :: @{thm notFalseI} :: Simplifier.prems_of ss),
            atac, etac @{thm falseE}];
                                   (*the above may instantiate variables*)
  val unsafe_solver = mk_solver "PredicateLogic unsafe" unsafe_solver_tac;

  fun safe_solver_tac ss =
    (fn i => REPEAT_DETERM (match_tac @{thms simp_impliesI} i)) THEN'
    FIRST' [match_tac (reflexive_thm :: @{thm trueI} :: @{thm refl} :: @{thm iff_refl} :: @{thm notFalseI} :: Simplifier.prems_of ss),
            eq_assume_tac, ematch_tac @{thms falseE}];
  val safe_solver = mk_solver "PredicateLogic safe" safe_solver_tac;

  (* Basic infrastructure for simplification *)
  val PL_basic_ss = Simplifier.global_context @{theory} empty_ss
    setsubgoaler asm_simp_tac
    setSSolver safe_solver
    setSolver unsafe_solver
    setmksimps (mksimps mksimps_pairs)
    setmkeqTrue mk_eq_True
    setmkcong mk_meta_cong;

  (* Combination of classical reasoning and simplifier. *)
  structure Splitter = Splitter (
      val thy              = @{theory}
      val mk_eq            = mk_eq
      val meta_eq_to_iff   = @{thm meta_eq_to_iff}
      val iffD             = @{thm iffD2}
      val disjE            = @{thm disjE}
      val conjE            = @{thm conjE}
      val exE              = @{thm exE}
      val contrapos        = @{thm contrapos}
      val contrapos2       = @{thm contrapos2}
      val notnotD          = @{thm notnotD}
  );

  val split_tac = Splitter.split_tac;
  val split_inside_tac = Splitter.split_inside_tac;
  (* val split_asm_tac    = Splitter.split_asm_tac; *)
  val op addsplits     = Splitter.addsplits;
  val op delsplits     = Splitter.delsplits;

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

end;  (* structure Simpdata *)

structure Splitter = Simpdata.Splitter;
structure Clasimp = Simpdata.Clasimp;
