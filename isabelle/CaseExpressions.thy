(*  Title:      TLA+/CaseExpressions.thy
    Author:     Stephan Merz, LORIA
    Copyright (C) 2009-2021  INRIA and Microsoft Corporation
    License:    BSD
    Version:    Isabelle2020
*)

section \<open> Case expressions \<close>

theory CaseExpressions
imports Tuples
begin

text \<open>
  A \textsc{case} expression in \tlaplus{} has the form
  \[
    \textsc{case } p_1 \rightarrow e_1
    \Box \ldots \Box p_n \rightarrow e_n
    \textsc{ other } e_{n+1}
  \]
  where the \textsc{other}-branch is optional. We represent this
  construct by Isabelle operators @{text "Case(ps, es)"} and
  @{text "CaseOther(ps, es, oth)"} where
  @{text ps} is the sequence of guards $p_i$, @{text es} is the sequence
  of expressions $e_i$ and @{text oth} is the expression that occurs
  in the optional \textsc{other}-branch. The @{text Case} operator
  could be considered as a special case of @{text CaseOther}, and thus
  be avoided, by adding an \textsc{other}-branch returning
  @{text default} (which is the result when all guards evaluate
  to @{text FALSE}). However, doing so slows down evaluation because the
  guard of the \textsc{other}-branch, when present, is the conjunction
  of the negated guards of all other branches, so every guard appears
  twice (and will be simplified twice) in a @{text CaseOther} expression.
\<close>

definition CaseArm  \<comment> \<open> preliminary construct to convert case arm into set \<close>
where "CaseArm(p,e) \<equiv> IF p THEN {e} ELSE {}"

definition Case where
  "Case(ps, es) \<equiv> CHOOSE x : x \<in> (UNION { CaseArm(ps[i], es[i]) : i \<in> DOMAIN ps })"

definition CaseOther where
  "CaseOther(ps, es, oth) \<equiv>
   CHOOSE x : x \<in> (UNION { CaseArm(ps[i], es[i]) : i \<in> DOMAIN ps })
                  \<union> CaseArm((\<forall>i \<in> DOMAIN ps : \<not>ps[i]), oth)"

nonterminal case_arm and case_arms

syntax
  "_case_syntax":: "case_arms \<Rightarrow> c"               ("(CASE _ )" 10)
  "_case1"      :: "[c, c] \<Rightarrow> case_arm"           ("(2_ \<rightarrow>/ _)" 10)
  ""            :: "case_arm \<Rightarrow> case_arms"        ("_")
  "_other"      :: "c \<Rightarrow> case_arms"               ("OTHER \<rightarrow> _")
  "_case2"      :: "[case_arm, case_arms] \<Rightarrow> case_arms"  ("_/ \<box> _")

syntax (ASCII)
  "_case1"      :: "[c, c] \<Rightarrow> case_arm"           ("(2_ ->/ _)" 10)
  "_other"      :: "c \<Rightarrow> case_arms"               ("OTHER -> _")
  "_case2"      :: "[case_arm, case_arms] \<Rightarrow> case_arms"  ("_/ [] _")

parse_ast_translation \<open>
  let
    (* make_tuple converts a list of ASTs to a tuple formed from these ASTs.
       The order of elements is reversed. *)
    fun make_tuple [] = Ast.Constant "emptySeq"
      | make_tuple (t :: ts) = Ast.Appl[Ast.Constant "Append", make_tuple ts, t]
    (* get_case_constituents extracts the lists of predicates, terms, and
       default value from the arms of a case expression.
       The order of the ASTs is reversed. *)
    fun get_case_constituents (Ast.Appl[Ast.Constant "_other", t]) =
            (* 1st case: single "OTHER" arm *)
            ([], [], SOME t)
      | get_case_constituents (Ast.Appl[Ast.Constant "_case1", p, t]) =
            (* 2nd case: a single arm, no "OTHER" branch *)
            ([p], [t], NONE)
      | get_case_constituents (Ast.Appl[Ast.Constant "_case2",
                                    Ast.Appl[Ast.Constant "_case1", p, t],
                                    arms]) =
            (* 3rd case: one arm, followed by remaining arms *)
            let val (ps, ts, oth) = get_case_constituents arms
            in  (ps @ [p], ts @ [t], oth)
            end
    fun case_syntax_tr [arms] =
        let val (preds, trms, oth) = get_case_constituents arms
            val pTuple = make_tuple preds
            val tTuple = make_tuple trms
        in
          if oth = NONE
          then Ast.Appl[Ast.Constant "Case", pTuple, tTuple]
          else Ast.Appl[Ast.Constant "CaseOther", pTuple, tTuple, the oth]
        end
      | case_syntax_tr _ = raise Match;
  in
    [("_case_syntax", K case_syntax_tr)]
  end
\<close>


(** debugging **
(*ML \<open> set Syntax.trace_ast; \<close>*)

lemma "CASE a \<rightarrow> b \<box> c \<rightarrow> d \<box> e \<rightarrow> f \<box> OTHER \<rightarrow> g"
oops

lemma "CASE a \<rightarrow> b"
oops

lemma "CASE OTHER \<rightarrow> g"  (* degenerated case *)
oops

(*ML \<open> reset Syntax.trace_ast; \<close>*)
**)

print_ast_translation \<open>
  let
    fun list_from_tuple (Ast.Constant @{const_syntax "emptySeq"}) = []
      | list_from_tuple (Ast.Appl[Ast.Constant "@tuple", tp]) =
        let fun list_from_tp (Ast.Appl[Ast.Constant "@app", tp, t]) =
                     (list_from_tp tp) @ [t]
              | list_from_tp t = [t]
        in  list_from_tp tp
        end
    (* make_case_arms constructs an AST representing the arms of the
       CASE expression. The result is an AST of "type" case_arms.
       The lists of predicates and terms are of equal length,
       oth is optional. The lists can be empty only if "oth" is present,
       corresponding to a degenerated expression "CASE OTHER -> e". *)
    fun make_case_arms [] [] (SOME oth) =
            (* only a single OTHER clause *)
            Ast.Appl[Ast.Constant @{syntax_const "_other"}, oth]
      | make_case_arms [p] [t] oth =
            let val arm = Ast.Appl[Ast.Constant @{syntax_const "_case1"}, p, t]
            in  (* last arm: check if OTHER defaults *)
                if oth = NONE
                then arm
                else Ast.Appl[Ast.Constant @{syntax_const "_case2"}, arm,
                       Ast.Appl[Ast.Constant @{syntax_const "_other"}, the oth]]
            end
      | make_case_arms (p::ps) (t::ts) oth =
            (* first arm, followed by others *)
            let val arms = make_case_arms ps ts oth
                val arm = Ast.Appl[Ast.Constant @{syntax_const "_case1"}, p, t]
            in  Ast.Appl[Ast.Constant @{syntax_const "_case2"}, arm, arms]
            end
    (* CASE construct without OTHER branch *)
    fun case_syntax_tr' [pTuple, tTuple] =
        let val prds = list_from_tuple pTuple
            val trms = list_from_tuple tTuple
        in  (* make sure that tuples are of equal length, otherwise give up *)
            if length prds = length trms
            then Ast.Appl[Ast.Constant @{syntax_const "_case_syntax"},
                             make_case_arms prds trms NONE]
            else Ast.Appl[Ast.Constant "Case", pTuple, tTuple]
        end
      | case_syntax_tr' _ = raise Match
    (* CASE construct with OTHER branch present *)
    fun caseother_tr' [pTuple, tTuple, oth] =
        let val prds = list_from_tuple pTuple
            val trms = list_from_tuple tTuple
        in  (* make sure that tuples are of equal length, otherwise give up *)
            if length prds = length trms
            then Ast.Appl[Ast.Constant @{syntax_const "_case_syntax"},
                             make_case_arms prds trms (SOME oth)]
            else Ast.Appl[Ast.Constant "CaseOther", pTuple, tTuple, oth]
        end
      | caseother_tr' _ = raise Match
  in
    [(@{const_syntax "Case"}, K case_syntax_tr'),
     (@{const_syntax "CaseOther"}, K caseother_tr')]
  end
\<close>

(** debugging **
(*ML \<open> set Syntax.trace_ast; \<close>*)

lemma "CASE a \<rightarrow> b \<box> c \<rightarrow> d \<box> e \<rightarrow> f \<box> OTHER \<rightarrow> g"
oops

lemma "CASE a \<rightarrow> b"
oops

lemma "CASE OTHER \<rightarrow> g"  (* degenerated case *)
oops

(*ML \<open> reset Syntax.trace_ast; \<close>*)
**)

lemmas Case_simps [simp] = CaseArm_def Case_def CaseOther_def

(** test cases **

lemma
  "i=1 \<Longrightarrow> (CASE i=0 \<rightarrow> 2 \<box> i=1 \<rightarrow> 0 \<box> i=2 \<rightarrow> 1) = 0"
by (simp add: two_def)

lemma
 "i \<notin> {0,1,2} \<Rightarrow>  (CASE i=0 \<rightarrow> 2 \<box> i=1 \<rightarrow> 0 \<box> i=2 \<rightarrow> 1) = default"
by auto

lemma
 "i \<notin> {0,1,2} \<Rightarrow>  (CASE i=0 \<rightarrow> 2 \<box> i=1 \<rightarrow> 0 \<box> i=2 \<rightarrow> 1 \<box> OTHER \<rightarrow> a) = a"
by auto

**)

end
