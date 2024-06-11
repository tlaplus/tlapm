(*  Title:      TLA+/FixedPoints.thy
    Author:     Stephan Merz, Inria Nancy
    Copyright (C) 2008-2024  INRIA and Microsoft Corporation
    License:    BSD
    Version:    Isabelle2024
*)

section \<open>Fixed points for set-theoretical constructions\<close>

theory FixedPoints
imports SetTheory
begin

text \<open>
  As a test for the encoding of \tlaplus{} set theory, we develop the
  Knaster-Tarski theorems for least and greatest fixed points in the
  subset lattice. Again, the proofs essentially follow Paulson's
  developments for Isabelle/ZF.
\<close>


subsection \<open> Monotonic operators \<close>

definition Monotonic :: "[c, c \<Rightarrow> c] \<Rightarrow> c" \<comment> \<open>monotonic operator on a domain\<close>
where "Monotonic(D,f) \<equiv> f(D) \<subseteq> D \<and> (\<forall>S,T \<in> SUBSET D : S \<subseteq> T \<Rightarrow> f(S) \<subseteq> f(T))"

lemma monotonicDomain:
  "Monotonic(D,f) \<Longrightarrow> f(D) \<subseteq> D"
by (unfold Monotonic_def, blast)

lemma monotonicSubset:
  "\<lbrakk>Monotonic(D,f); S \<subseteq> T; T \<subseteq> D\<rbrakk> \<Longrightarrow> f(S) \<subseteq> f(T)"
by (unfold Monotonic_def, blast)

lemma monotonicSubsetDomain:
  "\<lbrakk> Monotonic(D,f); S \<subseteq> D\<rbrakk> \<Longrightarrow> f(S) \<subseteq> D"
by (unfold Monotonic_def, blast)

lemma monotonicUnion:
  assumes mono: "Monotonic(D,f)" and s: "S \<subseteq> D" and t: "T \<subseteq> D"
  shows "f(S) \<union> f(T) \<subseteq> f(S \<union> T)"
proof (rule unionLUB)
  from s t show "f(S) \<subseteq> f(S \<union> T)"
    by (intro monotonicSubset[OF mono], blast+)
next
  from s t show "f(T) \<subseteq> f(S \<union> T)"
    by (intro monotonicSubset[OF mono], blast+)
qed

lemma monotonicInter:
  assumes mono: "Monotonic(D,f)" and s: "S \<subseteq> D" and t: "T \<subseteq> D"
  shows "f(S \<inter> T) \<subseteq> f(S) \<inter> f(T)"
proof (rule interGLB)
  from s t show "f(S \<inter> T) \<subseteq> f(S)"
    by (intro monotonicSubset[OF mono], blast+)
  from s t show "f(S \<inter> T) \<subseteq> f(T)"
    by (intro monotonicSubset[OF mono], blast+)
qed


subsection \<open> Least fixed point \<close>

text \<open>
  The least fixed point is defined as the greatest lower bound of
  the set of all pre-fixed points, and the Knaster-Tarski theorem
  is shown for monotonic operators.
\<close>

definition lfp :: "[c, c \<Rightarrow> c] \<Rightarrow> c"  \<comment> \<open>least fixed point as GLB of pre-fp's\<close>
where "lfp(D,f) \<equiv> INTER {S \<in> SUBSET D : f(S) \<subseteq> S}"

lemma lfpLB: \<comment> \<open>The lfp is contained in each pre-fixed point.\<close>
  "\<lbrakk> f(S) \<subseteq> S; S \<subseteq> D \<rbrakk> \<Longrightarrow> lfp(D,f) \<subseteq> S"
by (auto simp: lfp_def)

lemma lfpGLB: \<comment> \<open> \ldots{} and it is the GLB of all such sets \<close>
  "\<lbrakk>f(D) \<subseteq> D; \<And>S. \<lbrakk>f(S) \<subseteq> S; S \<subseteq> D\<rbrakk> \<Longrightarrow> A \<subseteq> S\<rbrakk> \<Longrightarrow> A \<subseteq> lfp(D,f)"
by (force simp: lfp_def)

lemma lfpSubsetDomain: "lfp(D,f) \<subseteq> D" (* monotonicity not required *)
by (auto simp: lfp_def)

lemma lfpPreFP: \<comment> \<open>@{text lfp} is a pre-fixed point \ldots \<close>
  assumes mono: "Monotonic(D,f)"
  shows "f(lfp(D,f)) \<subseteq> lfp(D,f)"
proof (rule lfpGLB)
  from mono show "f(D) \<subseteq> D" by (rule monotonicDomain)
next
  let ?mu = "lfp(D,f)"
  fix S
  assume pfp: "f(S) \<subseteq> S" and dom: "S \<subseteq> D"
  hence "?mu \<subseteq> S" by (rule lfpLB)
  from mono this dom have "f(?mu) \<subseteq> f(S)" by (rule monotonicSubset)
  with pfp show "f(?mu) \<subseteq> S" by blast
qed

lemma lfpPostFP: \<comment> \<open> \ldots{} and a post-fixed point \<close>
  assumes mono: "Monotonic(D,f)"
  shows "lfp(D,f) \<subseteq> f(lfp(D,f))"
proof -
  let ?mu = "lfp(D,f)"
  from mono lfpSubsetDomain have 1: "f(?mu) \<subseteq> D" by (rule monotonicSubsetDomain)
  from mono have "f(?mu) \<subseteq> ?mu" by (rule lfpPreFP)
  from mono this lfpSubsetDomain have "f(f(?mu)) \<subseteq> f(?mu)" by (rule monotonicSubset)
  from this 1 show ?thesis by (rule lfpLB)
qed

lemma lfpFixedPoint:
  assumes mono: "Monotonic(D,f)"
  shows "f(lfp(D,f)) = lfp(D,f)" (is "?lhs = ?rhs")
proof (rule setEqual)
  from mono show "?lhs \<subseteq> ?rhs" by (rule lfpPreFP)
next
  from mono show "?rhs \<subseteq> ?lhs" by (rule lfpPostFP)
qed

lemma lfpLeastFixedPoint:
  assumes "Monotonic(D,f)" and "S \<subseteq> D" and "f(S) = S"
  shows "lfp(D,f) \<subseteq> S"
using assms by (intro lfpLB, auto)

lemma lfpMono: \<comment> \<open> monotonicity of the @{text lfp} operator \<close>
  assumes g: "g(D) \<subseteq> D" and f: "\<And>S. S \<subseteq> D \<Longrightarrow> f(S) \<subseteq> g(S)"
  shows "lfp(D,f) \<subseteq> lfp(D,g)"
using g
proof (rule lfpGLB)
  fix S
  assume 1: "g(S) \<subseteq> S" and 2: "S \<subseteq> D"
  with f have "f(S) \<subseteq> S" by blast
  from this 2 show "lfp(D,f) \<subseteq> S" by (rule lfpLB)
qed


subsection \<open> Greatest fixed point \<close>

text \<open>
  Dually, the least fixed point is defined as the least upper bound of
  the set of all post-fixed points, and the Knaster-Tarski theorem
  is again established.
\<close>

definition gfp :: "[c, c \<Rightarrow> c] \<Rightarrow> c"  \<comment> \<open> greatest fixed point as LUB of post-fp's \<close>
where "gfp(D,f) \<equiv> UNION {S \<in> SUBSET D : S \<subseteq> f(S)}"

lemma gfpUB: \<comment> \<open> The gfp contains each post-fixed point \ldots \<close>
  "\<lbrakk>S \<subseteq> f(S); S \<subseteq> D\<rbrakk> \<Longrightarrow> S \<subseteq> gfp(D,f)"
by (auto simp: gfp_def)

lemma gfpLUB: \<comment> \<open> \ldots{} and it is the LUB of all such sets. \<close>
  "\<lbrakk>f(D) \<subseteq> D; \<And>S. \<lbrakk>S \<subseteq> f(S); S \<subseteq> D\<rbrakk> \<Longrightarrow> S \<subseteq> A\<rbrakk> \<Longrightarrow> gfp(D,f) \<subseteq> A"
by (auto simp: gfp_def)

lemma gfpSubsetDomain: "gfp(D,f) \<subseteq> D"
by (auto simp: gfp_def)

lemma gfpPostFP: \<comment> \<open> @text{gfp} is a post-fixed point \ldots \<close>
  assumes mono: "Monotonic(D,f)"
  shows "gfp(D,f) \<subseteq> f(gfp(D,f))"
proof (rule gfpLUB)
  from mono show "f(D) \<subseteq> D" by (rule monotonicDomain)
next
  let ?nu = "gfp(D,f)"
  fix S
  assume pfp: "S \<subseteq> f(S)" and dom: "S \<subseteq> D"
  hence "S \<subseteq> ?nu" by (rule gfpUB)
  from mono this gfpSubsetDomain have "f(S) \<subseteq> f(?nu)" by (rule monotonicSubset)
  with pfp show "S \<subseteq> f(?nu)" by blast
qed

lemma gfpPreFP: \<comment> \<open> \ldots{} and a pre-fixed point \<close>
  assumes mono: "Monotonic(D,f)"
  shows "f(gfp(D,f)) \<subseteq> gfp(D,f)"
proof -
  let ?nu = "gfp(D,f)"
  from mono gfpSubsetDomain have 1: "f(?nu) \<subseteq> D" by (rule monotonicSubsetDomain)
  from mono have "?nu \<subseteq> f(?nu)" by (rule gfpPostFP)
  from mono this 1 have "f(?nu) \<subseteq> f(f(?nu))" by (rule monotonicSubset)
  from this 1 show ?thesis by (rule gfpUB)
qed

lemma gfpFixedPoint:
  assumes mono: "Monotonic(D,f)"
  shows "f(gfp(D,f)) = gfp(D,f)" (is "?lhs = ?rhs")
proof (rule setEqual)
  from mono show "?lhs \<subseteq> ?rhs" by (rule gfpPreFP)
next
  from mono show "?rhs \<subseteq> ?lhs" by (rule gfpPostFP)
qed

lemma gfpGreatestFixedPoint:
  assumes "Monotonic(D,f)" and "S \<subseteq> D" and "f(S) = S"
  shows "S \<subseteq> gfp(D,f)"
using assms by (intro gfpUB, auto)

lemma gfpMono: \<comment> \<open> monotonicity of the @{text gfp} operator \<close>
  assumes g: "g(D) \<subseteq> D" and f: "\<And>S. S \<subseteq> D \<Longrightarrow> f(S) \<subseteq> g(S)"
  shows "gfp(D,f) \<subseteq> gfp(D,g)"
proof (rule gfpLUB)
  from f g show "f(D) \<subseteq> D" by blast
next
  fix S
  assume 1: "S \<subseteq> f(S)" and 2: "S \<subseteq> D"
  with f have "S \<subseteq> g(S)" by blast
  from this 2 show "S \<subseteq> gfp(D,g)" by (rule gfpUB)
qed


end
