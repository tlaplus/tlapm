theory Tests
  imports Constant
begin
text \<open>
This theory only acts as a test suite to check for regressions.
The test cases should be proved by \<open>auto\<close>, because that's the
default method used by TLAPM.
\<close>


section \<open>Interference of \<open>Nat\<close> and \<open>\<forall>\<close> elimination.\<close>

text \<open>After upgrading theories from Isabelle-2011 to Isabelle-202X
an interference of \<open>x \<in> Nat \<equiv> x \<in> Int \<and> 0 \<le> x\<close> and \<open>\<forall>\<close> elimination
was introduced. The former rule rewrites assumptions and then the
\<open>bAllE\<close> elimination rule don't apply anymore.\<close>

lemma
  fixes P
  assumes "\<forall>e : e \<in> Nat \<Rightarrow> P(e)"
  shows "\<And>e. e \<in> Nat \<Longrightarrow> P(e)"
  using assms
  by auto


text \<open>This lemma was passing with "blast" and failing with auto
until "lemma bspec' [dest]" was added. It was working with "auto"
in Isabelle-2011, so can be considered a regression.\<close>
lemma
  fixes P Q e
  assumes "e \<in> Nat" and "P(e)" and "\<forall>e \<in> Nat : (P(e) \<Rightarrow> Q(e))"
  shows "Q(e)"
  using assms
  by auto



text \<open>Only started to work after \<open>bAll_unb [simp]\<close> was added.\<close>
lemma
  assumes "RR (0)"
  assumes "\<And> i :: c. i \<in> Nat \<Longrightarrow> RR(i) \<Longrightarrow> RR(F(i))"
  assumes "\<And> PP :: c => c.
              PP (0) \<Longrightarrow>
              (\<forall>n\<in>Nat : PP(n) \<Rightarrow> PP(F(n))) \<Longrightarrow>
              (\<forall>n\<in>Nat : PP(n))"
  shows "\<forall> ii \<in> Nat : RR (ii)"
  using assms
  by auto


end
