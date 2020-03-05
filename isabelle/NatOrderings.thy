(*  Title:      TLA+/NatOrderings.thy
    Author:     Hernan Vanzetto and Stephan Merz, LORIA
    Copyright (C) 2008-2011  INRIA and Microsoft Corporation
    License:    BSD
    Version:    Isabelle2011-1
    Time-stamp: <2011-10-11 17:39:28 merz>
*)


header {* Orders on natural numbers *}

theory NatOrderings
imports Peano
begin

text {* 
  Using the sets @{text upto} we can now define the standard ordering on 
  natural numbers. The constant @{text "\<le>"} is defined over the naturals
  by the axiom (conditional definition) @{text "nat_leq_def"} below; it
  should be defined over other domains as appropriate later on.

  We generally define the constant @{text "<"} such that @{text "a<b"}
  iff @{text "a\<le>b \<and> a\<noteq>b"}, over any domain.
*}

definition leq  :: "[c,c] \<Rightarrow> c"         (infixl "<=" 50)
(*where nat_leq_def: "\<lbrakk>m \<in> Nat; n \<in> Nat\<rbrakk> \<Longrightarrow> (m <= n) \<equiv> (m \<in> upto(n))"*)
where nat_leq_def: "(m <= n) \<equiv> (m \<in> upto(n))"

abbreviation (input)
  geq  :: "[c,c] \<Rightarrow> c"         (infixl ">=" 50)
where "x >= y  \<equiv>  y <= x"

notation (xsymbols)
  leq   (infixl "\<le>" 50)  and
  geq   (infixl "\<ge>" 50)

notation (HTML output)
  leq   (infixl "\<le>" 50)  and
  geq   (infixl "\<ge>" 50)


subsection {* Operator definitions and generic facts about @{text "<"} *}

definition less :: "[c,c] \<Rightarrow> c"       (infixl "<" 50)
where "a < b  \<equiv>  a \<le> b \<and> a \<noteq> b"

abbreviation (input)
  greater :: "[c,c] \<Rightarrow> c"         (infixl ">" 50)
where "x > y  \<equiv>  y < x"

lemma boolify_less [simp]: "boolify(a < b) = (a < b)"
by (simp add: less_def)

lemma less_isBool [intro!,simp]: "isBool(a<b)"
by (simp add: less_def)

lemma less_imp_leq [elim!]: "a < b \<Longrightarrow> a \<le> b"
unfolding less_def by simp

lemma less_irrefl [simp]: "(a < a) = FALSE"
unfolding less_def by simp

lemma less_irreflE [elim!]: "a < a \<Longrightarrow> R"
by simp

lemma less_not_refl: "a < b \<Longrightarrow> a \<noteq> b"
by auto

lemma neq_leq_trans [trans]: "a \<noteq> b \<Longrightarrow> a \<le> b \<Longrightarrow> a < b"
by (simp add: less_def)

declare neq_leq_trans[simplified,trans]

lemma leq_neq_trans [trans,elim!]: "a \<le> b \<Longrightarrow> a \<noteq> b \<Longrightarrow> a < b"
by (simp add: less_def)

declare leq_neq_trans[simplified,trans]

(* Don't add to [simp]: will be tried on all disequalities! *)
lemma leq_neq_iff_less: "a \<le> b \<Longrightarrow> (a \<noteq> b) = (a < b)"
by auto

subsection {* Facts about @{text "\<le>"} over @{text Nat} *}

lemma nat_boolify_leq [simp]: "boolify(m \<le> n) = (m \<le> n)"
by (simp add: nat_leq_def)

lemma nat_leq_isBool [intro,simp]: "isBool(m \<le> n)"
by (simp add: nat_leq_def)

lemma nat_leq_refl [intro,simp]: "n \<in> Nat \<Longrightarrow> n \<le> n"
unfolding nat_leq_def by (rule uptoRefl)

lemma eq_leq_bothE:   -- {* reduce equality over integers to double inequality *}
  assumes "m \<in> Nat" and "n \<in> Nat" and "m = n" and "\<lbrakk> m \<le> n; n \<le> m \<rbrakk> \<Longrightarrow> P"
  shows "P"
using assms by simp

lemma nat_zero_leq [simp]: "n \<in> Nat \<Longrightarrow> 0 \<le> n"
unfolding nat_leq_def by (rule zeroInUpto)

lemma nat_leq_zero [simp]: "n \<in> Nat \<Longrightarrow> (n \<le> 0) = (n = 0)"
by (simp add: nat_leq_def uptoZero)

lemma nat_leq_SuccI [elim!,simp]:  (** FIXME: why simp ? **)
  assumes "m \<le> n" and "m \<in> Nat" and "n \<in> Nat"
  shows "m \<le> Succ[n]"
using assms by (auto simp: nat_leq_def uptoSucc)

lemma nat_leq_Succ:  (** FIXME: make this simp ? **)
  assumes "m \<in> Nat" and "n \<in> Nat"
  shows "(m \<le> Succ[n]) = (m \<le> n \<or> m = Succ[n])"
using assms by (auto simp: nat_leq_def uptoSucc)

lemma nat_leq_SuccE [elim]:
  assumes "m \<le> Succ[n]" and "m \<in> Nat" and "n \<in> Nat"
      and "m \<le> n \<Longrightarrow> P" and "m = Succ[n] \<Longrightarrow> P"
  shows "P"
using assms by (auto simp: nat_leq_Succ)

lemma nat_leq_limit:
  assumes "m \<le> n" and "\<not>(Succ[m] \<le> n)" and "m \<in> Nat" and "n \<in> Nat"
  shows "m=n"
using assms by (auto simp: nat_leq_def intro: uptoLimit)

lemma nat_leq_trans [trans]: 
  assumes "k \<le> m" and "m \<le> n" and "k \<in> Nat" and "m \<in> Nat" and "n \<in> Nat"
  shows "k \<le> n"
using assms by (auto simp: nat_leq_def elim: uptoTrans)

lemma nat_leq_antisym: 
  assumes "m \<le> n" and "n \<le> m" and "m \<in> Nat" and "n \<in> Nat"
  shows "m = n"
using assms by (auto simp add: nat_leq_def elim: uptoAntisym)

lemma nat_Succ_not_leq_self [simp]:
  assumes n: "n \<in> Nat"
  shows "(Succ[n] \<le> n) = FALSE"
using n by (auto dest: nat_leq_antisym)

lemma nat_Succ_leqD: 
  assumes leq: "Succ[m] \<le> n" and m: "m \<in> Nat" and n: "n \<in> Nat"
  shows "m \<le> n"
proof -
  from m have "m \<le> Succ[m]" by simp
  with leq m n show ?thesis by (elim nat_leq_trans, auto)
qed

lemma nat_Succ_leq_Succ:
  (* needn't be added to simp: consequence of nat_Succ_leq_iff_less and nat_less_Succ_iff_leq *)
  assumes m: "m \<in> Nat" and n: "n \<in> Nat"
  shows "(Succ[m] \<le> Succ[n]) = (m \<le> n)"
using m n by (auto simp: nat_leq_Succ intro: nat_leq_limit elim: nat_Succ_leqD)

lemma nat_leq_linear: "\<lbrakk>m \<in> Nat; n \<in> Nat\<rbrakk> \<Longrightarrow> m \<le> n \<or> n \<le> m"
unfolding nat_leq_def using uptoLinear .

lemma nat_leq_cases:
  assumes m: "m \<in> Nat" and n: "n \<in> Nat"
  and leq: "m \<le> n \<Longrightarrow> P" and geq: "\<lbrakk>n \<le> m; n \<noteq> m\<rbrakk> \<Longrightarrow> P"
  shows "P"
proof (cases "m \<le> n")
  case True thus "P" by (rule leq)
next
  case False
  with m n have nm: "n \<le> m" by (blast dest: nat_leq_linear)
  thus "P"
  proof (cases "n=m")
    case True
    with m have "m \<le> n" by simp
    thus "P" by (rule leq)
  next
    case False
    with nm show "P" by (rule geq)
  qed
qed

lemma nat_leq_induct:  -- {* sometimes called ``complete induction'' *}
  assumes "P(0)"
  and "\<forall>n\<in>Nat : (\<forall>m\<in>Nat : m \<le> n \<Rightarrow> P(m)) \<Rightarrow> P(Succ[n])"
  shows "\<forall>n\<in>Nat : P(n)"
proof -
  from assms have "\<forall>n\<in>Nat : \<forall>m\<in>Nat : m \<le> n \<Rightarrow> P(m)"
    by (intro natInduct, auto simp: nat_leq_Succ)
  thus ?thesis by (blast dest: nat_leq_refl)
qed

lemma nat_leq_inductE:
  assumes "n \<in> Nat"
  and "P(0)" and "\<And>n. \<lbrakk>n \<in> Nat; \<forall>m\<in>Nat : m \<le> n \<Rightarrow> P(m)\<rbrakk> \<Longrightarrow> P(Succ[n])"
  shows "P(n)"
using assms by (blast dest: nat_leq_induct)


subsection {* Facts about @{text "<"} over @{text Nat} *}

lemma nat_Succ_leq_iff_less [simp]:
  assumes "m \<in> Nat" and "n \<in> Nat"
  shows "(Succ[m] \<le> n) = (m < n)"
using assms by (auto simp: less_def dest: nat_Succ_leqD nat_leq_limit)

-- {* alternative definition of @{text "<"} over @{text Nat} *}
lemmas nat_less_iff_Succ_leq = sym[OF nat_Succ_leq_iff_less, standard]

text {* Reduce @{text "\<le>"} to @{text "<"}. *}

lemma nat_leq_less: -- {* premises needed for @{text "isBool(m\<le>n)"} and reflexivity *}
  assumes "m \<in> Nat" and "n \<in> Nat"
  shows "m \<le> n = (m < n \<or> m = n)"
using assms by (auto simp: less_def)

lemma nat_less_Succ_iff_leq [simp]:
  assumes "m \<in> Nat" and "n \<in> Nat"
  shows "(m < Succ[n]) = (m \<le> n)"
using assms
by (simp del: nat_Succ_leq_iff_less add: nat_less_iff_Succ_leq nat_Succ_leq_Succ)

lemmas nat_leq_iff_less_Succ = sym[OF nat_less_Succ_iff_leq, standard]

lemma nat_not_leq_one:
  assumes "n \<in> Nat"
  shows "(\<not>(1 \<le> n)) = (n = 0)"
using assms by (cases, auto)

declare nat_not_leq_one[simplified,simp]

text {* @{text "<"} and @{text "Succ"}. *}

lemma nat_Succ_less_mono:
  assumes "m \<in> Nat" and "n \<in> Nat"
  shows "(Succ[m] < Succ[n]) = (m < n)"
using assms by simp

lemma nat_Succ_less_SuccE:
  assumes "Succ[m] < Succ[n]" and "m \<in> Nat" and "n \<in> Nat" and "m < n \<Longrightarrow> P"
  shows "P"
using assms by simp

lemma nat_not_less0 [simp]: 
  assumes "n \<in> Nat"
  shows "(n < 0) = FALSE"
using assms by (auto simp: less_def)

lemma nat_less0E (*[elim!]*):
  assumes "n < 0" and "n \<in> Nat"
  shows "P"
using assms by simp

lemma nat_less_SuccI: 
  assumes "m < n" and "m \<in> Nat" and "n \<in> Nat"
  shows "m < Succ[n]"
using assms by auto

lemma nat_Succ_lessD: 
  assumes 1: "Succ[m] < n" and 2: "m \<in> Nat" and 3: "n \<in> Nat"
  shows "m < n"
using 1[unfolded less_def] 2 3 by simp

lemma nat_less_leq_not_leq:
  assumes m: "m \<in> Nat" and n: "n \<in> Nat"
  shows "(m < n) = (m \<le> n \<and> \<not> n \<le> m)"
using assms by (auto simp: less_def dest: nat_leq_antisym)

text {* Transitivity. *}

lemma nat_less_trans (*[trans]*):
  assumes "k < m" and "m < n" and "k \<in> Nat" and "m \<in> Nat" and "n \<in> Nat"
  shows "k < n"
using assms by (auto simp: less_def dest: nat_leq_trans nat_leq_antisym)

lemma nat_less_trans_Succ [trans]:
  assumes lt1: "i < j" and lt2: "j < k"
      and i: "i \<in> Nat" and j: "j \<in> Nat" and k: "k \<in> Nat"
  shows "Succ[i] < k"
proof -
  from i j lt1 have "Succ[Succ[i]] \<le> Succ[j]" by simp
  also from j k lt2 have "Succ[j] \<le> k" by simp
  finally show ?thesis using i j k by simp
qed

lemma nat_leq_less_trans [trans]:
  assumes "k \<le> m" and "m < n" and "k \<in> Nat" and "m \<in> Nat" and "n \<in> Nat"
  shows "k < n"
using assms by (auto simp: less_def dest: nat_leq_trans nat_leq_antisym)

lemma nat_less_leq_trans [trans]: 
  assumes "k < m" and "m \<le> n" and "k \<in> Nat" and "m \<in> Nat" and "n \<in> Nat"
  shows "k < n"
using assms by (auto simp: less_def dest: nat_leq_trans nat_leq_antisym)

text {* Asymmetry. *}

lemma nat_less_not_sym: 
  assumes "m < n" and "m \<in> Nat" and "n \<in> Nat"
  shows "(n < m) = FALSE"
using assms by (simp add: nat_less_leq_not_leq)

lemma nat_less_asym: 
  assumes "m < n" and "m \<in> Nat" and "n \<in> Nat" and "\<not>P \<Longrightarrow> n < m"
  shows "P"
proof (rule contradiction)
  assume "\<not>P" with assms show "FALSE" by (auto dest: nat_less_not_sym)
qed

text {* Linearity (totality). *}

lemma nat_less_linear: 
  assumes m: "m \<in> Nat" and n: "n \<in> Nat"
  shows "m < n \<or> m = n \<or> n < m"
unfolding less_def using nat_leq_linear[OF m n] by blast

lemma nat_leq_less_linear: 
  assumes m: "m \<in> Nat" and n: "n \<in> Nat"
  shows "m \<le> n \<or> n < m"
using assms nat_less_linear[OF m n] by (auto simp: less_def)

lemma nat_less_cases [case_names less equal greater]:
  assumes m: "m \<in> Nat" and n: "n \<in> Nat"
  shows "(m < n \<Longrightarrow> P) \<Longrightarrow> (m = n \<Longrightarrow> P) \<Longrightarrow> (n < m \<Longrightarrow> P) \<Longrightarrow> P"
using nat_less_linear[OF m n] by blast

lemma nat_not_less:
  assumes m: "m \<in> Nat" and n: "n \<in> Nat"
  shows "(\<not> m < n) = (n \<le> m)"
using assms nat_leq_linear[OF m n] by (auto simp: less_def dest: nat_leq_antisym)

lemma nat_not_less_iff_gr_or_eq:
  assumes m: "m \<in> Nat" and n: "n \<in> Nat"
  shows "(\<not> m < n) = (m > n \<or> m = n)"
unfolding nat_not_less[OF m n] using assms by (auto simp: less_def)

lemma nat_not_less_eq: 
  assumes m: "m \<in> Nat" and n: "n \<in> Nat"
  shows "(\<not> m < n) = (n < Succ[m])"
unfolding nat_not_less[OF m n] using assms by simp

lemma nat_not_leq:
  assumes m: "m \<in> Nat" and n: "n \<in> Nat"
  shows "(\<not> m \<le> n) = (n < m)"
using assms by (simp add: sym[OF nat_not_less])

-- {* often useful, but not active by default *}
lemmas nat_not_order_simps[simplified] = nat_not_less nat_not_leq

lemma nat_not_leq_eq: 
  assumes m: "m \<in> Nat" and n: "n \<in> Nat"
  shows "(\<not> m \<le> n) = (Succ[n] \<le> m)"
unfolding nat_not_leq[OF m n] using assms by simp

lemma nat_neq_iff: 
  assumes m: "m \<in> Nat" and n: "n \<in> Nat"
  shows "m \<noteq> n = (m < n \<or> n < m)"
using assms nat_less_linear[OF m n] by auto

lemma nat_neq_lessE:
  assumes "m \<noteq> n" and "m \<in> Nat" and "n \<in> Nat"
  shows "(m < n \<Longrightarrow> R) \<Longrightarrow> (n < m \<Longrightarrow> R) \<Longrightarrow> R"
using assms by (auto simp: nat_neq_iff[simplified])

lemma nat_antisym_conv1: 
  assumes "\<not>(m < n)" and "m \<in> Nat" and "n \<in> Nat"
  shows "(m \<le> n) = (m = n)"
using assms by (auto simp: nat_leq_less)

lemma nat_antisym_conv2: 
  assumes "m \<le> n" and "m \<in> Nat" and "n \<in> Nat"
  shows "(\<not> m < n) = (m = n)"
using assms by (auto simp: nat_antisym_conv1)

lemma nat_antisym_conv3: 
  assumes "\<not> n < m" and "m \<in> Nat" and "n \<in> Nat"
  shows "(\<not> m < n) = (m = n)"
using assms by (auto simp: nat_not_order_simps elim: nat_leq_antisym)

lemma nat_not_lessD: 
  assumes "\<not>(m < n)" and "m \<in> Nat" and "n \<in> Nat"
  shows "n \<le> m"
using assms by (simp add: nat_not_order_simps)

lemma nat_not_lessI:
  assumes "n \<le> m" and "m \<in> Nat" and "n \<in> Nat"
  shows "\<not>(m < n)"
using assms by (simp add: nat_not_order_simps)

lemma nat_gt0_not0 (*[simp]*):
  assumes "n \<in> Nat"
  shows "(0 < n) = (n \<noteq> 0)"
using assms by (auto simp: nat_neq_iff[simplified])

lemmas nat_neq0_conv = sym[OF nat_gt0_not0, standard]

text {* Introduction properties *}

lemma nat_less_Succ_self (*[iff]*):
  assumes "n \<in> Nat"
  shows "n < Succ[n]"
using assms by simp

lemma nat_zero_less_Succ (*[iff]*):
  assumes "n \<in> Nat"
  shows "0 < Succ[n]"
using assms by simp

text {* Elimination properties. *}

lemma nat_less_Succ:
  assumes "m \<in> Nat" and "n \<in> Nat"
  shows "(m < Succ[n]) = (m < n \<or> m = n)"
using assms by (simp add: nat_leq_less)

lemma nat_less_SuccE:
  assumes "m < Succ[n]" and "m \<in> Nat" and "n \<in> Nat"
      and "m < n \<Longrightarrow> P" and "m = n \<Longrightarrow> P"
  shows P
using assms by (auto simp: nat_leq_less)

lemma nat_less_one (*[simp]*):
  assumes "n \<in> Nat"
  shows "(n < 1) = (n = 0)"
using assms by simp

text {* "Less than" is antisymmetric, sort of. *}

lemma nat_less_antisym: 
  assumes m: "m \<in> Nat" and n: "n \<in> Nat"
  shows "\<lbrakk> \<not>(n < m); n < Succ[m] \<rbrakk> \<Longrightarrow> m = n"
using assms by (auto simp: nat_not_order_simps elim: nat_leq_antisym)

text {* Lifting @{text "<"} monotonicity to @{text "\<le>"} monotonicity. *}
lemma less_mono_imp_leq_mono:
  assumes i: "i \<in> Nat" and j: "j \<in> Nat" and f: "\<forall>n \<in> Nat : f(n) \<in> Nat"
  and ij: "i \<le> j" and mono: "\<And>i j. \<lbrakk>i \<in> Nat; j \<in> Nat; i<j\<rbrakk> \<Longrightarrow> f(i) < f(j)"
  shows "f(i) \<le> f(j)"
using ij proof (auto simp: nat_leq_less[OF i j])
  assume "i < j" 
  with i j have "f(i) < f(j)" by (rule mono)
  thus "f(i) \<le> f(j)" by (simp add: less_imp_leq)
next
  from j f show "f(j) \<le> f(j)" by auto
qed

text {* Inductive (?) properties. *}

lemma nat_Succ_lessI:
  assumes "m \<in> Nat" and "n \<in> Nat" and "m < n" and "Succ[m] \<noteq> n"
  shows "Succ[m] < n"
using assms by (simp add: leq_neq_iff_less[simplified])

lemma nat_lessE:
  assumes major: "i < k" and i: "i \<in> Nat" and k: "k \<in> Nat"
  obtains j where "j \<in> Nat" and "i \<le> j" and "k = Succ[j]"
proof -
  from k major have "\<exists>j\<in>Nat : i \<le> j \<and> k = Succ[j]"
  proof (induct k)
    case 0 with i show ?case by simp
  next
    fix n
    assume n: "n \<in> Nat" and 1: "i < Succ[n]"
      and ih: "i < n \<Longrightarrow> \<exists>j\<in>Nat : i \<le> j \<and> n = Succ[j]"
    from i n 1 have "i < n \<or> i = n" by (simp add: nat_leq_less)
    thus "\<exists>j\<in>Nat : i \<le> j \<and> Succ[n] = Succ[j]"
    proof
      assume "i < n"
      then obtain j where "j \<in> Nat" and "i \<le> j" and "n = Succ[j]"
        by (blast dest: ih)
      with i have "Succ[j] \<in> Nat" and "i \<le> Succ[j]" and "Succ[n] = Succ[Succ[j]]"
        by auto
      thus ?thesis by blast
    next
      assume "i = n"
      with i show ?thesis by blast
    qed
  qed
  with that show ?thesis by blast
qed

lemma nat_Succ_lessE:
  assumes major: "Succ[i] < k" and i: "i \<in> Nat" and k: "k \<in> Nat"
  obtains j where "j \<in> Nat" and "i < j" and "k = Succ[j]"
using assms by (auto elim: nat_lessE)

lemma nat_gt0_implies_Succ:
  assumes 1: "0 < n" and 2: "n \<in> Nat"
  shows "\<exists>m : m \<in> Nat \<and> n = Succ[m]"
using 2 1 by (cases, auto)

lemma nat_gt0_iff_Succ:
  assumes n: "n \<in> Nat"
  shows "(0 < n) = (\<exists>m \<in> Nat: n = Succ[m])"
using n by (auto dest: nat_gt0_implies_Succ)

lemma nat_less_Succ_eq_0_disj: 
  assumes "m \<in> Nat" and "n \<in> Nat"
  shows "(m < Succ[n]) = (m = 0 \<or> (\<exists>j\<in>Nat: m = Succ[j] \<and> j < n))"
using assms by (induct m, auto)

lemma nat_less_antisym_false: "\<lbrakk>m < n; m \<in> Nat; n \<in> Nat\<rbrakk> \<Longrightarrow> n < m = FALSE"
  unfolding less_def using nat_leq_antisym by auto

lemma nat_less_antisym_leq_false: "\<lbrakk>m < n; m \<in> Nat; n \<in> Nat\<rbrakk> \<Longrightarrow> n \<le> m = FALSE"
  unfolding less_def using nat_leq_antisym[of m n] by auto


subsection {* Intervals of natural numbers *}

definition natInterval :: "[c,c] \<Rightarrow> c"    ("(_ .. _)" [90,90] 70)
where "m .. n \<equiv> { k \<in> Nat : m \<le> k \<and> k \<le> n }"

lemma inNatIntervalI [intro!,simp]:
  assumes "k \<in> Nat" and "m \<le> k" and "k \<le> n"
  shows "k \<in> m .. n"
using assms by (simp add: natInterval_def)

lemma inNatIntervalE [elim]:
  assumes 1: "k \<in> m .. n" and 2: "\<lbrakk>k \<in> Nat; m \<le> k; k \<le> n\<rbrakk> \<Longrightarrow> P"
  shows P
using 1 by (intro 2, auto simp add: natInterval_def)

lemma inNatInterval_iff: "(k \<in> m .. n) = (k \<in> Nat \<and> m \<le> k \<and> k \<le> n)"
using assms by auto

lemmas
  setEqualI [where A = "m .. n", standard, intro]
  setEqualI [where B = "m .. n", standard, intro]

lemma lowerInNatInterval [iff]:
  assumes "m \<le> n" and "m \<in> Nat"
  shows "m \<in> m .. n"
using assms by (simp add: natInterval_def)

lemma upperInNatInterval [iff]:
  assumes "m \<le> n" and "n \<in> Nat"
  shows "n \<in> m .. n"
using assms by (simp add: natInterval_def)

lemma gtNotinNatInterval:
  assumes gt: "m > n" and k: "k \<in> m .. n" and m: "m \<in> Nat" and n: "n \<in> Nat"
  shows "P"
proof -
  from k have 1: "m \<le> k" and 2: "k \<le> n" and 3: "k \<in> Nat" by auto
  from 1 2 m 3 n have "m \<le> n" by (rule nat_leq_trans)
  with m n have "\<not>(n < m)" by (simp add: nat_not_order_simps)
  from this gt show ?thesis ..
qed

lemma natIntervalIsEmpty:
  assumes "m \<in> Nat" and "n \<in> Nat" and "m > n"
  shows "m .. n = {}"
using assms by (blast dest: gtNotinNatInterval)

lemma natIntervalEmpty_iff:
  assumes m: "m \<in> Nat" and n: "n \<in> Nat"
  shows "(m .. n = {}) = (m > n)"
proof (auto dest: natIntervalIsEmpty[OF m n])
  assume mt: "m .. n = {}"
  show "n < m"
  proof (rule contradiction)
    assume "\<not>(n < m)"
    with m n have "m \<le> n" by (simp add: nat_not_order_simps)
    from this m have "m \<in> m .. n" by (rule lowerInNatInterval)
    with mt show "FALSE" by blast
  qed
qed

lemma natIntervalSingleton [simp]:
  assumes "n \<in> Nat"
  shows "n .. n = {n}"
using assms by (auto dest: nat_leq_antisym)

lemma natIntervalSucc [simp]:
  assumes "m \<in> Nat" and "n \<in> Nat" and "m \<le> Succ[n]"
  shows "m .. Succ[n] = addElt(Succ[n], m .. n)"
using assms by (auto simp: natInterval_def)

lemma succNatInterval:
  assumes "m \<in> Nat" and "n \<in> Nat"
  shows "Succ[m] .. n = (m .. n \<setminus> {m})"
using assms by (auto simp: natInterval_def)

lemma natIntervalEqual_iff:
  assumes k: "k \<in> Nat" and l: "l \<in> Nat" and m: "m \<in> Nat" and n: "n \<in> Nat"
  shows "(k .. l = m .. n) = ((k > l \<and> m > n) \<or> (k = m \<and> l = n))" (is "?lhs = ?rhs")
proof -
  have 1: "?lhs \<Rightarrow> ?rhs"
  proof
    assume eq: "?lhs"
    show ?rhs
    proof (cases "k .. l = {}")
      case True
      with k l have "k > l" by (simp only: natIntervalEmpty_iff)
      moreover
      from True eq m n have "m > n" by (simp only: natIntervalEmpty_iff)
      ultimately
      show ?rhs by blast
    next
      case False
      with k l have 11: "k \<le> l" by (simp only: natIntervalEmpty_iff nat_not_less)
      from False eq m n have 12: "m \<le> n" by (simp only: natIntervalEmpty_iff nat_not_less)
      from 11 k eq have 13: "m \<le> k" by auto
      from 12 m eq have 14: "k \<le> m" by auto
      from 14 13 k m have 15: "k = m" by (rule nat_leq_antisym)
      from 11 l eq have 16: "l \<le> n" by auto
      from 12 n eq have 17: "n \<le> l" by auto
      from 16 17 l n have "l = n" by (rule nat_leq_antisym)
      with 15 show ?rhs by blast
    qed
  qed
  have 2: "?rhs \<Rightarrow> ?lhs"
  proof auto
    assume lk: "l < k" and nm: "n < m"
    from k l lk have "k .. l = {}" by (rule natIntervalIsEmpty)
    moreover
    from m n nm have "m .. n = {}" by (rule natIntervalIsEmpty)
    ultimately
    show ?lhs by auto
  qed
  from 1 2 show ?thesis by blast
qed

lemma zerotoInj [simp]:
  assumes "l \<in> Nat" and "m \<in> Nat" and "n \<in> Nat"
  shows "(0 .. l = m .. n) = (m=0 \<and> l=n)"
using assms by (auto simp: natIntervalEqual_iff)

lemma zerotoInj' [simp]:
  assumes "k \<in> Nat" and "l \<in> Nat" and "n \<in> Nat"
  shows "(k .. l = 0 .. n) = (k=0 \<and> l=n)"
using assms by (auto simp: natIntervalEqual_iff)

lemma zerotoEmpty [simp]:
  assumes "m \<in> Nat"
  shows "Succ[m] .. 0 = {}"
using assms by auto

lemma onetoInj [simp]:
  assumes "l \<in> Nat" and "m \<in> Nat" and "n \<in> Nat" and "l\<noteq>0 \<or> m=1"
  shows "(1 .. l = m .. n) = (m=1 \<and> l=n)"
using assms by (auto simp: natIntervalEqual_iff)

lemma onetoInj' [simp]:
  assumes "k \<in> Nat" and "l \<in> Nat" and "n \<in> Nat" and "n\<noteq>0 \<or> k=1"
  shows "(k .. l = 1 .. n) = (k=1 \<and> l=n)"
using assms by (auto simp: natIntervalEqual_iff)

lemma SuccInNatIntervalSucc:
  assumes "m \<le> k" and "k \<in> Nat" and "m \<in> Nat" and "n \<in> Nat"
  shows "(Succ[k] \<in> m .. Succ[n]) = (k \<in> m .. n)"
using assms by auto

lemma SuccInNatIntervalSuccSucc:
  assumes "k \<in> Nat" and "m \<in> Nat" and "n \<in> Nat"
  shows "(Succ[k] \<in> Succ[m] .. Succ[n]) = (k \<in> m .. n)"
using assms by auto

end
