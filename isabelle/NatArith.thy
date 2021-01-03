(*  Title:      TLA+/NatArith.thy
    Author:     Hernan Vanzetto, LORIA
    Copyright (C) 2009-2021  INRIA and Microsoft Corporation
    License:    BSD
    Version:    Isabelle2020
*)

section \<open> Arithmetic (except division) over natural numbers \<close>

theory NatArith
imports NatOrderings
begin

named_theorems algebra_simps "algebra simplification rules"

(*
ML \<open>
structure AlgebraSimps =
  Named_Thms(val name = "algebra_simps"
               val description = "algebra simplification rules");
\<close>

setup AlgebraSimps.setup
*)

text \<open>
  The rewrites accumulated in @{text algebra_simps} deal with the
  classical algebraic structures of groups, rings and family. They simplify
  terms by multiplying everything out (in case of a ring) and bringing sums and
  products into a canonical form (by ordered rewriting). As a result these
  rewrites decide group and ring equalities but also help with inequalities.

  Of course it also works for fields, but it knows nothing about multiplicative
  inverses or division. This should be catered for by @{text field_simps}.
\<close>


subsection \<open> Addition of natural numbers \<close>

definition addnat
where "addnat(m) \<equiv> CHOOSE g \<in> [Nat \<rightarrow> Nat] : g[0] = m \<and> (\<forall>x \<in> Nat : g[Succ[x]] = Succ[g[x]])"

definition arith_add  :: "[c,c] \<Rightarrow> c"         (infixl "+" 65)
where nat_add_def: "\<lbrakk>m \<in> Nat; n \<in> Nat\<rbrakk> \<Longrightarrow> (m + n) \<equiv> addnat(m)[n]"

text \<open> Closure \<close>

lemma addnatType:
  assumes "m \<in> Nat" shows "addnat(m) \<in> [Nat \<rightarrow> Nat]"
using assms unfolding addnat_def by (rule bprimrecType_nat, auto)

lemma addIsNat [intro!,simp]:
  assumes "m \<in> Nat" and "n \<in> Nat" shows "m + n \<in> Nat"
unfolding nat_add_def[OF assms] using assms addnatType by blast

text \<open> Base case and Inductive case \<close>

lemma addnat_0:
  assumes "m \<in> Nat" shows "addnat(m)[0] = m"
using assms unfolding addnat_def by (rule primrec_natE, auto)

lemma add_0_nat [simp]:
  assumes "m \<in> Nat" shows "m + 0 = m"
by (simp add: nat_add_def[OF assms] addnat_0[OF assms])

lemma addnat_Succ:
  assumes m: "m \<in> Nat" and n: "n \<in> Nat"
  shows "addnat(m)[Succ[n]] = Succ[addnat(m)[n]]"
proof (rule primrec_natE[OF m])
  show "addnat(m) = (CHOOSE g \<in> [Nat \<rightarrow> Nat] : g[0] = m \<and> (\<forall>x \<in> Nat : g[Succ[x]] = Succ[g[x]]))"
    unfolding addnat_def ..
next
  assume "\<forall>n \<in> Nat : addnat(m)[Succ[n]] = Succ[addnat(m)[n]]"
  with n show "addnat(m)[Succ[n]] = Succ[addnat(m)[n]]" by blast
qed (auto)

lemma add_Succ_nat [simp]:
  assumes "m \<in> Nat" and "n \<in> Nat"
  shows "m + Succ[n] = Succ[m + n]"
using assms by (simp add: nat_add_def addnat_Succ[OF assms])

lemma add_0_left_nat [simp]:
  assumes n: "n \<in> Nat"
  shows "0 + n = n"
using n by (induct, auto)

lemma add_Succ_left_nat [simp]:
  assumes n: "n \<in> Nat" and m: "m \<in> Nat"
  shows "Succ[m] + n = Succ[m + n]"
using n apply induct
using m by auto

lemma add_Succ_shift_nat:
  assumes n: "n \<in> Nat" and m: "m \<in> Nat"
  shows "Succ[m] + n = m + Succ[n]"
using assms by simp

text \<open> Commutativity \<close>

lemma add_commute_nat [algebra_simps]:
  assumes m: "m \<in> Nat" and n: "n \<in> Nat"
  shows "m + n = n + m"
using n apply induct
using assms by auto

text \<open> Associativity \<close>

lemma add_assoc_nat [algebra_simps]:
  assumes m: "m \<in> Nat" and n: "n \<in> Nat" and p: "p \<in> Nat"
  shows "m + (n + p) = (m + n) + p"
using assms by (induct, simp_all)

text \<open> Cancellation rules \<close>

lemma add_left_cancel_nat [simp]:
  assumes m: "m \<in> Nat" and n: "n \<in> Nat" and p: "p \<in> Nat"
  shows "(m + n = m + p) = (n = p)"
using assms by (induct, simp_all)

lemma add_right_cancel_nat [simp]:
  assumes m: "m \<in> Nat" and n: "n \<in> Nat" and p: "p \<in> Nat"
  shows "(n + m = p + m) = (n = p)"
using assms by (induct, simp_all)


lemma add_left_commute_nat [algebra_simps]:
  assumes a: "a \<in> Nat" and b: "b \<in> Nat" and c: "c \<in> Nat"
  shows "a + (b + c) = b + (a + c)"
using assms by(simp only: add_assoc_nat add_commute_nat)

(* from HOL/OrderedGroups.thy *)
lemmas add_ac_nat = add_assoc_nat add_commute_nat add_left_commute_nat

text \<open> Reasoning about @{text "m + n = 0"}, etc. \<close>

lemma add_is_0_nat [iff]:
  assumes m: "m \<in> Nat" and n: "n \<in> Nat"
  shows "(m + n = 0) = (m = 0 \<and> n = 0)"
using m apply (rule natCases)
using n by (induct, auto)

lemma add_is_1_nat:
  assumes m: "m \<in> Nat" and n: "n \<in> Nat"
  shows "(m + n = 1) = (m = 1 \<and> n = 0 \<or> m = 0 \<and> n = 1)"
using m apply (rule natCases)
using n by (induct, auto)

lemma one_is_add_nat:
  assumes m: "m \<in> Nat" and n: "n \<in> Nat"
  shows "(1 = m + n) = (m = 1 \<and> n = 0 \<or> m = 0 \<and> n = 1)"
using m apply (rule natCases)
using n by (induct, auto)+

lemma add_eq_self_zero_nat1 [simp]:
  assumes m: "m \<in> Nat" and n: "n \<in> Nat"
  shows "(m + n = m) = (n = 0)"
using n apply (rule natCases)
  using m apply simp
  using m apply induct apply auto
done

lemma add_eq_self_zero_nat2 [simp]:
  assumes m: "m \<in> Nat" and n: "n \<in> Nat"
  shows "(n + m = m) = (n = 0)"
using assms by (simp add: add_commute_nat)


subsection \<open> Multiplication of natural numbers \<close>

definition multnat
where "multnat(m) \<equiv> CHOOSE g \<in> [Nat \<rightarrow> Nat] : g[0] = 0 \<and> (\<forall>x \<in> Nat : g[Succ[x]] = g[x] + m)"

definition mult :: "[c,c] \<Rightarrow> c"       (infixl "*" 70)
where nat_mult_def: "\<lbrakk>m \<in> Nat; n \<in> Nat\<rbrakk> \<Longrightarrow> m * n \<equiv> multnat(m)[n]"

text \<open> Closure \<close>

lemma multnatType:
  assumes "m \<in> Nat" shows "multnat(m) \<in> [Nat \<rightarrow> Nat]"
unfolding multnat_def by (rule bprimrecType_nat, auto simp: assms)

lemma multIsNat [intro!, simp]:
  assumes m: "m \<in> Nat" and n: "n \<in> Nat"
  shows "m * n \<in> Nat"
unfolding nat_mult_def[OF assms] using assms multnatType by blast

text \<open> Base case and Inductive step \<close>

lemma multnat_0:
  assumes "m \<in> Nat" shows "multnat(m)[0] = 0"
unfolding multnat_def by (rule primrec_natE, auto simp: assms)

lemma mult_0_nat [simp]:  \<comment> \<open> neutral element \<close>
  assumes n: "n \<in> Nat" shows "n * 0 = 0"
by (simp add: nat_mult_def[OF assms] multnat_0[OF assms])


lemma multnat_Succ:
  assumes m: "m \<in> Nat" and n: "n \<in> Nat"
  shows "multnat(m)[Succ[n]] = multnat(m)[n] + m"
proof (rule primrec_natE)
  show "multnat(m) = (CHOOSE g \<in> [Nat \<rightarrow> Nat] : g[0] = 0 \<and> (\<forall>x \<in> Nat : g[Succ[x]] = g[x] + m))"
    unfolding multnat_def ..
next
  assume "\<forall>n \<in> Nat : multnat(m)[Succ[n]] = multnat(m)[n] + m"
  with n show "multnat(m)[Succ[n]] = multnat(m)[n] + m" by blast
qed (auto simp: m)

lemma mult_Succ_nat [simp]:
  assumes "m \<in> Nat" and "n \<in> Nat"
  shows "m * Succ[n] = m * n + m"
using assms by (simp add: nat_mult_def multnat_Succ[OF assms])

lemma mult_0_left_nat [simp]:
  assumes n: "n \<in> Nat"
  shows "0 * n = 0"
using n by (induct, simp_all)

lemma mult_Succ_left_nat [simp]:
  assumes m: "m \<in> Nat" and n: "n \<in> Nat"
  shows "Succ[m] * n = m * n + n"
using n apply induct
using m by (simp_all add: add_ac_nat)

text \<open> Commutativity \<close>

lemma mult_commute_nat [algebra_simps]:
  assumes m: "m \<in> Nat" and n: "n \<in> Nat"
  shows "m * n = n * m"
using assms by (induct, simp_all)

text \<open> Distributivity \<close>

lemma add_mult_distrib_left_nat [algebra_simps]:
  assumes m: "m \<in> Nat" and n: "n \<in> Nat" and p: "p \<in> Nat"
  shows "m * (n + p) = m * n + m * p"
using assms apply induct
proof auto
  fix m
  assume "m \<in> Nat" "m * (n + p) = m * n + m * p"
  with n p
    add_assoc_nat[of "m * n + m * p" n p]
    add_assoc_nat[of "m * n" "m * p" n]
    add_commute_nat[of "m * p" n]
    add_assoc_nat[of "m * n" n "m * p"]
    add_assoc_nat[of "m * n + n" "m * p" p]
  show "m * n + m * p + (n + p) = m * n + n + (m * p + p)"
    by simp
qed

lemma add_mult_distrib_right_nat [algebra_simps]:
  assumes m: "m \<in> Nat" and n: "n \<in> Nat" and p: "p \<in> Nat"
  shows "(n + p) * m = n * m + p * m"
using m apply induct
using n p apply auto
proof -
  fix m
  assume "m \<in> Nat" "(n + p) * m = n * m + p * m"
  with n p
    add_assoc_nat[of "n * m + p * m" n p]
    add_assoc_nat[of "n * m" "p * m" n]
    add_commute_nat[of "p * m" n]
    add_assoc_nat[of "n * m" n "p * m"]
    add_assoc_nat[of "n * m + n" "p * m" p]
  show "n * m + p * m + (n + p) = n * m + n + (p * m + p)"
    by simp
qed

text \<open> Identity element \<close>

(* used for arithmetic simplification setup *)
lemma mult_1_right_nat: "a \<in> Nat \<Longrightarrow> a * 1 = a" by simp
lemma mult_1_left_nat: "a \<in> Nat \<Longrightarrow> 1 * a = a" by simp

text \<open> Associativity \<close>

lemma mult_assoc_nat[algebra_simps]:
  assumes m: "m \<in> Nat" and n: "n \<in> Nat" and p: "p \<in> Nat"
  shows "m * (n * p) = (m * n) * p"
using m apply induct
using assms by (auto simp add: add_mult_distrib_right_nat)

text \<open> Reasoning about @{text "m * n = 0"}, etc. \<close>

lemma mult_is_0_nat [simp]:
  assumes m: "m \<in> Nat" and n: "n \<in> Nat"
  shows "(m * n = 0) = (m = 0 \<or> n = 0)"
using m apply induct
using n by auto

lemma mult_eq_1_iff_nat [simp]:
  assumes m: "m \<in> Nat" and n: "n \<in> Nat"
  shows "(m * n = 1) = (m = 1 \<and> n = 1)"
using m apply induct
using n by (induct, auto)+

lemma one_eq_mult_iff_nat [simp]:
  assumes m: "m \<in> Nat" and n: "n \<in> Nat"
  shows "(1 = m * n) = (m = 1 \<and> n = 1)"
proof -
  have "(1 = m * n) = (m * n = 1)" by auto
  also from assms have "... = (m = 1 \<and> n = 1)" by simp
  finally show ?thesis .
qed

text \<open> Cancellation rules \<close>

lemma mult_cancel1_nat [simp]:
  assumes k: "k \<in> Nat" and m: "m \<in> Nat" and n: "n \<in> Nat"
  shows "(k * m = k * n) = (m = n \<or> (k = 0))"
proof -
  have "k \<noteq> 0 \<Longrightarrow> k * m = k * n \<Longrightarrow> m = n"
  using n m proof (induct arbitrary: m)
    fix m
    assume "k \<noteq> 0" "k * m = k * 0" "m \<in> Nat"
    with k show "m = 0" by simp
  next
    fix n m
    assume
      n': "n \<in> Nat" and h1:"\<And>m. \<lbrakk>k \<noteq> 0; k * m = k * n; m \<in> Nat\<rbrakk> \<Longrightarrow> m = n"
      and k0: "k \<noteq> 0" and h2: "k * m = k * Succ[n]" and m':"m \<in> Nat"
    from m' show "m = Succ[n]"
    proof (rule natCases)
      assume "m = 0"
      with k have "k * m = 0" by simp
      moreover
      from k k0 n' have "k * Succ[n] \<noteq> 0" by simp
      moreover
      note h2
      ultimately show ?thesis by simp
    next
      fix w
      assume w:"w \<in> Nat" and h3:"m = Succ[w]"
      with k n' h2 have "k * w = k * n" by simp
      with k k0 w h1[of w] h3 show ?thesis by simp
      qed
    qed
    with k m n show ?thesis by auto
qed

lemma mult_cancel2_nat [simp]:
  assumes m: "m \<in> Nat" and n: "n \<in> Nat" and k: "k \<in> Nat"
  shows "(m * k = n * k) = (m = n \<or> k = 0)"
using assms by (simp add: mult_commute_nat)

lemma Suc_mult_cancel1_nat:
  assumes k: "k \<in> Nat" and m: "m \<in> Nat" and n: "n \<in> Nat"
  shows "(Succ[k] * m = Succ[k] * n) = (m = n)"
using k m n mult_cancel1_nat[of "Succ[k]" m n] by simp


lemma mult_left_commute_nat[algebra_simps]:
  assumes a: "a \<in> Nat" and b: "b \<in> Nat" and c: "c \<in> Nat"
  shows "a * (b * c) = b * (a * c)"
using assms by(simp only: mult_commute_nat mult_assoc_nat)

(* from HOL/OrderedGroups.thy *)
lemmas mult_ac_nat = mult_assoc_nat mult_commute_nat mult_left_commute_nat


subsection \<open> Predecessor \<close>

definition Pred
where "Pred \<equiv> [n \<in> Nat \<mapsto> IF n=0 THEN 0 ELSE CHOOSE x \<in> Nat : n=Succ[x]]"

lemma Pred_0_nat [simp]: "Pred[0] = 0"
by (simp add: Pred_def)

lemma Pred_Succ_nat [simp]: "n \<in> Nat \<Longrightarrow> Pred[Succ[n]] = n"
unfolding Pred_def by (auto intro: bChooseI2)

lemma Succ_Pred_nat [simp]:
  assumes "n \<in> Nat" and "n \<noteq> 0"
  shows "Succ[Pred[n]] = n"
using assms unfolding Pred_def by (cases "n", auto intro: bChooseI2)

lemma Pred_in_nat [intro!, simp]:
  assumes "n \<in> Nat" shows "Pred[n] \<in> Nat"
using assms by (cases "n", auto)

subsection \<open> Difference of natural numbers \<close>

text \<open>
  We define a form of difference @{text "--"} of natural numbers that cuts off
  at $0$, that is @{text "m -- n = 0"} if @{text "m < n"}. This is sometimes
  called ``arithmetic difference''.
\<close>

definition adiffnat
where "adiffnat(m) \<equiv> CHOOSE g \<in> [Nat \<rightarrow> Nat] : g[0] = m \<and> (\<forall>x \<in> Nat : g[Succ[x]] = Pred[g[x]])"

definition adiff        (infixl "--" 65)
where nat_adiff_def: "\<lbrakk>m \<in> Nat; n \<in> Nat\<rbrakk> \<Longrightarrow> (m -- n) \<equiv> adiffnat(m)[n]"

text \<open> Closure \<close>

lemma adiffnatType:
  assumes "m \<in> Nat" shows "adiffnat(m) \<in> [Nat \<rightarrow> Nat]"
using assms unfolding adiffnat_def by (rule bprimrecType_nat, auto)

lemma adiffIsNat [intro!, simp]:
  assumes m: "m \<in> Nat" and n: "n \<in> Nat" shows "m -- n \<in> Nat"
unfolding nat_adiff_def[OF assms] using assms adiffnatType by blast

text \<open> Neutral element and Inductive step \<close>

lemma adiffnat_0:
  assumes "m \<in> Nat" shows "adiffnat(m)[0] = m"
using assms unfolding adiffnat_def by (rule primrec_natE, auto)

lemma adiff_0_nat [simp]:
  assumes "m \<in> Nat" shows "m -- 0 = m"
by (simp add: nat_adiff_def[OF assms] adiffnat_0[OF assms])

lemma adiffnat_Succ:
  assumes m: "m \<in> Nat" and n: "n \<in> Nat"
  shows "adiffnat(m)[Succ[n]] = Pred[adiffnat(m)[n]]"
proof (rule primrec_natE[OF m])
  show "adiffnat(m) = (CHOOSE g \<in> [Nat \<rightarrow> Nat] : g[0] = m \<and> (\<forall>x \<in> Nat : g[Succ[x]] = Pred[g[x]]))"
    unfolding adiffnat_def ..
next
  assume "\<forall>n \<in> Nat : adiffnat(m)[Succ[n]] = Pred[adiffnat(m)[n]]"
  with n show "adiffnat(m)[Succ[n]] = Pred[adiffnat(m)[n]]" by blast
qed (auto)

lemma adiff_Succ_nat:
  assumes "m \<in> Nat" and "n \<in> Nat"
  shows "m -- Succ[n] = Pred[m -- n]"
using assms by (simp add: nat_adiff_def adiffnat_Succ[OF assms])

lemma adiff_0_eq_0_nat [simp]:
  assumes n: "n \<in> Nat"
  shows "0 -- n = 0"
using assms by (induct) (simp_all add: adiff_Succ_nat)

text \<open> Reasoning about @{text "m -- m = 0"}, etc. \<close>

lemma adiff_Succ_Succ_nat [simp]:
  assumes m: "m \<in> Nat" and n: "n \<in> Nat"
  shows "Succ[m] -- Succ[n] = m -- n"
  using n by induct (auto simp add: m adiff_Succ_nat)

lemma adiff_self_eq_0_nat [simp]:
  assumes m: "m \<in> Nat"
  shows  "m -- m = 0"
using m by induct auto

text \<open> Associativity \<close>

lemma adiff_adiff_left_nat:
  assumes i: "i \<in> Nat" and j: "j \<in> Nat" and k: "k \<in> Nat"
  shows "(i -- j) -- k = i -- (j + k)"
using i j by (rule diffInduct) (auto simp: k)

lemma Succ_adiff_adiff_nat [simp]:
  assumes m: "m \<in> Nat" and n: "n \<in> Nat" and k: "k \<in> Nat"
  shows "(Succ[m] -- n) -- Succ[k] = (m -- n) -- k"
using assms by (simp add: adiff_adiff_left_nat)

text \<open> Commutativity \<close>

lemma adiff_commute_nat:
  assumes i: "i \<in> Nat" and j: "j \<in> Nat" and k: "k \<in> Nat"
  shows "i -- j -- k = i -- k -- j"
using assms by (simp add: adiff_adiff_left_nat add_commute_nat)

text \<open> Cancellation rules \<close>

lemma adiff_add_inverse_nat [simp]:
  assumes m: "m \<in> Nat" and n: "n \<in> Nat"
  shows "(n + m) -- n = m"
using n by induct (simp_all add: m)

lemma adiff_add_inverse2_nat [simp]:
  assumes m: "m \<in> Nat" and n: "n \<in> Nat"
  shows "(m + n) -- n = m"
using assms by (simp add: add_commute_nat [of m n])

lemma adiff_cancel_nat [simp]:
  assumes k: "k \<in> Nat" and m: "m \<in> Nat" and n: "n \<in> Nat"
  shows "(k + m) -- (k + n) = m -- n"
using k by induct (simp_all add: m n)

lemma adiff_cancel2_nat [simp]:
  assumes k: "k \<in> Nat" and m: "m \<in> Nat" and n: "n \<in> Nat"
  shows "(m + k) -- (n + k) = m -- n"
using assms by (simp add: add_commute_nat)

lemma adiff_add_0_nat [simp]:
  assumes m: "m \<in> Nat" and n: "n \<in> Nat"
  shows "n -- (n + m) = 0"
using n by induct (simp_all add: m)

text \<open> Difference distributes over multiplication \<close>

lemma adiff_mult_distrib_nat [algebra_simps]:
  assumes k: "k \<in> Nat" and m: "m \<in> Nat" and n: "n \<in> Nat"
  shows "(m -- n) * k = (m * k) -- (n * k)"
using m n by (rule diffInduct) (simp_all add: k)

lemma adiff_mult_distrib2_nat [algebra_simps]:
  assumes k: "k \<in> Nat" and m: "m \<in> Nat" and n: "n \<in> Nat"
  shows "k * (m -- n) = (k * m) -- (k * n)"
using assms by (simp add: adiff_mult_distrib_nat mult_commute_nat [of k])

\<comment> \<open> NOT added as rewrites, since sometimes they are used from right to left \<close>
lemmas nat_distrib =
  add_mult_distrib_right_nat add_mult_distrib_left_nat
  adiff_mult_distrib_nat adiff_mult_distrib2_nat


subsection \<open> Additional arithmetic theorems \<close>

subsubsection \<open> Monotonicity of Addition \<close>

lemma Succ_pred [simp]:
  assumes n: "n \<in> Nat"
  shows "n > 0 \<Longrightarrow> Succ[n -- 1] = n"
using assms by (simp add: adiff_Succ_nat[OF n zeroIsNat] nat_gt0_not0[OF n])

lemma nat_add_left_cancel_leq [simp]:
  assumes k: "k \<in> Nat" and m: "m \<in> Nat" and n: "n \<in> Nat"
  shows "(k + m \<le> k + n) = (m \<le> n)"
using assms by (induct k) simp_all

lemma nat_add_right_cancel_leq [simp]:
  assumes k: "k \<in> Nat" and m: "m \<in> Nat" and n: "n \<in> Nat"
  shows "(m + k \<le> n + k) = (m \<le> n)"
using assms by (induct k) simp_all

lemma nat_add_left_cancel_Succ_leq [simp]:
  assumes k: "k \<in> Nat" and m: "m \<in> Nat" and n: "n \<in> Nat"
  shows "(Succ[k + m] \<le> k + n) = (Succ[m] \<le> n)"
using assms by (induct k) simp_all

(* immediate corollary *)
lemma nat_add_left_cancel_less:
  assumes k: "k \<in> Nat" and m: "m \<in> Nat" and n: "n \<in> Nat"
  shows "(k + m < k + n) = (m < n)"
using assms by simp

lemma nat_add_right_cancel_Succ_less [simp]:
  assumes k: "k \<in> Nat" and m: "m \<in> Nat" and n: "n \<in> Nat"
  shows "(Succ[m + k] \<le> n + k) = (Succ[m] \<le> n)"
using assms by (induct k) simp_all

lemma nat_add_right_cancel_less:
  assumes k: "k \<in> Nat" and m: "m \<in> Nat" and n: "n \<in> Nat"
  shows "(m + k < n + k) = (m < n)"
using assms by simp

lemma less_imp_Succ_add:
  assumes m: "m \<in> Nat" and n: "n \<in> Nat"
  shows "m < n \<Longrightarrow> (\<exists>k \<in> Nat: n = Succ[m + k])" (is "_ \<Longrightarrow> ?P(n)")
using n proof (induct)
  case 0 with m show ?case by simp
next
  fix n
  assume n: "n \<in> Nat" and ih: "m<n \<Longrightarrow> ?P(n)" and suc: "m < Succ[n]"
  from suc m n show "?P(Succ[n])"
  proof (rule nat_less_SuccE)
    assume "m<n"
    then obtain k where "k \<in> Nat" and "n = Succ[m + k]" by (blast dest: ih)
    with m n have "Succ[k] \<in> Nat" and "Succ[n] = Succ[m + Succ[k]]" by auto
    thus ?thesis ..
  next
    assume "m=n"
    with n have "Succ[n] = Succ[m + 0]" by simp
    thus ?thesis by blast
  qed
qed

lemma nat_leq_trans_add_left_false [simp]:
  assumes m: "m \<in> Nat" and n: "n \<in> Nat" and p: "p \<in> Nat"
  shows "\<lbrakk>m + n \<le> p; p \<le> n\<rbrakk> \<Longrightarrow> (m + n < p) = FALSE"
apply (induct n p rule: diffInduct)
using assms by simp_all


subsubsection \<open> (Partially) Ordered Groups \<close>

\<comment> \<open> The two following lemmas are just ``one half'' of
     @{text nat_add_left_cancel_leq} and @{text nat_add_right_cancel_leq}
     proved above." \<close>
lemma add_leq_left_mono:
  assumes a: "a \<in> Nat" and b: "b \<in> Nat" and c: "c \<in> Nat"
  shows "a \<le> b \<Longrightarrow> c + a \<le> c + b"
using assms by simp

lemma add_leq_right_mono:
  assumes a: "a \<in> Nat" and b: "b \<in> Nat" and c: "c \<in> Nat"
  shows "a \<le> b \<Longrightarrow> a + c \<le> b + c"
using assms by simp

text \<open> non-strict, in both arguments \<close>
lemma add_leq_mono:
  assumes a: "a \<in> Nat" and b: "b \<in> Nat" and c: "c \<in> Nat" and d: "d \<in> Nat"
  shows "a \<le> b \<Longrightarrow> c \<le> d \<Longrightarrow> a + c \<le> b + d"
using assms
  add_leq_right_mono[OF a b c]
  add_leq_left_mono[OF c d b]
  nat_leq_trans[of "a + c" "b + c" "b + d"]
by simp

\<comment> \<open> Similar for strict less than. \<close>
lemma add_less_left_mono:
  assumes "a \<in> Nat" and "b \<in> Nat" and "c \<in> Nat"
  shows "a < b \<Longrightarrow> c + a < c + b"
  using assms by (simp add: add_leq_left_mono less_def)

lemma add_less_right_mono:
  assumes a: "a \<in> Nat" and b: "b \<in> Nat" and c: "c \<in> Nat"
  shows "a < b \<Longrightarrow> a + c < b + c"
using assms by (auto simp: add_less_left_mono add_commute_nat)

text \<open> Strict monotonicity in both arguments \<close>
lemma add_less_mono:
  assumes a: "a \<in> Nat" and b: "b \<in> Nat" and c: "c \<in> Nat" and d: "d \<in> Nat"
  shows "a < b \<Longrightarrow> c < d \<Longrightarrow> a + c < b + d"
using assms
  add_less_right_mono[OF a b c]
  add_less_left_mono[OF c d b]
  nat_less_trans[of "a + c" "b + c" "b + d"]
by simp

lemma add_less_leq_mono:
  assumes a: "a \<in> Nat" and b: "b \<in> Nat" and c: "c \<in> Nat" and d: "d \<in> Nat"
  shows "a < b \<Longrightarrow> c \<le> d \<Longrightarrow> a + c < b + d"
using assms
  add_less_right_mono[OF a b c]
  add_leq_left_mono[OF c d b]
  nat_less_leq_trans[of "a + c" "b + c" "b + d"]
by blast

lemma add_leq_less_mono:
  assumes a: "a \<in> Nat" and b: "b \<in> Nat" and c: "c \<in> Nat" and d: "d \<in> Nat"
  shows "a \<le> b \<Longrightarrow> c < d \<Longrightarrow> a + c < b + d"
using assms
  add_leq_right_mono[OF a b c]
  add_less_left_mono[OF c d b]
  nat_leq_less_trans[of "a + c" "b + c" "b + d"]
by blast

lemma leq_add1 [simp]:
  assumes m: "m \<in> Nat" and n: "n \<in> Nat"
  shows "n \<le> n + m"
using assms add_leq_left_mono[of 0 m n] by simp

lemma leq_add2 [simp]:
  assumes "m \<in> Nat" and "n \<in> Nat"
  shows "n \<le> m + n"
using assms add_leq_right_mono [of 0 m n] by simp

lemma trans_leq_add1 [elim]:
  assumes "n \<le> m" and "n \<in> Nat" and "m \<in> Nat" and "k \<in> Nat"
  shows "n \<le> m+k"
using assms by (simp add: nat_leq_trans)

lemma trans_leq_add2 [elim]:
  assumes "n \<le> m" and "n \<in> Nat" and "m \<in> Nat" and "k \<in> Nat"
  shows "n \<le> k+m"
using assms by (simp add: nat_leq_trans)

lemma add_leqD1 [elim]:
  assumes "n+k \<le> m" and "n \<in> Nat" and "m \<in> Nat" and "k \<in> Nat"
  shows "n \<le> m"
using assms by (simp add: nat_leq_trans[of "n" "n+k" "m"])

lemma add_leqD2 [elim]:
  assumes "k+n \<le> m" and "n \<in> Nat" and "m \<in> Nat" and "k \<in> Nat"
  shows "n \<le> m"
using assms by (simp add: nat_leq_trans[of "n" "k+n" "m"])

lemma add_Succ_leqD1 [elim]:
  assumes "Succ[n+k] \<le> m" and "n \<in> Nat" and "m \<in> Nat" and "k \<in> Nat"
  shows "Succ[n] \<le> m"
using assms by (simp add: nat_leq_trans[of "Succ[n]" "Succ[n+k]" "m"])

lemma add_Succ_leqD2 [elim]:
  assumes "Succ[k+n] \<le> m" and "n \<in> Nat" and "m \<in> Nat" and "k \<in> Nat"
  shows "Succ[n] \<le> m"
using assms by (simp add: nat_leq_trans[of "Succ[n]" "Succ[k+n]" "m"])

lemma less_add_Succ1:
  assumes "i \<in> Nat" and "m \<in> Nat"
  shows "i < Succ[i + m]"
using assms by simp

lemma less_add_Succ2:
  assumes "i \<in> Nat" and "m \<in> Nat"
  shows "i < Succ[m + i]"
using assms by simp

lemma less_iff_Succ_add:
  assumes "m \<in> Nat" and "n \<in> Nat"
  shows "(m < n) = (\<exists>k \<in> Nat: n = Succ[m + k])"
using assms by (auto intro!: less_imp_Succ_add)

lemma trans_less_add1:
  assumes "i < j" and "i \<in> Nat" and "j \<in> Nat" and "m \<in> Nat"
  shows "i < j + m"
using assms by auto

lemma trans_less_add2:
  assumes "i < j" and "i \<in> Nat" and "j \<in> Nat" and "m \<in> Nat"
  shows "i < m + j"
using assms by auto

lemma add_lessD1:
  assumes "i+j < k" and "i \<in> Nat" and "j \<in> Nat" and "k \<in> Nat"
  shows "i < k"
using assms by auto

lemma add_lessD2:
  assumes "j+i < k" and "i \<in> Nat" and "j \<in> Nat" and "k \<in> Nat"
  shows "i < k"
using assms by auto

lemma not_Succ_add_le1:
  assumes i: "i \<in> Nat" and j: "j \<in> Nat"
  shows "(Succ[i + j] \<le> i) = FALSE"
using assms by simp

lemma not_Succ_add_le2:
  assumes i: "i \<in> Nat" and j: "j \<in> Nat"
  shows "(Succ[j + i] \<le> i) = FALSE"
using assms by simp

lemma not_add_less1:
  assumes i: "i \<in> Nat" and j: "j \<in> Nat"
  shows "(i + j < i) = FALSE"
using assms by simp

lemma not_add_less2:
  assumes "i \<in> Nat" and "j \<in> Nat"
  shows "(j + i < i) = FALSE"
using assms by simp

lemma add_leqE:
  assumes "m+k \<le> n" and "k \<in> Nat" and "m \<in> Nat" and "n \<in> Nat"
  shows "(m \<le> n \<Longrightarrow> k \<le> n \<Longrightarrow> R) \<Longrightarrow> R"
using assms by (blast dest: add_leqD1 add_leqD2)

lemma leq_add_self1 [simp]:
  assumes "m \<in> Nat" and "n \<in> Nat"
  shows "(m+n \<le> m) = (n=0)"
proof -
  {
    assume "m+n \<le> m"
    with assms have "m+n = m" by (intro nat_leq_antisym) simp_all
  }
  with assms show ?thesis by auto
qed

lemma leq_add_self2 [simp]:
  assumes "m \<in> Nat" and "n \<in> Nat"
  shows "(n+m \<le> m) = (n=0)"
proof -
  {
    assume "n+m \<le> m"
    with assms have "n+m = m" by (intro nat_leq_antisym) simp_all
  }
  with assms show ?thesis by auto
qed

lemma add_gt_0:
  assumes "m \<in> Nat" and "n \<in> Nat"
  shows "(m + n > 0) = (m > 0 \<or> n > 0)"
proof -
  from assms have "m + n \<in> Nat" by simp
  hence "(m + n > 0) = (m + n \<noteq> 0)" by (rule nat_gt0_not0)
  also from assms have "\<dots> = (m \<noteq> 0 \<or> n \<noteq> 0)" by simp
  finally show ?thesis using assms by (simp only: nat_gt0_not0)
qed

(* The above lemma follows from the following simplification rule. *)
lemma add_ge_1 [simp]:
  assumes "m \<in> Nat" and "n \<in> Nat"
  shows "(m + n \<ge> 1) = (m \<ge> 1 \<or> n \<ge> 1)"
  using assms by (auto simp add: add_gt_0)


subsubsection \<open> More results about arithmetic difference \<close>

text \<open> Addition is the inverse of subtraction:
  if @{term "n \<le> m"} then @{term "n + (m -- n) = m"}. \<close>
lemma add_adiff_inverse:
  assumes "m \<in> Nat" and "n \<in> Nat"
  shows "\<not>(m < n) \<Longrightarrow> n + (m -- n) = m"
apply (induct m n rule: diffInduct)
using assms by simp_all

lemma le_add_adiff_inverse [simp]:
  assumes "m \<in> Nat" and "n \<in> Nat"
  shows "n \<le> m \<Longrightarrow> n + (m -- n) = m"
using assms by (simp add: add_adiff_inverse nat_not_order_simps)

lemma le_add_adiff_inverse2 [simp]:
  assumes "m \<in> Nat" and "n \<in> Nat"
  shows "n \<le> m \<Longrightarrow> (m -- n) + n = m"
using assms by (simp add: add_commute_nat)

lemma Succ_adiff_leq:
  assumes "m \<in> Nat" and "n \<in> Nat"
  shows "n \<le> m \<Longrightarrow> Succ[m] -- n = Succ[m -- n]"
apply (induct m n rule: diffInduct)
using assms by simp_all

lemma adiff_less_Succ:
  assumes m: "m \<in> Nat" and n: "n \<in> Nat"
  shows "m -- n < Succ[m]"
apply (induct m n rule: diffInduct)
using assms by (auto simp: nat_less_Succ)

lemma adiff_leq_self [simp]:
  assumes m: "m \<in> Nat" and n: "n \<in> Nat"
  shows "m -- n \<le> m"
apply (induct m n rule: diffInduct)
using assms by auto

lemma leq_iff_add:
  assumes m: "m \<in> Nat" and n: "n \<in> Nat"
  shows "m \<le> n = (\<exists>k \<in> Nat: n = m + k)"  (is "?lhs = ?rhs")
proof -
  have "?lhs \<Rightarrow> ?rhs"
  proof
    assume mn: "m \<le> n"
    with m n have "n = m + (n -- m)" by simp
    with m n show "?rhs" by blast
  qed
  moreover
  from assms have "?rhs \<Rightarrow> ?lhs" by auto
  ultimately show ?thesis by blast
qed

lemma less_imp_adiff_less:
  assumes jk: "j < k" and j: "j \<in> Nat" and k: "k \<in> Nat" and n: "n \<in> Nat"
  shows "j -- n < k"
proof -
  from j n have "j -- n \<in> Nat" by simp
  moreover
  from j n have s1_2: "j -- n \<le> j" by simp
  ultimately show ?thesis using j k jk nat_leq_less_trans by auto
qed

lemma adiff_Succ_less (*[simp]*):
  assumes i: "i \<in> Nat" and n: "n \<in> Nat"
  shows "0 < n \<Longrightarrow> n -- Succ[i] < n"
using n by cases (auto simp: i)

lemma adiff_add_assoc:
  assumes "k \<le> j" and "i \<in> Nat" and "j \<in> Nat" and "k \<in> Nat"
  shows "(i + j) -- k = i + (j -- k)"
using assms by (induct j k rule: diffInduct, simp+)

lemma adiff_add_assoc2:
  assumes "k \<le> j" and "i \<in> Nat" and "j \<in> Nat" and "k \<in> Nat"
  shows "(j + i) -- k = (j -- k) + i"
using assms by (simp add: add_commute_nat adiff_add_assoc)

lemma adiff_add_assoc3:
  assumes "n \<le> p" and "p \<le> m+n" and "m \<in> Nat" and "n \<in> Nat" and "p \<in> Nat"
  shows "m -- (p -- n) = m + n -- p"
using assms by (induct p n rule: diffInduct, simp+)

lemma adiff_add_assoc4:
  assumes 1: "n \<le> m" and 2: "m -- n \<le> p" and 3: "m \<le> p"
      and m: "m \<in> Nat" and n: "n \<in> Nat" and p: "p \<in> Nat"
  shows "p -- (m -- n) = (p -- m) + n"
using assms
  adiff_add_assoc2[OF _ n p m, symmetric]
  adiff_add_assoc3[OF _ _ p n m] apply simp
using trans_leq_add1[OF _ m p n] by simp

lemma le_imp_adiff_is_add:
  assumes "i \<le> j" and "i \<in> Nat" and "j \<in> Nat" and "k \<in> Nat"
  shows "(j -- i = k) = (j = k + i)"
using assms by auto

lemma adiff_is_0_eq [simp]:
  assumes m: "m \<in> Nat" and n: "n \<in> Nat"
  shows "(m -- n = 0) = (m \<le> n)"
by (induct m n rule: diffInduct, simp_all add: assms)

lemma adiff_is_0_eq' (*[simp]*):
  assumes "m \<le> n" and "m \<in> Nat" and "n \<in> Nat"
  shows "m -- n = 0"
using assms by simp

lemma one_leq_adiff [simp]:
  assumes "m \<in> Nat" and "n \<in> Nat"
  shows "(1 \<le> n -- m) = (Succ[m] \<le> n)"
by (induct m n rule: diffInduct, simp_all add: assms)

lemma zero_less_adiff:
  assumes "m \<in> Nat" and "n \<in> Nat"
  shows "(0 < n -- m) = (m < n)"
using assms by simp

lemma less_imp_add_positive:
  assumes "i < j" and "i \<in> Nat" and "j \<in> Nat"
  shows "\<exists>k \<in> Nat: 0 < k \<and> i + k = j"
proof -
  thm leq_iff_add
  from assms obtain k where k: "k \<in> Nat" "j = Succ[i]+k"
    by (auto simp: leq_iff_add)
  with assms show ?thesis by force
qed

lemma leq_adiff_right_add_left:
  assumes "k \<le> n" and "m \<in> Nat" and "n \<in> Nat" and "k \<in> Nat"
  shows "m \<le> n -- k = (m + k \<le> n)"
using assms by (induct n k rule: diffInduct, simp+)

lemma leq_adiff_left_add_right_equiv:
  assumes "k \<le> n" and "m \<in> Nat" and "n \<in> Nat" and "k \<in> Nat"
  shows "(n -- k \<le> m) = (n \<le> m + k)"
using assms by (induct n k rule: diffInduct, simp+)

lemma leq_adiff_left_add_right:
  assumes 1: "n -- p \<le> m" and m: "m \<in> Nat" and n: "n \<in> Nat" and p: "p \<in> Nat"
  shows "n \<le> m + p"
using assms by (induct n p rule: diffInduct, simp+)

lemma leq_adiff_trans:
  assumes "p \<le> m" and m: "m \<in> Nat" and n: "n \<in> Nat" and p: "p \<in> Nat"
  shows "p -- n \<le> m"
apply(rule nat_leq_trans[of "p -- n" p m])
using assms adiff_leq_self[OF p n] by simp_all

lemma leq_adiff_right [simp]:
  assumes "n \<le> m" and "m \<in> Nat" and "n \<in> Nat"
  shows "(m \<le> m -- n) = (n = 0)"
  using assms by (simp add: leq_adiff_right_add_left)


subsubsection \<open> Monotonicity of Multiplication \<close>

(* from HOL/Ring_and_Field.thy *)

lemma mult_leq_left_mono:
  assumes 1:"a \<le> b" and a: "a \<in> Nat" and b: "b \<in> Nat" and c: "c \<in> Nat"
  shows "c * a \<le> c * b"
using c by induct (simp_all add: add_leq_mono 1 a b)

lemma mult_leq_right_mono:
  assumes 1:"a \<le> b" and a: "a \<in> Nat" and b: "b \<in> Nat" and c: "c \<in> Nat"
  shows "a * c \<le> b * c"
using c by induct (simp_all add: add_leq_mono add_commute_nat 1 a b)

text \<open> @{text "\<le>"} monotonicity, BOTH arguments \<close>

lemma mult_leq_mono:
  assumes 1: "i \<le> j" "k \<le> l"
  and i: "i \<in> Nat" and j: "j \<in> Nat" and k: "k \<in> Nat" and l: "l \<in> Nat"
  shows "i * k \<le> j * l"
using assms
  mult_leq_right_mono[OF _ i j k]
  mult_leq_left_mono[OF _ k l j]
  nat_leq_trans[of "i * k" "j * k" "j * l"]
  by simp

lemma self_leq_mult_left:
  assumes a: "a \<in> Nat" and b: "b \<in> Nat" and 1: "1 \<le> b"
  shows "a \<le> a * b"
proof -
  have "1 \<in> Nat" by simp
  from 1 this b a have "a * 1 \<le> a * b" by (rule mult_leq_left_mono)
  with a b show ?thesis by simp
qed

lemma self_leq_mult_right:
  assumes a: "a \<in> Nat" and b: "b \<in> Nat" and 1: "1 \<le> b"
  shows "a \<le> b * a"
using assms by (simp add: self_leq_mult_left mult_commute_nat)

text \<open> Similar lemmas for @{text "<"} \<close>

lemma mult_Succ_leq_right_mono1:
  assumes ab: "Succ[a] \<le> b" and a: "a \<in> Nat" and b: "b \<in> Nat" and c: "c \<in> Nat"
  shows "Succ[a * Succ[c]] \<le> b * Succ[c]"
using c proof induct
  case 0
  with assms show ?case by simp
next
  fix n
  assume n: "n \<in> Nat" and ih: "Succ[a * Succ[n]] \<le> b * Succ[n]"
  from ab a b have 1: "a \<le> b" 
    by (simp add: nat_leq_trans[of "a" "Succ[a]" "b"])
  from a n have "Succ[a * Succ[Succ[n]]] = Succ[a * Succ[n]] + a"
    by simp
  also from a b n ih have "\<dots> \<le> b* Succ[n] + a"
    by simp
  also from a b n 1 have "\<dots> \<le> b * Succ[n] + b"
    by simp
  finally show "Succ[a * Succ[Succ[n]]] \<le> b * Succ[Succ[n]]"
    using b n by simp
qed

lemma mult_Succ_leq_right_mono2:
  assumes ab: "Succ[a] \<le> b"  and a: "a \<in> Nat" and b: "b \<in> Nat" and c: "c \<in> Nat" and 1: "1 \<le> c"
  shows "Succ[a * c] \<le> b * c"
proof -
  from c 1 obtain k where k: "k \<in> Nat" "c = Succ[k]"
    by (blast dest: nat_ge1_implies_Succ)
  with ab a b show ?thesis by (auto dest: mult_Succ_leq_right_mono1[of a b k])
qed

lemma mult_less_right_mono:
  assumes "a < b" and "0 < c" and "a \<in> Nat" and "b \<in> Nat" and "c \<in> Nat"
  shows "a * c < b * c"
using assms by (simp add: mult_Succ_leq_right_mono2)

lemma mult_Succ_leq_left_mono1:
  assumes ab: "Succ[a] \<le> b" and a: "a \<in> Nat" and b: "b \<in> Nat" and c: "c \<in> Nat"
  shows "Succ[Succ[c] * a] \<le> Succ[c] * b"
proof -
  have "Succ[Succ[c] * a] = Succ[a * Succ[c]]"
    using a c by (simp add: mult_commute_nat)
  also have "\<dots> \<le> b * Succ[c]"
    using assms by (rule mult_Succ_leq_right_mono1)
  also have "\<dots> = Succ[c] * b"
    using b c by (simp add: mult_commute_nat)
  finally show ?thesis .
qed

lemma mult_Succ_leq_left_mono2:
  assumes ab: "Succ[a] \<le> b"  and a: "a \<in> Nat" and b: "b \<in> Nat" and c: "c \<in> Nat" and 1: "1 \<le> c"
  shows "Succ[c * a] \<le> c * b"
proof -
  from c 1 obtain k where k: "k \<in> Nat" "c = Succ[k]"
    by (blast dest: nat_ge1_implies_Succ)
  with ab a b show ?thesis by (auto dest: mult_Succ_leq_left_mono1[of a b k])
qed

lemma mult_less_left_mono:
  assumes "a < b" and "0 < c" and "a \<in> Nat" and "b \<in> Nat" and "c \<in> Nat"
  shows "c * a < c * b"
using assms by (simp add: mult_Succ_leq_left_mono2)

lemma one_leq_mult_iff[simp]:
  assumes m: "m \<in> Nat" and n: "n \<in> Nat"
  shows "(1 \<le> m * n) = (1 \<le> m \<and> 1 \<le> n)"
using assms nat_gt0_not0 by simp

lemma nat_0_less_mult_iff:
  assumes i: "i \<in> Nat" and j: "j \<in> Nat"
  shows "(0 < i * j) = (0 < i \<and> 0 < j)"
using assms by simp

lemma mult_Succ_leq_cancel_left [simp]:
  assumes m: "m \<in> Nat" and n: "n \<in> Nat" and k: "k \<in> Nat"
  shows "(Succ[k * m] \<le> k * n) = (1 \<le> k \<and> Succ[m] \<le> n)"
proof (auto intro: mult_Succ_leq_left_mono2[OF _ m n k _])
  assume "Succ[k * m] \<le> k * n"
  from k m n this show "1 \<le> k" by (cases k) simp_all
next
  assume 1: "Succ[k * m] \<le> k * n"
  show "Succ[m] \<le> n"
  proof (rule contradiction)
    assume "\<not>(Succ[m] \<le> n)"
    with m n k have "k*n \<le> k*m" by (simp add: nat_not_order_simps mult_leq_left_mono)
    with m n k have "\<not>(Succ[k*m] \<le> k*n)" by (simp add: nat_not_order_simps)
    with 1 show "FALSE" by simp
  qed
qed

lemma mult_less_cancel_left:
  assumes m: "m \<in> Nat" and n: "n \<in> Nat" and k: "k \<in> Nat"
  shows "(k * m < k * n) = (0 < k \<and> m < n)"
using assms by simp

lemma mult_Succ_leq_cancel_right [simp]:
  assumes m: "m \<in> Nat" and n: "n \<in> Nat" and k: "k \<in> Nat"
  shows "(Succ[m * k] \<le> n * k) = (1 \<le> k \<and> Succ[m] \<le> n)"
proof (auto intro: mult_Succ_leq_right_mono2[OF _ m n k _])
  assume "Succ[m * k] \<le> n * k"
  from k m n this show "1 \<le> k" by (cases k) simp_all
next
  assume 1: "Succ[m * k] \<le> n * k"
  show "Succ[m] \<le> n"
  proof (rule contradiction)
    assume "\<not>(Succ[m] \<le> n)"
    with m n k have "n*k \<le> m*k" by (simp add: nat_not_order_simps mult_leq_right_mono)
    with m n k have "\<not>(Succ[m*k] \<le> n*k)" by (simp add: nat_not_order_simps)
    with 1 show "FALSE" by simp
  qed
qed

lemma mult_less_cancel_right:
  assumes m: "m \<in> Nat" and n: "n \<in> Nat" and k: "k \<in> Nat"
  shows "(m * k < n * k) = (0 < k \<and> m < n)"
using assms by simp

lemma mult_Succ_leq_self_left [dest]:
  assumes nk: "Succ[n*k] \<le> n" and n: "n \<in> Nat" and k: "k \<in> Nat"
  shows "k = 0"
proof (rule contradiction)
  assume "k \<noteq> 0"
  with k nat_neq0_conv have "1 \<le> k" by simp
  with n k have "n \<le> n * k" by (rule self_leq_mult_left)
  with n k have "\<not>(Succ[n*k] \<le> n)" by (simp add: nat_not_order_simps)
  from this nk show "FALSE" ..
qed

lemma mult_less_self_left:
  assumes "n * k < n" and "n \<in> Nat" and "k \<in> Nat"
  shows "k=0"
using assms by auto

lemma mult_Succ_leq_self_right [dest]:
  assumes less: "Succ[k*n] \<le> n" and n: "n \<in> Nat" and k: "k \<in> Nat"
  shows "k=0"
using assms by (auto simp: mult_commute_nat[OF k n])

lemma mult_less_self_right:
  assumes less: "k*n < n" and n: "n \<in> Nat" and k: "k \<in> Nat"
  shows "k=0"
using assms by auto

lemma mult_leq_cancel_left [simp]:
  assumes m: "m \<in> Nat" and n: "n \<in> Nat" and k: "k \<in> Nat"
  shows "(k * m \<le> k * n) = (k = 0 \<or> m \<le> n)"
proof -
  {
    assume 1: "k*m \<le> k*n" and 2: "k \<noteq> 0" and 3: "\<not>(m \<le> n)"
    from k 2 nat_gt0_not0 have "k > 0" by simp
    with 3 k m n have "\<not>(k * m \<le> k * n)" by (simp add: nat_not_order_simps)
    from this 1 have "FALSE" ..
  }
  moreover have "k=0 \<Longrightarrow> k*m \<le> k*n"
    using assms by simp
  moreover have "m \<le> n \<Longrightarrow> k*m \<le> k*n"
    using assms by (simp add: mult_leq_left_mono)
  ultimately show ?thesis by blast
qed

lemma mult_leq_cancel_right [simp]:
  assumes m: "m \<in> Nat" and n: "n \<in> Nat" and k: "k \<in> Nat"
  shows "(m * k \<le> n * k) = (k = 0 \<or> m \<le> n)"
using assms by (simp add: mult_commute_nat)

lemma Suc_mult_less_cancel1:
  assumes "m \<in> Nat" and "n \<in> Nat" and "k \<in> Nat"
  shows "(Succ[k] * m < Succ[k] * n) = (m < n)"
using assms mult_less_cancel_left[of "m" "n" "Succ[k]"]
      nat_zero_less_Succ[of "k"] by auto

lemma Suc_mult_leq_cancel1:
  assumes "m \<in> Nat" and "n \<in> Nat" and "k \<in> Nat"
  shows "(Succ[k] * m \<le> Succ[k] * n) = (m \<le> n)"
using assms by (simp del: mult_Succ_left_nat)

lemma nat_leq_square:
  assumes m: "m \<in> Nat"
  shows "m \<le> m * m"
using m by (cases, auto)

lemma nat_leq_cube:
  assumes m: "m \<in> Nat"
  shows "m \<le> m * (m * m)"
using m by (cases, auto)

text \<open> Lemma for @{text gcd} \<close>
lemma mult_eq_self_implies_10:
  assumes m: "m \<in> Nat" and n: "n \<in> Nat"
  shows "(m * n = m) = (n = 1 \<or> m = 0)" (is "?lhs = ?rhs")
proof -
  from assms have "(m*n = m) = (m*n = m*1)" by simp
  also have "\<dots> = ?rhs" by (rule mult_cancel1_nat[OF m n oneIsNat])
  finally show ?thesis .
qed

end
