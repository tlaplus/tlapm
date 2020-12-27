(*  Title:      TLA+/NatArith.thy
    Author:     Hernan Vanzetto, LORIA
    Copyright (C) 2009-2011  INRIA and Microsoft Corporation
    License:    BSD
    Version:    Isabelle2020
    Time-stamp: <2011-10-11 17:39:37 merz>
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

lemma add_eq_self_zero_nat [simp]:
  assumes m: "m \<in> Nat" and n: "n \<in> Nat"
  shows "(m + n = m) = (n = 0)"
using n apply (rule natCases)
  using m apply simp
  using m apply induct apply auto
done


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

lemma mult_0_nat [simp]:  (* -- "neutral element" *)
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
using n apply induct by (simp_all add: adiff_Succ_nat)

text \<open> Reasoning about @{text "m -- m = 0"}, etc. \<close>

lemma adiff_Succ_Succ_nat [simp]:
  assumes m: "m \<in> Nat" and n: "n \<in> Nat"
  shows "Succ[m] -- Succ[n] = m -- n"
using n apply induct
using assms by (auto simp add: adiff_Succ_nat)

lemma adiff_self_eq_0_nat [simp]:
  assumes m: "m \<in> Nat"
  shows  "m -- m = 0"
using m apply induct by auto

text \<open> Associativity \<close>

lemma adiff_adiff_left_nat:
  assumes i: "i \<in> Nat" and j: "j \<in> Nat" and k: "k \<in> Nat"
  shows "(i -- j) -- k = i -- (j + k)"
using i j apply (rule diffInduct)
using k by auto

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
using n apply induct
using assms by auto

lemma adiff_add_inverse2_nat [simp]:
  assumes m: "m \<in> Nat" and n: "n \<in> Nat"
  shows "(m + n) -- n = m"
using assms by (simp add: add_commute_nat [of m n])

lemma adiff_cancel_nat [simp]:
  assumes k: "k \<in> Nat" and m: "m \<in> Nat" and n: "n \<in> Nat"
  shows "(k + m) -- (k + n) = m -- n"
using k apply induct
using assms by simp_all

lemma adiff_cancel2_nat [simp]:
  assumes k: "k \<in> Nat" and m: "m \<in> Nat" and n: "n \<in> Nat"
  shows "(m + k) -- (n + k) = m -- n"
using assms by (simp add: add_commute_nat)

lemma adiff_add_0_nat [simp]:
  assumes m: "m \<in> Nat" and n: "n \<in> Nat"
  shows "n -- (n + m) = 0"
using n apply induct
using assms by simp_all

text \<open> Difference distributes over multiplication \<close>

lemma adiff_mult_distrib_nat [algebra_simps]:
  assumes k: "k \<in> Nat" and m: "m \<in> Nat" and n: "n \<in> Nat"
  shows "(m -- n) * k = (m * k) -- (n * k)"
using m n apply(rule diffInduct)
using k by simp_all

lemma adiff_mult_distrib2_nat [algebra_simps]:
  assumes k: "k \<in> Nat" and m: "m \<in> Nat" and n: "n \<in> Nat"
  shows "k * (m -- n) = (k * m) -- (k * n)"
using assms by (simp add: adiff_mult_distrib_nat mult_commute_nat [of k])

(* -- "NOT added as rewrites, since sometimes they are used from right-to-left" *)
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

lemma nat_add_left_cancel_less [simp]:
  assumes k: "k \<in> Nat" and m: "m \<in> Nat" and n: "n \<in> Nat"
  shows "(k + m < k + n) = (m < n)"
using k apply induct
using assms by simp_all

lemma nat_add_right_cancel_less [simp]:
  assumes k: "k \<in> Nat" and m: "m \<in> Nat" and n: "n \<in> Nat"
  shows "(m + k < n + k) = (m < n)"
using k apply induct
using assms by simp_all

lemma nat_add_right_cancel_leq [simp]:
  assumes k: "k \<in> Nat" and m: "m \<in> Nat" and n: "n \<in> Nat"
  shows "(m + k \<le> n + k) = (m \<le> n)"
using k apply induct
using assms by simp_all

lemma add_gr_0 [simp]:
    assumes ndom: "n \<in> Nat" and mdom: "m \<in> Nat"
    shows "(m + n > 0) = (m > 0 \<or> n > 0)"
    proof -
    have s1_1: "m + n > 0 ==> m > 0 \<or> n > 0"
        proof -
        assume s1_1_asm: "m + n > 0"
        have s2_1: "m \<noteq> 0 \<or> n \<noteq> 0"
            proof -
            have s3_1: "m = 0 \<and> n = 0 ==> FALSE"
                proof -
                assume s3_1_asm: "m = 0 \<and> n = 0"
                have s4_1: "m + n = 0"
                    using s3_1_asm ndom mdom add_is_0_nat by auto
                have s4_2: "m + n \<noteq> 0"
                    unfolding less_def using s1_1_asm by auto
                show "FALSE"
                    using s4_1 s4_2 by auto
                qed
            show ?thesis
                using s3_1 by auto
            qed
        show "m > 0 \<or> n > 0"
            using s2_1 ndom mdom nat_gt0_not0 by auto
        qed
    have s1_2: "m > 0 \<or> n > 0 ==> m + n > 0"
        proof -
        assume s1_2_asm: "m > 0 \<or> n > 0"
        have s2_1: "m > 0 ==> m + n > 0"
            proof -
            assume s2_1_asm: "m > 0"
            have s3_1: "m + n > 0 + n"
                proof -
                have s4_1: "0 < m"
                    using s2_1_asm by auto
                have s4_2: "(0 + n < m + n) = (0 < m)"
                    using ndom mdom zeroIsNat nat_add_right_cancel_less
                        by blast
                have s4_3: "0 + n < m + n"
                    using s4_1 s4_2 by auto
                show ?thesis
                    using s4_3 by auto
                qed
            have s3_2: "0 + n = n"
                using ndom add_0_nat add_commute_nat zeroIsNat
                    by auto
            have s3_3: "n >= 0"
                using ndom nat_zero_leq by auto
            have s3_4: "m + n >= 0 + n"
                using s3_1 by (auto simp: less_def)
            have s3_5: "m + n >= n"
                using s3_4 s3_2 by auto
            have s3_6: "m + n >= 0"
                using s3_5 s3_3 nat_leq_trans
                    zeroIsNat ndom mdom addIsNat by auto
            have s3_7: "m + n = 0 ==> FALSE"
                proof -
                assume s3_7_asm: "m + n = 0"
                have s4_1: "m = 0 \<and> n = 0"
                    using s3_7_asm mdom ndom add_is_0_nat
                        by auto
                show "FALSE"
                    using s4_1 s2_1_asm by (auto simp: less_def)
                qed
            show "m + n > 0"
                unfolding less_def
                using s3_6 s3_7 by auto
            qed
        have s2_2: "n > 0 ==> m + n > 0"
            proof -
            assume s2_2_asm: "n > 0"
            have s3_1: "m + n > m + 0"
                proof -
                have s4_1: "0 < n"
                    using s2_2_asm by auto
                have s4_2: "(m + 0 < m + n) = (0 < n)"
                    using ndom mdom zeroIsNat nat_add_left_cancel_less
                        by blast
                have s4_3: "m + 0 < m + n"
                    using s4_1 s4_2 by auto
                show ?thesis
                    using s4_3 by auto
                qed
            have s3_2: "m + 0 = m"
                using mdom add_0_nat by auto
            have s3_3: "m >= 0"
                using mdom nat_zero_leq by auto
            have s3_4: "m + n >= m + 0"
                using s3_1 by (auto simp: less_def)
            have s3_5: "m + n >= m"
                using s3_4 s3_2 by auto
            have s3_6: "m + n >= 0"
                using s3_5 s3_3 nat_leq_trans
                    zeroIsNat ndom mdom addIsNat by auto
            have s3_7: "m + n = 0 ==> FALSE"
                proof -
                assume s3_7_asm: "m + n = 0"
                have s4_1: "m = 0 \<and> n = 0"
                    using s3_7_asm mdom ndom add_is_0_nat
                        by auto
                show "FALSE"
                    using s4_1 s2_2_asm by (auto simp: less_def)
                qed
            show "m + n > 0"
                unfolding less_def
                using s3_6 s3_7 by auto
            qed
        show "m + n > 0"
            using s1_2_asm s2_1 s2_2 by auto
        qed
    show ?thesis
        using s1_1 s1_2 by auto
    qed

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

(* -- "The two following lemmas are just ``one half'' of
      @{text nat_add_left_cancel_leq} and @{text nat_add_right_cancel_leq}
      proved above." *)
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

(* -- "Similar for strict less than." *)
lemma add_less_left_mono:
  assumes a: "a \<in> Nat" and b: "b \<in> Nat" and c: "c \<in> Nat"
  shows "a < b \<Longrightarrow> c + a < c + b"
    proof -
    have s1_1: "a <= b ==> c + a <= c + b"
        using a b c add_leq_left_mono by auto
    have s1_2: "a \<noteq> b ==> (c + a) \<noteq> (c + b)"
        using a b c add_left_cancel_nat by auto
    have s1_3: "a < b ==> c + a < c + b"
        proof -
        assume s1_3_asm: "a < b"
        have s2_1: "a <= b"
            using s1_3_asm by (auto simp: less_def)
        have s2_2: "a \<noteq> b"
            using s1_3_asm by (auto simp: less_def)
        have s2_3: "c + a <= c + b"
            using s1_1 s2_1 by auto
        have s2_4: "(c + a) \<noteq> (c + b)"
            using s1_2 s2_2 by auto
        show "c + a < c + b"
            using s2_3 s2_4 by (auto simp: less_def)
        qed
    show "a < b \<Longrightarrow> c + a < c + b"
        using a b c s1_3 by auto
    qed
(*
using assms add_leq_left_mono[OF "a" "b" "c"] add_left_cancel_nat[OF "c" "b" "a"]
    by (auto simp: nat_less_Succ_iff_leq nat_gt0_not0)
*)

lemma add_less_right_mono:
  assumes a: "a \<in> Nat" and b: "b \<in> Nat" and c: "c \<in> Nat"
  shows "a < b \<Longrightarrow> a + c < b + c"
using assms add_less_left_mono add_commute_nat by auto

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

lemma trans_leq_add1:
  assumes "i \<le> j" and "i \<in> Nat" and "j \<in> Nat" and "m \<in> Nat"
  shows "i \<le> j + m"
using assms by (auto elim: nat_leq_trans)

lemma trans_leq_add2:
  assumes "i \<le> j" and "i \<in> Nat" and "j \<in> Nat" and "m \<in> Nat"
  shows "i \<le> m + j"
using assms by (auto elim: nat_leq_trans)

lemma trans_less_add1:
  assumes ij: "i < j" and idom: "i \<in> Nat" and
    jdom: "j \<in> Nat" and mdom: "m \<in> Nat"
  shows "i < j + m"
    proof -
    have s1_1: "i <= i + m"
        proof -
        have s2_1: "0 <= m"
            using mdom nat_zero_leq by auto
        have s2_2: "i + 0 <= i + m"
            using idom zeroIsNat mdom s2_1 nat_add_left_cancel_leq by auto
        have s2_3: "i + 0 = i"
            using idom add_0_nat by auto
        show ?thesis
            using s2_2 s2_3 by auto
        qed
    have s1_2: "i + m < j + m"
        using ij idom jdom mdom add_less_right_mono by auto
    have s1_3: "i + m \<in> Nat"
        using idom mdom addIsNat by auto
    have s1_4: "j + m \<in> Nat"
        using jdom mdom addIsNat by auto
    show ?thesis
        using s1_1 s1_2 idom s1_3 s1_4 nat_leq_less_trans
            by auto
    qed

lemma trans_less_add2:
  assumes "i < j" and "i \<in> Nat" and "j \<in> Nat" and "m \<in> Nat"
  shows "i < m + j"
using assms trans_less_add1 add_commute_nat by auto

lemma add_lessD1:
  assumes "i+j < k" and "i \<in> Nat" and "j \<in> Nat" and "k \<in> Nat"
  shows "i < k"
using assms by (intro nat_leq_less_trans[of "i" "i+j" "k"], simp+)

lemma not_add_less1 [simp]:
  assumes i: "i \<in> Nat" and j: "j \<in> Nat"
  shows "(i + j < i) = FALSE"
by (auto dest: add_lessD1[OF _ i j i])

lemma not_add_less2 [simp]:
  assumes "i \<in> Nat" and "j \<in> Nat"
  shows "(j + i < i) = FALSE"
using assms by (simp add: add_commute_nat)

lemma add_leqD1:
  assumes "m + k \<le> n" and "k \<in> Nat" and "m \<in> Nat" and "n \<in> Nat"
  shows "m \<le> n"
using assms by (intro nat_leq_trans[of "m" "m+k" "n"], simp+)

lemma add_leqD2:
  assumes "m+k \<le> n" and "k \<in> Nat" and "m \<in> Nat" and "n \<in> Nat"
  shows "k \<le> n"
using assms by (intro nat_leq_trans[of "k" "m+k" "n"], simp+)

lemma add_leqE:
  assumes "m+k \<le> n" and "k \<in> Nat" and "m \<in> Nat" and "n \<in> Nat"
  shows "(m \<le> n \<Longrightarrow> k \<le> n \<Longrightarrow> R) \<Longrightarrow> R"
using assms by (blast dest: add_leqD1 add_leqD2)

lemma leq_add_left_false [simp]:
  assumes mdom: "m \<in> Nat" and ndom: "n \<in> Nat" and n0: "n \<noteq> 0"
  shows "m + n \<le> m = FALSE"
    proof -
    have s1_1: "m + n \<le> m = (m + n < m \<or> m + n = m)"
        proof -
        define p where "p \<equiv> m + n"
        have s2_1: "p \<le> m = (p < m \<or> p = m)"
            using mdom nat_leq_less by auto
        show ?thesis
            using s2_1 by (auto simp: p_def)
        qed
    have s1_2: "(m + n = m) = (n = 0)"
        using mdom ndom add_eq_self_zero_nat[of "m" "n"] by auto
    have s1_3: "(m + n <= m) = (m + n < m)"
        using n0 s1_1 s1_2 by auto
    have s1_4: "(m + n < m) = FALSE"
        using mdom ndom not_add_less1[of "m" "n"] by auto
    show ?thesis
        using s1_3 s1_4 by auto
    qed


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
  have 1: "?lhs \<Rightarrow> ?rhs"
  proof
    assume mn: "m \<le> n"
    with m n have "n = m + (n -- m)" by simp
    with m n show "?rhs" by blast
  qed
  from assms have 2: "?rhs \<Rightarrow> ?lhs" by auto
  from 1 2 assms show ?thesis by blast
qed

lemma less_imp_adiff_less:
  assumes jk: "j < k" and j: "j \<in> Nat" and k: "k \<in> Nat" and n: "n \<in> Nat"
  shows "j -- n < k"
    proof -
    have s1_1: "j -- n \<in> Nat"
        using j n by simp+
    have s1_2: "j -- n \<le> j"
        using j n by simp+
    show ?thesis
        using j k jk s1_1 s1_2 nat_leq_less_trans by auto
    qed

lemma adiff_Succ_less (*[simp]*):
  assumes i: "i \<in> Nat" and n: "n \<in> Nat"
  shows "0 < n \<Longrightarrow> n -- Succ[i] < n"
using n apply cases
using i by auto

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

lemma zero_less_adiff [simp]:
  assumes m: "m \<in> Nat" and n: "n \<in> Nat"
  shows "(0 < n -- m) = (m < n)"
by (induct m n rule: diffInduct, simp_all add: assms)

lemma less_imp_add_positive:
  assumes ij: "i < j" and i: "i \<in> Nat" and j: "j \<in> Nat"
  shows "\<exists>k \<in> Nat: 0 < k \<and> i + k = j"
proof -
  have s1_1: "i + (j -- i) = j"
    using i j ij le_add_adiff_inverse by (auto simp: less_def)
  have s1_2: "j -- i \<in> Nat"
    using assms by simp+
  have s1_3: "0 < j -- i"
    using assms zero_less_adiff by auto
  show ?thesis
    using s1_1 s1_2 s1_3 by blast
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

lemma leq_adiff_right_false [simp]:
  assumes "n \<noteq> 0" "n \<le> m" and m: "m \<in> Nat" and n: "n \<in> Nat"
  shows "m \<le> m -- n = FALSE"
using assms by (simp add: leq_adiff_right_add_left[OF _ m m n])

lemma leq_adiff_right_imp_0:
  assumes h:"n \<le> n -- p" "p \<le> n" and n: "n \<in> Nat" and p: "p \<in> Nat"
  shows "p = 0"
using p h apply (induct)
using n by auto


subsubsection \<open> Monotonicity of Multiplication \<close>

(* from HOL/Ring_and_Field.thy *)

lemma mult_leq_left_mono:
  assumes 1:"a \<le> b" and a: "a \<in> Nat" and b: "b \<in> Nat" and c: "c \<in> Nat"
  shows "c * a \<le> c * b"
using c apply induct
using 1 a b by (simp_all add: add_leq_mono)

lemma mult_leq_right_mono:
  assumes 1:"a \<le> b" and a: "a \<in> Nat" and b: "b \<in> Nat" and c: "c \<in> Nat"
  shows "a * c \<le> b * c"
using c apply induct
using 1 a b by (simp_all add: add_leq_mono add_commute_nat)

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

text \<open> strict, in 1st argument \<close>

lemma mult_less_left_mono:
  assumes ij: "i < j" and k0: "0 < k" and
    idom: "i \<in> Nat" and jdom: "j \<in> Nat" and kdom: "k \<in> Nat"
  shows "k * i < k * j"
    proof -
    have s1_1: "Succ[0] * i < Succ[0] * j"
        using mult_1_left_nat ij idom jdom by auto
    have s1_2: "\<And> n.  \<lbrakk>
            n \<in> Nat;
            Succ[n] * i < Succ[n] * j
        \<rbrakk> \<Longrightarrow>
            Succ[Succ[n]] * i < Succ[Succ[n]] * j"
        proof -
        fix "n" :: "c"
        assume s1_2_ndom: "n \<in> Nat"
        assume s1_2_induct: "Succ[n] * i < Succ[n] * j"
        have s2_1: "Succ[n] * i + i < Succ[n] * j + j"
            proof -
            have s3_1: "Succ[n] \<in> Nat"
                using s1_2_ndom succIsNat by auto
            have s3_2: "Succ[n] * i \<in> Nat"
                using s3_1 idom multIsNat by auto
            have s3_3: "Succ[n] * j \<in> Nat"
                using s3_1 jdom multIsNat by auto
            show ?thesis
                using s3_2 s3_3 idom jdom s1_2_induct ij
                    add_less_mono by auto
            qed
        have s2_2: "i * Succ[n] + i < j * Succ[n] + j"
            proof -
            have s3_1: "Succ[n] \<in> Nat"
                using s1_2_ndom succIsNat by auto
            have s3_2: "Succ[n] * i = i * Succ[n]"
                using s3_1 idom mult_commute_nat by auto
            have s3_3: "Succ[n] * j = j * Succ[n]"
                using s3_1 jdom mult_commute_nat by auto
            show ?thesis
                using s2_1 s3_2 s3_3 by auto
            qed
        have s2_3: "i * Succ[Succ[n]] < j * Succ[Succ[n]]"
            proof -
            have s3_1: "Succ[n] \<in> Nat"
                using s1_2_ndom succIsNat by auto
            have s3_2: "i * Succ[Succ[n]] = i * Succ[n] + i"
                using idom s3_1 multnat_Succ by (auto simp: nat_mult_def)
            have s3_3: "j * Succ[Succ[n]] = j * Succ[n] + j"
                using jdom s3_1 multnat_Succ by (auto simp: nat_mult_def)
            show ?thesis
                using s2_2 s3_2 s3_3 by auto
            qed
        have s2_4: "i * Succ[Succ[n]] = Succ[Succ[n]] * i"
            proof -
            have s3_1: "Succ[Succ[n]] \<in> Nat"
                using s1_2_ndom succIsNat by auto
            show ?thesis
                using s3_1 idom mult_commute_nat by auto
            qed
        have s2_5: "j * Succ[Succ[n]] = Succ[Succ[n]] * j"
            proof -
            have s3_1: "Succ[Succ[n]] \<in> Nat"
                using s1_2_ndom succIsNat by auto
            show ?thesis
                using s3_1 jdom mult_commute_nat by auto
            qed
        show "Succ[Succ[n]] * i < Succ[Succ[n]] * j"
            using s2_3 s2_4 s2_5 by auto
        qed
    have s1_3: "\<forall> n \<in> Nat:  Succ[n] * i < Succ[n] * j"
        using s1_1 s1_2
            natInduct[of "\<lambda> q.  Succ[q] * i < Succ[q] * j"] by auto
    show ?thesis
        using s1_3 nat_gt0_iff_Succ[of "k"] k0 kdom by auto
    qed

lemma mult_less_right_mono:
  assumes 1: "i < j" "0 < k" and i: "i \<in> Nat" and j: "j \<in> Nat" and k: "k \<in> Nat"
  shows "i * k < j * k"
    proof -
    have s1_1: "k * i < k * j"
        using 1 i j k mult_less_left_mono by auto
    have s1_2: "k * i = i * k"
        using i k mult_commute_nat by auto
    have s1_3: "k * j = j * k"
        using j k mult_commute_nat by auto
    show ?thesis
        using s1_1 s1_2 s1_3 by auto
    qed

lemma nat_0_less_mult_iff [simp]:
  assumes i: "i \<in> Nat" and j: "j \<in> Nat"
  shows "(0 < i * j) = (0 < i \<and> 0 < j)"
using i apply induct
  using j apply simp
  using j apply(induct, simp_all)
done

lemma one_leq_mult_iff (*[simp]*):
  assumes m: "m \<in> Nat" and n: "n \<in> Nat"
  shows "(1 \<le> m * n) = (1 \<le> m \<and> 1 \<le> n)"
using assms nat_gt0_not0 by simp

lemma mult_less_cancel_left [simp]:
  assumes m: "m \<in> Nat" and n: "n \<in> Nat" and k: "k \<in> Nat"
  shows "(k * m < k * n) = (0 < k \<and> m < n)"
proof (auto intro!: mult_less_left_mono[OF _ _ m n k])
  assume "k*m < k*n"
  from k m n this show "0 < k" by (cases k, simp_all)
next
  assume 1: "k*m < k*n"
  show "m < n"
  proof (rule contradiction)
    assume "\<not>(m < n)"
    with m n k have "k*n \<le> k*m" by (simp add: nat_not_order_simps mult_leq_left_mono)
    with m n k have "\<not>(k*m < k*n)" by (simp add: nat_not_order_simps)
    with 1 show "FALSE" by simp
  qed
qed

lemma mult_less_cancel_right [simp]:
  assumes m: "m \<in> Nat" and n: "n \<in> Nat" and k: "k \<in> Nat"
  shows "(m * k < n * k) = (0 < k \<and> m < n)"
proof (auto intro!: mult_less_right_mono[OF _ _ m n k])
  assume "m*k < n*k"
  from k m n this show "0 < k" by (cases k, simp_all)
next
  assume 1: "m*k < n*k"
  show "m < n"
  proof (rule contradiction)
    assume "\<not>(m < n)"
    with m n k have "n*k \<le> m*k" by (simp add: nat_not_order_simps mult_leq_right_mono)
    with m n k have "\<not>(m*k < n*k)" by (simp add: nat_not_order_simps)
    with 1 show "FALSE" by simp
  qed
qed

lemma mult_less_self_left [dest]:
  assumes less: "n * k < n" and n: "n \<in> Nat" and k: "k \<in> Nat"
  shows "k=0"
    proof -
    have s1_1: "1 \<le> k ==> FALSE"
        proof -
        assume s1_1_asm: "1 \<le> k"
        have s2_1: "n * 1 \<le> n * k"
            using n k oneIsNat s1_1_asm mult_leq_left_mono[of "1" "k" "n"]
                by auto
        have s2_2: "n \<le> n * k"
            proof -
            have s3_1: "n * 1 = n"
                using n mult_1_right_nat by auto
            show ?thesis
                using s2_1 s3_1 by auto
            qed
        define p where "p \<equiv> n"
        define q where "q \<equiv> n * k"
        have s2_3: "q < p"
            unfolding p_def q_def using less by auto
        have s2_4: "n < p"
            proof -
            have s3_1: "q \<in> Nat"
                unfolding q_def using n k multIsNat by auto
            have s3_2: "p \<in> Nat"
                unfolding p_def using n by auto
            have s3_3: "n \<le> q"
                unfolding q_def using s2_2 by auto
            show ?thesis
                using s3_1 s3_2 n s3_3 s2_3
                    nat_leq_less_trans[of "n" "q" "p"]
                    by auto
            qed
        have s2_5: "n \<noteq> n"
            using s2_4 by (auto simp: less_def p_def)
        show "FALSE"
            using s2_5 by auto
        qed
    have s1_2: "\<not> (1 \<le> k)"
        using s1_1 by auto
    show ?thesis
        using s1_2 k nat_not_leq_one[of "k"] by auto
    qed

lemma mult_less_self_right [dest]:
  assumes less: "k*n < n" and n: "n \<in> Nat" and k: "k \<in> Nat"
  shows "k=0"
    proof -
    have s1_1: "n * k < n"
        proof -
        have s2_1: "k * n = n * k"
            using n k mult_commute_nat by auto
        show ?thesis
            using less s2_1 by auto
        qed
    show ?thesis
        using s1_1 n k mult_less_self_left by auto
    qed

lemma mult_leq_cancel_left [simp]:
  assumes m: "m \<in> Nat" and n: "n \<in> Nat" and k: "k \<in> Nat"
  shows "(k * m \<le> k * n) = (k = 0 \<or> m \<le> n)"
    proof -
    have s1_1: "(k * m \<le> k * n) ==> (k = 0 \<or> m \<le> n)"
        proof -
        assume s1_1_asm: "k * m \<le> k * n"
        have s2_1: "\<not> (k = 0) ==> m \<le> n"
            proof -
            assume s2_1_asm: "\<not> (k = 0)"
            have s3_1: "k > 0"
                using k nat_gt0_not0 s2_1_asm by auto
            have s3_2: "\<not>(m \<le> n) ==> FALSE"
                proof -
                assume s3_2_asm: "\<not>(m \<le> n)"
                have s2_1: "n < m"
                    using s3_2_asm m n nat_not_leq[of "m" "n"] by auto
                have s2_2: "k * n < k * m"
                    using s3_1 s2_1 m n k mult_less_left_mono[of "n" "m" "k"] by auto
                with m n k have s2_3: "\<not> (k * m \<le> k * n)"
                    by (simp add: nat_not_order_simps)
                show "FALSE"
                    using s2_2 s2_3 s1_1_asm by auto
                qed
            show "m \<le> n"
                using s3_2 by auto
            qed
        show "k = 0 \<or> m \<le> n"
            using s2_1 by auto
        qed
    have s1_2: "(k = 0 \<or> m \<le> n) ==> (k * m \<le> k * n)"
        proof -
        assume s1_2_asm: "k = 0 \<or> m \<le> n"
        have s2_1: "k = 0 ==> k * m \<le> k * n"
            proof -
            assume s2_1_asm: "k = 0"
            have s3_1: "k * m = 0"
                using s2_1_asm m mult_0_left_nat by auto
            have s3_2: "k * n = 0"
                using s2_1_asm n mult_0_left_nat by auto
            show "k * m \<le> k * n"
                using s3_1 s3_2 by auto
            qed
        have s2_2: "m \<le> n ==> k * m \<le> k * n"
            proof -
            assume s2_2_asm: "m \<le> n"
            show "k * m \<le> k * n"
                using s2_2_asm m n k mult_leq_left_mono by auto
            qed
        show "k * m \<le> k * n"
            using s1_2_asm s2_1 s2_2 by auto
        qed
    show ?thesis
        using s1_1 s1_2 by auto
    qed

lemma mult_leq_cancel_right [simp]:
  assumes m: "m \<in> Nat" and n: "n \<in> Nat" and k: "k \<in> Nat"
  shows "(m * k \<le> n * k) = (k = 0 \<or> m \<le> n)"
    proof -
    have s1_1: "(k * m \<le> k * n) = (k = 0 \<or> m \<le> n)"
        using m n k mult_leq_cancel_left by auto
    have s1_2: "k * m = m * k"
        using k m mult_commute_nat by auto
    have s1_3: "k * n = n * k"
        using k n mult_commute_nat by auto
    show ?thesis
        using s1_1 s1_2 s1_3 by auto
    qed

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
  also have "... = ?rhs" by (rule mult_cancel1_nat[OF m n oneIsNat])
  finally show ?thesis .
qed

end
