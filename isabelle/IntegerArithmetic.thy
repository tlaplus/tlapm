(*  Title:      TLA+/IntegerArithmetic.thy
    Author:     Stephan Merz, Inria Nancy
    Copyright (C) 2009-2022  INRIA and Microsoft Corporation
    License:    BSD
    Version:    Isabelle2021-1
*)

section \<open> Arithmetic (except division) for the integers \<close>

theory IntegerArithmetic
imports Integers
begin

named_theorems algebra_simps "algebra simplification rules"

text \<open>
  The rewrites accumulated in @{text algebra_simps} deal with the
  classical algebraic structures of groups, rings and family. They simplify
  terms by multiplying everything out (in case of a ring) and bringing sums and
  products into a canonical form (by ordered rewriting). As a result these
  rewrites decide the equational theory of groups and rings but also help 
  with inequalities.
\<close>


subsection \<open> Addition and difference of integers \<close>

text \<open>
  We define integer addition as a recursive function.
  Subtraction is just addition of the complement, and
  is introduced as an abbreviation.
\<close>

definition pr_addint where
"pr_addint(a) \<equiv> int_primrec(Int, a, \<lambda>n x y. succ[x], \<lambda>n x y. pred[y])"

definition addint  :: "[c,c] \<Rightarrow> c"         (infixl "+" 65)
where "\<lbrakk>a \<in> Int; b \<in> Int\<rbrakk> \<Longrightarrow> (a + b) \<equiv> pr_addint(a)[b]"

abbreviation subint (infixl "-" 65)
where "a - b \<equiv> a + (-b)"

text \<open> Closure \<close>

lemma pr_addintType:
  assumes "a \<in> Int" shows "pr_addint(a) \<in> [Int \<rightarrow> Int]"
  using assms unfolding pr_addint_def by (rule int_primrecType) auto

lemma addintType [iff]: "\<lbrakk>a \<in> Int; b \<in> Int\<rbrakk> \<Longrightarrow> a+b \<in> Int"
  unfolding addint_def by (blast dest: pr_addintType)

text \<open> Base case and successor cases \<close>

lemma pr_addint_0: "a \<in> Int \<Longrightarrow> pr_addint(a)[0] = a"
  by (rule int_primrecE[OF pr_addint_def[THEN meta_to_obj_eq]]) auto

lemma add_0_int [simp]: "a \<in> Int \<Longrightarrow> a + 0 = a"
  by (simp add: addint_def pr_addint_0)

lemma pr_addint_SuccNat: 
  "\<lbrakk>a \<in> Int; n \<in> Nat\<rbrakk> \<Longrightarrow> pr_addint(a)[succ[n]] = succ[pr_addint(a)[n]]"
  by (rule int_primrecE[OF pr_addint_def[THEN meta_to_obj_eq]]) auto

lemma pr_addint_uminusSuccNat: 
  "\<lbrakk>a \<in> Int; n \<in> Nat\<rbrakk> \<Longrightarrow> pr_addint(a)[-succ[n]] = pred[pr_addint(a)[-n]]"
  by (rule int_primrecE[OF pr_addint_def[THEN meta_to_obj_eq]]) auto

lemma addint_succ [simp]:
  assumes a: "a \<in> Int" and b: "b \<in> Int"
  shows "a + succ[b] = succ[a+b]"
  using b a
  by (cases b)
     (auto dest: pr_addintType 
           simp: addint_def pr_addint_SuccNat pr_addint_uminusSuccNat)

lemma addint_pred [simp]:
  assumes a: "a \<in> Int" and b: "b \<in> Int"
  shows "a + pred[b] = pred[a+b]"
  using b a
  by (cases b)
     (auto dest: pr_addintType
           simp: addint_def pr_addint_SuccNat pr_addint_uminusSuccNat pred0 sym[OF uminusSucc])

lemma subint_succ [simp]:
  assumes "a \<in> Int" and "b \<in> Int"
  shows "a - succ[b] = pred[a-b]"
  using assms by (simp add: uminusSucc)

lemma subint_pred [simp]:
  assumes "a \<in> Int" and "b \<in> Int"
  shows "a - pred[b] = succ[a-b]"
  using assms by (simp add: uminusPred)

lemma addintNat [simp]:
  assumes m: "m \<in> Nat" and n: "n \<in> Nat"
  shows "m + n \<in> Nat"
  using n m by induct auto

lemma addint_0_left [simp]:
  assumes "a \<in> Int"
  shows "0 + a = a"
  using assms 
  by induct (auto simp: uminusSucc)

lemma add_succ_left [simp]:
  assumes a: "a \<in> Int" and b: "b \<in> Int"
  shows "succ[a] + b = succ[a + b]"
  using b a by (induct b) auto

lemma add_pred_left [simp]:
  assumes a: "a \<in> Int" and b: "b \<in> Int"
  shows "pred[a] + b = pred[a + b]"
  using b a by (induct b) auto

lemma add_uminus_succ_left [simp]:
  assumes "a \<in> Int" and "b \<in> Int"
  shows "-succ[a] + b = pred[-a + b]"
  using assms by (simp add: uminusSucc)

lemma add_uminus_pred_left [simp]:
  assumes "a \<in> Int" and "b \<in> Int"
  shows "-pred[a] + b = succ[-a + b]"
  using assms by (simp add: uminusPred)

lemma succ_pred_add [simp]:
  assumes a: "a \<in> Int" and b: "b \<in> Int"
  shows "succ[pred[a] + b] = a + b"
  using b a by induct auto

lemma pred_succ_add [simp]:
  assumes a: "a \<in> Int" and b: "b \<in> Int"
  shows "pred[succ[a] + b] = a + b"
  using b a by induct auto

lemma subint_self [simp]:
  assumes "a \<in> Int"
  shows "a - a = 0"
  using assms by induct auto

lemma addint_uminus_self [simp]:
  assumes "a \<in> Int"
  shows "-a + a = 0"
  using assms by induct auto

lemma uminus_add [simp]:
  assumes a: "a \<in> Int" and b: "b \<in> Int"
  shows "-(a + b) = -a - b"
  using b a by induct (auto simp: uminusSucc)

text \<open> Commutativity \<close>

lemma add_commute [algebra_simps]:
  assumes a: "a \<in> Int" and b: "b \<in> Int"
  shows "a + b = b + a"
  using b a by (induct b) (auto simp: uminusSucc)

text \<open> Associativity \<close>

lemma add_assoc [algebra_simps]:
  assumes "a \<in> Int" and "b \<in> Int" and "c \<in> Int"
  shows "a + (b + c) = (a + b) + c"
  using assms by induct simp+

lemma add_left_commute [algebra_simps]:
  assumes "a \<in> Int" and "b \<in> Int" and "c \<in> Int"
  shows "a + (b + c) = b + (a + c)"
  using assms by (simp only: add_assoc add_commute)

lemma add_right_commute:
  assumes "a \<in> Int" and "b \<in> Int" and "c \<in> Int"
  shows "a + b + c = a + c + b"
proof -
  from assms have "a + b + c = a + (b + c)"
    by (rule sym[OF add_assoc])
  also from assms have "\<dots> = a + (c + b)"
    by (simp add: add_commute)
  finally show ?thesis
    using assms by (simp add: add_assoc)
qed

lemmas add_ac = add_assoc add_commute add_left_commute


text \<open> Cancellation rules \<close>

lemma add_left_cancel [simp]:
  assumes "a \<in> Int" and "b \<in> Int" and "c \<in> Int"
  shows "(a + b = a + c) = (b = c)"
  using assms by induct simp+

lemma add_right_cancel [simp]:
  assumes "a \<in> Int" and "b \<in> Int" and "c \<in> Int"
  shows "(b + a = c + a) = (b = c)"
  using assms by induct simp+

lemma add_eq_self1 [simp]:
  assumes "a \<in> Int" and "b \<in> Int"
  shows "(a + b = a) = (b = 0)"
  using assms by induct (simp add: uminusSucc)+

lemma add_eq_self2 [simp]:
  "\<lbrakk>a \<in> Int; b \<in> Int\<rbrakk> \<Longrightarrow> (a = a + b) = (b = 0)"
  "\<lbrakk>a \<in> Int; b \<in> Int\<rbrakk> \<Longrightarrow> (b + a = a) = (b = 0)"
  "\<lbrakk>a \<in> Int; b \<in> Int\<rbrakk> \<Longrightarrow> (a = b + a) = (b = 0)"
  by (auto simp: add_commute dest: sym)

lemma succ_add_eq_self1 [simp]:
  assumes "a \<in> Int" and "b \<in> Int"
  shows "(succ[a+b] = a) = (b = -1)"
proof -
  {
    assume "succ[a+b] = a"
    with assms have "a + succ[b] = a" by simp
    with assms add_eq_self1[of "a" "succ[b]"] 
    have "succ[b] = 0" by simp
    hence "pred[succ[b]] = pred[0]" by simp
    with assms have "b = -1" by (simp add: pred0)
  }
  with assms show ?thesis by auto
qed

lemma succ_add_eq_self2 [simp]:
  "\<lbrakk>a \<in> Int; b \<in> Int\<rbrakk> \<Longrightarrow> (succ[b+a] = a) = (b = -1)"
  "\<lbrakk>a \<in> Int; b \<in> Int\<rbrakk> \<Longrightarrow> (a = succ[a+b]) = (b = -1)"
  "\<lbrakk>a \<in> Int; b \<in> Int\<rbrakk> \<Longrightarrow> (a = succ[b+a]) = (b = -1)"
  by (auto simp: add_commute dest: sym)

lemma pred_add_eq_self1 [simp]:
  assumes "a \<in> Int" and "b \<in> Int"
  shows "(pred[a+b] = a) = (b = 1)"
proof -
  {
    assume "pred[a+b] = a"
    with assms have "a + pred[b] = a" by simp
    with assms add_eq_self1[of "a" "pred[b]"] 
    have "pred[b] = 0" by simp
    hence "succ[pred[b]] = succ[0]" by simp
    with assms have "b = 1" by simp
  }
  with assms show ?thesis by auto
qed

lemma pred_add_eq_self2 [simp]:
  "\<lbrakk>a \<in> Int; b \<in> Int\<rbrakk> \<Longrightarrow> (pred[b+a] = a) = (b = 1)"
  "\<lbrakk>a \<in> Int; b \<in> Int\<rbrakk> \<Longrightarrow> (a = pred[a+b]) = (b = 1)"
  "\<lbrakk>a \<in> Int; b \<in> Int\<rbrakk> \<Longrightarrow> (a = pred[b+a]) = (b = 1)"
  by (auto simp: add_commute dest: sym)


text \<open> Rules about integer difference \<close>

lemma diff_diff_left:
  assumes a: "a \<in> Int" and b: "b \<in> Int" and c: "c \<in> Int"
  shows "(a - b) - c = a - (b + c)"
  using assms by (simp add: add_assoc)

lemma add_diff_same_1 [simp]:
  assumes "a \<in> Int" and "b \<in> Int"
  shows "(a + b) - a = b"
  using assms by (simp add: add_ac)

lemma add_diff_same_2 [simp]:
  assumes "a \<in> Int" and "b \<in> Int"
  shows "(a + b) - b = a"
proof -
  from assms have "(a + b) - b = a + (b - b)"
    by (intro sym[OF add_assoc]) auto
  with assms show ?thesis by simp
qed

lemma diff_add_same_1 [simp]:
  assumes "a \<in> Int" and "b \<in> Int"
  shows "(a - b) + b = a"
  using assms add_diff_same_2[of "a" "-b"] by simp

lemma diff_add_same_2 [simp]:
  assumes "a \<in> Int" and "b \<in> Int"
  shows "(-a + b) + a = b"
  using assms by (simp add: add_ac)

lemma add_diff_cancel_left [simp]:
  assumes "a \<in> Int" and "b \<in> Int" and "c \<in> Int"
  shows "(a + b) - (a + c) = b - c"
  using assms by (simp add: add_ac)

lemma add_diff_cancel_right [simp]:
  assumes "a \<in> Int" and "b \<in> Int" and "c \<in> Int"
  shows "(a + b) - (c + b) = a - c" (is "?lhs = ?rhs")
proof -
  from assms have "?lhs = a + (b - (c + b))"
    by (intro sym[OF add_assoc]) simp+
  also have "\<dots> = ?rhs"
    using assms by (simp add: add_ac)
  finally show ?thesis .
qed

lemma add_left_diff_right:
  assumes "a \<in> Int" and "b \<in> Int" and "c \<in> Int"
  shows "(a + b = c) = (a = c - b)"
proof -
  {
    assume "a + b = c"
    hence "(a + b) - b = c - b" by simp
    with assms have "a = c - b" by simp
  }
  moreover
  {
    assume "a = c - b"
    hence "a + b = (c - b) + b" by simp 
    with assms have "a + b = c" by simp
  }
  ultimately show ?thesis by auto
qed

lemma diff_0_eq [simp]:
  assumes "a \<in> Int" and "b \<in> Int"
  shows "(a - b = 0) = (a = b)"
proof -
  {
    assume "a - b = 0"
    hence "(a - b) + b = 0 + b" by simp
    with assms have "a = b" by simp
  }
  with assms show ?thesis by auto
qed

lemma add_right_diff_left:
  assumes "a \<in> Int" and "b \<in> Int" and "c \<in> Int"
  shows "(a = b + c) = (c = a - b)"
  using assms by (auto simp: add_left_diff_right add_assoc)

lemma diff_0_eqs [simp]:
  "\<lbrakk>a \<in> Int; b \<in> Int\<rbrakk> \<Longrightarrow> (-a + b = 0) = (a = b)"
  "\<lbrakk>a \<in> Int; b \<in> Int\<rbrakk> \<Longrightarrow> (0 = a - b) = (a = b)"
  "\<lbrakk>a \<in> Int; b \<in> Int\<rbrakk> \<Longrightarrow> (0 = -a + b) = (a = b)"
  by (auto simp: add_commute dest: sym)

text \<open> Reasoning about @{text "m + n = 0"}, etc. \<close>

lemma add_is_0_nat:
  assumes m: "m \<in> Nat" and n: "n \<in> Nat"
  shows "(m + n = 0) = (m = 0 \<and> n = 0)"
  using m apply cases
  using n by (induct, auto)

lemma zero_is_add_nat:
  assumes m: "m \<in> Nat" and n: "n \<in> Nat"
  shows "(0 = m + n) = (m = 0 \<and> n = 0)"
  using m apply cases
  using n by (induct, auto)

lemma add_is_1_nat:
  assumes m: "m \<in> Nat" and n: "n \<in> Nat"
  shows "(m + n = 1) = (m = 1 \<and> n = 0 \<or> m = 0 \<and> n = 1)"
  using m apply cases
  using n by (induct, auto simp: add_is_0_nat)

lemma one_is_add_nat:
  assumes m: "m \<in> Nat" and n: "n \<in> Nat"
  shows "(1 = m + n) = (m = 1 \<and> n = 0 \<or> m = 0 \<and> n = 1)"
  using m apply (rule natCases)
  using n by (induct, auto simp: zero_is_add_nat)


subsection \<open> Multiplication of natural numbers \<close>

definition pr_multint where
"pr_multint(a) \<equiv> int_primrec(Int, 0, \<lambda>n x y. x+a, \<lambda>n x y. y-a)"

definition multint  :: "[c,c] \<Rightarrow> c"         (infixl "*" 70)
where "\<lbrakk>a \<in> Int; b \<in> Int\<rbrakk> \<Longrightarrow> (a * b) \<equiv> pr_multint(a)[b]"

text \<open> Closure \<close>

lemma pr_multintType:
  assumes "a \<in> Int" shows "pr_multint(a) \<in> [Int \<rightarrow> Int]"
  using assms unfolding pr_multint_def
  by (intro int_primrecType) auto

lemma multintType [iff]: "\<lbrakk>a \<in> Int; b \<in> Int\<rbrakk> \<Longrightarrow> a*b \<in> Int"
  unfolding multint_def by (blast dest: pr_multintType)

text \<open> Base case and successor cases \<close>

lemma pr_multint_0: "a \<in> Int \<Longrightarrow> pr_multint(a)[0] = 0"
  by (rule int_primrecE[OF pr_multint_def[THEN meta_to_obj_eq]]) auto

lemma times_0 [simp]: "a \<in> Int \<Longrightarrow> a * 0 = 0"
  by (simp add: multint_def pr_multint_0)

lemma pr_multint_SuccNat: 
  "\<lbrakk>a \<in> Int; n \<in> Nat\<rbrakk> \<Longrightarrow> pr_multint(a)[succ[n]] = pr_multint(a)[n] + a"
  by (rule int_primrecE[OF pr_multint_def[THEN meta_to_obj_eq]]) auto

lemma pr_multint_uminusSuccNat: 
  "\<lbrakk>a \<in> Int; n \<in> Nat\<rbrakk> \<Longrightarrow> pr_multint(a)[-succ[n]] = pr_multint(a)[-n] - a"
  by (rule int_primrecE[OF pr_multint_def[THEN meta_to_obj_eq]]) auto

lemma times_succ [simp]:
  assumes a: "a \<in> Int" and b: "b \<in> Int"
  shows "a * succ[b] = a*b + a"
  using b a
  by (cases b)
     (simp add: multint_def pr_multint_SuccNat pr_multint_uminusSuccNat 
                pr_multintType[THEN funcSetValue])+

lemma times_pred [simp]:
  assumes a: "a \<in> Int" and b: "b \<in> Int"
  shows "a * pred[b] = a*b - a"
  using b a
  by (cases b)
     (simp add: multint_def pr_multint_SuccNat pr_multint_uminusSuccNat 
                pr_multintType[THEN funcSetValue] pred0 sym[OF uminusSucc])+

lemma times_uminus_right [simp]:
  assumes a: "a \<in> Int" and b: "b \<in> Int"
  shows "a * (-b) = -(a * b)"
using b proof induct
  case 0
  with a show ?case by simp
next
  case (pos n)
  with a show ?case by (simp add: uminusSucc)
next
  case (neg n)
  with a show ?case
    by simp (simp add: uminusSucc)
qed

lemma times_nat [simp]:
  assumes m: "m \<in> Nat" and n: "n \<in> Nat"
  shows "m * n \<in> Nat"
  using n m by induct simp+

lemma times_0_left [simp]:
  assumes "a \<in> Int"
  shows "0 * a = 0"
  using assms by induct simp+

lemma times_succ_left [simp]:
  assumes a: "a \<in> Int" and b: "b \<in> Int"
  shows "succ[a] * b = a * b + b"
using b proof induct
  case 0
  with a show ?case by simp
next
  case (pos n)
  with a show ?case by (simp add: add_ac)
next
  case (neg n)
  with a show ?case 
    (* the two applications of simp cannot be combined ... *)
    by (simp add: add_right_commute) (simp add: uminusSucc)
qed

lemma times_pred_left [simp]:
  assumes a: "a \<in> Int" and b: "b \<in> Int"
  shows "pred[a] * b = a*b - b"
  using b a by induct (simp add: add_right_commute)+

text \<open> Commutativity \<close>

lemma times_commute [algebra_simps]:
  assumes "a \<in> Int" and "b \<in> Int"
  shows "a * b = b * a"
using assms by induct (simp add: uminusSucc)+

lemma times_uminus_left [simp]:
  assumes "a \<in> Int" and "b \<in> Int"
  shows "(-a) * b = -(a * b)"
  using assms by (simp add: times_commute)

text \<open> Distributivity \<close>

lemma add_times_distrib_left [algebra_simps]:
  assumes "a \<in> Int" and "b \<in> Int" and "c \<in> Int"
  shows "a * (b + c) = a * b + a * c"
  using assms by induct (simp add: uminusSucc add_right_commute add_assoc)+

lemma add_times_distrib_right [algebra_simps]:
  assumes a: "a \<in> Int" and b: "b \<in> Int" and c: "c \<in> Int"
  shows "(b + c) * a = b * a + c * a"
  using assms by (simp add: times_commute add_times_distrib_left)

\<comment> \<open> NOT added as rewrites, since sometimes they are used from right to left \<close>
lemmas int_distrib = add_times_distrib_left add_times_distrib_right

(*
text \<open> Identity element \<close>

(no longer?) used for arithmetic simplification setup 
lemma times_1_right: "a \<in> Int \<Longrightarrow> a * 1 = a" by simp
lemma times_1_left: "a \<in> Int \<Longrightarrow> 1 * a = a" by simp
lemma times_uminus_1_right: "a \<in> Int \<Longrightarrow> a * (-1) = -a" by simp
lemma times_uminus_1_left: "a \<in> Int \<Longrightarrow> (-1) * a = -a" by simp
*)

text \<open> Associativity \<close>

lemma times_assoc [algebra_simps]:
  assumes "a \<in> Int" and "b \<in> Int" and "c \<in> Int"
  shows "a * (b * c) = (a * b) * c"
  using assms by induct (auto simp add: add_times_distrib_right)

lemma times_left_commute [algebra_simps]:
  assumes "a \<in> Int" and "b \<in> Int" and "c \<in> Int"
  shows "a * (b * c) = b * (a * c)"
using assms by (simp only: times_commute times_assoc)

(* from HOL/OrderedGroups.thy *)
lemmas times_ac = times_assoc times_commute times_left_commute

lemma times_right_commute:
  assumes "a \<in> Int" and "b \<in> Int" and "c \<in> Int"
  shows "a * b * c = a * c * b"
proof -
  from assms have "a * b * c = a * (b * c)"
    by (rule sym[OF times_assoc])
  also from assms have "\<dots> = a * (c * b)"
    by (simp add: times_commute)
  finally show ?thesis
    using assms by (simp add: times_assoc)
qed

text \<open> Reasoning about @{text "m * n = 0"}, etc. \<close>

lemma times_is_0_iff [simp]:
  assumes a: "a \<in> Int" and b: "b \<in> Int"
  shows "(a * b = 0) = (a = 0 \<or> b = 0)"
using a proof cases
  case 0
  with b show ?thesis by simp
next
  case (pos n)
  with b show ?thesis
    by cases auto
next
  case na: (neg n)
  with b show ?thesis
  proof cases
    case 0
    with na show ?thesis by simp
  next
    case (pos m)
    with na have "n * m + m + n \<in> Nat" 
      by simp
    hence "pred[-(n * m + m + n)] \<noteq> 0"
      by (simp add: sym[OF uminusSucc])
    with na pos show ?thesis by simp
  next
    case (neg m)
    with na have "n * m + m + n \<in> Nat" 
      by simp
    hence "pred[-(n * m + m + n)] \<noteq> 0"
      by (simp add: sym[OF uminusSucc])
    with na neg show ?thesis by simp
  qed
qed

lemma zero_istimes_iff [simp]:
  assumes a: "a \<in> Int" and b: "b \<in> Int"
  shows "(0 = a * b) = (a = 0 \<or> b = 0)"
  using assms by (auto dest: sym)

lemma times_is_1_iff [simp]:
  assumes a: "a \<in> Int" and b: "b \<in> Int"
  shows "(a * b = 1) = ((a = 1 \<and> b = 1) \<or> (a = -1 \<and> b = -1))"
using a proof induct
  case 0
  with b show ?case by simp
next
  case (pos n)
  with b show ?case by cases (auto simp: add_is_0_nat)
next
  case na: (neg n)
  with b show ?case 
  proof cases
    case 0
    with na show ?thesis by simp
  next
    case (pos m)
    with na have "n * m + m + n \<in> Nat" 
      by simp
    hence "pred[-(n * m + m + n)] \<noteq> 1"
      by (simp add: sym[OF uminusSucc])
    with na pos show ?thesis by simp
  next
    case (neg m) 
    with na show ?thesis by (auto simp: zero_is_add_nat)
  qed
qed

lemma one_is_times_iff [simp]:
  assumes a: "a \<in> Int" and b: "b \<in> Int"
  shows "(1 = a * b) = ((a = 1 \<and> b = 1) \<or> (a = -1 \<and> b = -1))"
  using assms by (auto dest: sym)

text \<open> Cancellation rules \<close>

lemma times_cancel1 [simp]:
  assumes a: "a \<in> Int" and b: "b \<in> Int" and c: "c \<in> Int"
  shows "(a * b = a * c) = (b = c \<or> (a = 0))"
proof -
  {
    assume "a \<noteq> 0" "a*b = a*c"
    from b c \<open>a*b = a*c\<close> have "b = c"
    proof (induct arbitrary: c)
      case 0
      with a \<open>a \<noteq> 0\<close> show ?case by simp
    next
      fix n c
      assume n: "n \<in> Nat" and c: "c \<in> Int" and eq: "a * succ[n] = a * c"
         and ih: "\<And>d. \<lbrakk>d \<in> Int; a*n = a *d\<rbrakk> \<Longrightarrow> n = d"
      from a n have "a * n = (a * succ[n]) - a" by simp
      also have "\<dots> = a*c - a" using eq by simp
      finally have "a * n = a * pred[c]" using a c by simp
      with c ih have "n = pred[c]" by blast
      with n c show "succ[n] = c" by simp
    next
      fix n c
      assume n: "n \<in> Nat" and c: "c \<in> Int" and eq: "a * -succ[n] = a * c"
         and ih: "\<And>d. \<lbrakk>d \<in> Int; a*(-n) = a *d\<rbrakk> \<Longrightarrow> -n = d"
      from a n have "a * (-n) = (a * -succ[n]) + a" by simp
      also have "\<dots> = a * c + a" using eq by simp
      finally have "a * (-n) = a * succ[c]" using a c by simp
      with c ih have "-n = succ[c]" by blast
      with n c show "-succ[n] = c" by (simp add: uminusSucc)
    qed
  }
  with assms show ?thesis by auto
qed

lemma times_cancel2 [simp]:
  assumes "a \<in> Int" and "b \<in> Int" and "c \<in> Int"
  shows "(a * c = b * c) = (a = b \<or> c = 0)"
proof -
  from assms have "a*c = c*a" "b*c = c*b" 
    by (simp add: times_commute)+
  with assms show ?thesis
    by simp
qed

lemma mult_eq_self1 [simp]:
  assumes a: "a \<in> Int" and b: "b \<in> Int"
  shows "(a * b = a) = (b = 1 \<or> a = 0)" (is "?lhs = ?rhs")
proof -
  from assms have "?lhs = (a*b = a*1)" by simp
  also from assms have "\<dots> = ?rhs" by (intro times_cancel1) simp+
  finally show ?thesis .
qed

lemma mult_eq_self2 [simp]:
  assumes a: "a \<in> Int" and b: "b \<in> Int"
  shows "(b * a = a) = (b = 1 \<or> a = 0)"
  using assms by (simp add: times_commute)


subsection \<open>Order on integer numbers\<close>

text \<open>
  We define the standard order @{text "\<le>"} on integers using a conditional
  definition, and we define the constant @{text "<"} such that @{text "a<b"}
  iff @{text "a\<le>b \<and> a\<noteq>b"}, for any values.
\<close>

definition leq  :: "[c,c] \<Rightarrow> c"         (infixl "\<le>" 50)
where int_leq_def: "\<lbrakk>a \<in> Int; b \<in> Int\<rbrakk> \<Longrightarrow> a \<le> b \<equiv> b - a \<in> Nat"

abbreviation (input)
  geq  :: "[c,c] \<Rightarrow> c"         (infixl "\<ge>" 50)
where "x \<ge> y  \<equiv>  y \<le> x"

notation (ASCII)
  leq   (infixl "<=" 50)  and
  geq   (infixl ">=" 50)

lemma boolify_leq [simp]: "\<lbrakk>a \<in> Int; b \<in> Int\<rbrakk> \<Longrightarrow> boolify(a \<le> b) = (a \<le> b)"
by (simp add: int_leq_def)

lemma leq_isBool [intro!,simp]: "\<lbrakk>a \<in> Int; b \<in> Int\<rbrakk> \<Longrightarrow> isBool(a \<le> b)"
by (simp add: int_leq_def)

lemma eq_leq_trans [trans]: "\<lbrakk>m = n; n \<le> p\<rbrakk> \<Longrightarrow> m \<le> p"
by (rule ssubst)

lemma leq_eq_trans [trans]: "\<lbrakk>m \<le> n; n = p\<rbrakk> \<Longrightarrow> m \<le> p"
by (rule subst)

subsection \<open> Operator definitions and generic facts about @{text "<"} \<close>

definition less :: "[c,c] \<Rightarrow> c"       (infixl "<" 50)
where "a < b  \<equiv>  a \<le> b \<and> a \<noteq> b"

abbreviation (input)
  greater :: "[c,c] \<Rightarrow> c"         (infixl ">" 50)
where "x > y  \<equiv>  y < x"

lemma boolify_less [simp]: "boolify(a < b) = (a < b)"
by (simp add: less_def)

lemma less_isBool [intro!,simp]: "isBool(a<b)"
by (simp add: less_def)

lemma eq_less_trans [trans]: "\<lbrakk>m = n; n < p\<rbrakk> \<Longrightarrow> m < p"
by (rule ssubst)

lemma less_eq_trans [trans]: "\<lbrakk>m < n; n = p\<rbrakk> \<Longrightarrow> m < p"
by (rule subst)

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

subsection \<open> Facts about @{text "\<le>"} over @{text Int} \<close>

lemma int_leq_refl [intro,simp]: "a \<in> Int \<Longrightarrow> a \<le> a"
  by (simp add: int_leq_def)

lemma int_leq_antisym [elim]:
  assumes ab: "a \<le> b" and ba: "b \<le> a" and a: "a \<in> Int" and b: "b \<in> Int" 
  shows "a = b"
proof -
  from a b ab have "b - a \<in> Nat"
    by (simp add: int_leq_def)
  moreover
  from a b ba have "-(b - a) \<in> Nat"
    by (simp add: int_leq_def add_commute)
  ultimately have "b - a = 0"
    by simp
  with a b show ?thesis 
    by simp
qed

declare int_leq_antisym[THEN sym, elim]

lemma int_leq_trans [trans]:
  assumes "a \<le> b" and "b \<le> c" 
      and a: "a \<in> Int" and b: "b \<in> Int" and c: "c \<in> Int"
    shows "a \<le> c"
proof -
  from a b c have "c - a = (c - b) + (b - a)"
    by (simp add: add_assoc)
  with assms show ?thesis
    by (simp add: int_leq_def)
qed

lemma eq_leq_bothE:   \<comment> \<open>reduce equality over integers to double inequality\<close>
  assumes "a \<in> Int" and "b \<in> Int" and "a = b" and "\<lbrakk> a \<le> b; b \<le> a \<rbrakk> \<Longrightarrow> P"
  shows "P"
  using assms by simp

lemma int_leq_linear: 
  assumes "a \<in> Int" and "b \<in> Int"
  shows "a \<le> b \<or> b \<le> a"
proof -
  from assms have "b - a \<in> Int" by simp
  hence "b - a \<in> Nat \<or> -(b - a) \<in> Nat" by (auto elim: intElim)
  with assms show ?thesis by (simp add: int_leq_def add_commute)
qed

lemma int_leq_uminus [simp]:
  assumes "a \<in> Int" and "b \<in> Int"
  shows "(-a \<le> -b) = (b \<le> a)"
  using assms by (simp add: int_leq_def add_commute)

lemma uminus_leq_zero [simp]:
  "a \<in> Int \<Longrightarrow> (-a \<le> 0) = (0 \<le> a)"
  "a \<in> Int \<Longrightarrow> (0 \<le> -a) = (a \<le> 0)"
  by (simp add: int_leq_def)+

lemma int_leq_succ [iff]:
  "a \<in> Int \<Longrightarrow> a \<le> succ[a]"
  by (simp add: int_leq_def)

lemma int_pred_leq [iff]:
  "a \<in> Int \<Longrightarrow> pred[a] \<le> a"
  by (simp add: int_leq_def)

lemma int_leq_iff_zero_leq_diff:
  (* loops, not suitable as a rewrite rule *)
  assumes "a \<in> Int" and "b \<in> Int"
  shows "(a \<le> b) = (0 \<le> b-a)"
  using assms by (simp add: int_leq_def)

lemma int_leqI:
  "\<lbrakk>a \<in> Int; b \<in> Int; 0 \<le> b-a\<rbrakk> \<Longrightarrow> a \<le> b"
  by (simp add: int_leq_def)

lemma int_leqE:
  "\<lbrakk>a \<le> b; a \<in> Int; b \<in> Int; 0 \<le> b-a \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (simp add: int_leq_def)

text \<open>
  From now on, we reduce the set @{text "Nat"} to the set of
  non-negative integers.
\<close>
lemma nat_iff_int_geq0 [simp]: "n \<in> Nat = (n \<in> Int \<and> 0 \<le> n)"
  by (auto simp: int_leq_def)

declare natIsInt [simp del]
declare succInNat [simp del]
declare predInNat [simp del]

lemma succ_geq_0 [simp]:
  assumes "a \<in> Int"
  shows "(0 \<le> succ[a]) = (0 \<le> a \<or> a = -1)"
  using assms succInNat[OF assms] by auto

lemma pred_geq_0 [simp]:
  assumes "a \<in> Int"
  shows "(0 \<le> pred[a]) = (0 \<le> a \<and> a \<noteq> 0)"
  using assms predInNat[OF assms] by auto

lemma succ_leq_0 [simp]:
  assumes "a \<in> Int"
  shows "(succ[a] \<le> 0) = (a \<le> 0 \<and> a \<noteq> 0)"
proof -
  from assms have "(succ[a] \<le> 0) = (-0 \<le> -succ[a])"
    by (intro sym[OF int_leq_uminus]) simp+
  with assms show ?thesis by (simp add: uminusSucc)
qed

lemma pred_leq_0 [simp]:
  assumes "a \<in> Int"
  shows "(pred[a] \<le> 0) = (a \<le> 0 \<or> a = 1)"
proof -
  from assms have "(pred[a] \<le> 0) = (-0 \<le> -pred[a])"
    by (intro sym[OF int_leq_uminus]) simp+
  with assms show ?thesis by (simp add: uminusPred)
qed

lemma nat_zero_leq: "n \<in> Nat \<Longrightarrow> 0 \<le> n"
  by simp

lemma nat_leq_zero [simp]:
  "\<lbrakk>n \<in> Int; 0 \<le> n\<rbrakk> \<Longrightarrow> (n \<le> 0) = (n = 0)"
  by auto

lemma uminus_leq_nat:
  assumes "m \<in> Int" and "0 \<le> m" and "n \<in> Int" and "0 \<le> n"
  shows "-m \<le> n"
  using assms by (simp add: int_leq_trans[of "-m" "0" "n"])

lemma int_succ_leq_succ [simp]:
  "\<lbrakk>a \<in> Int; b \<in> Int\<rbrakk> \<Longrightarrow> (succ[a] \<le> succ[b]) = (a \<le> b)"
  using int_leq_iff_zero_leq_diff[of "a" "b"] 
        int_leq_iff_zero_leq_diff[of "succ[a]" "succ[b]"]
  by simp

lemma int_succ_leq_succI [intro!]:
  "\<lbrakk>a \<in> Int; b \<in> Int; a \<le> b\<rbrakk> \<Longrightarrow> succ[a] \<le> succ[b]"
  by simp

lemma int_succ_leq_succE [elim!]:
  "\<lbrakk>succ[a] \<le> succ[b]; a \<in> Int; b \<in> Int; a \<le> b \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by simp

lemma int_pred_leq_pred [simp]:
  "\<lbrakk>a \<in> Int; b \<in> Int\<rbrakk> \<Longrightarrow> (pred[a] \<le> pred[b]) = (a \<le> b)"
  using int_leq_iff_zero_leq_diff[of "a" "b"] 
        int_leq_iff_zero_leq_diff[of "pred[a]" "pred[b]"]
  by simp

lemma int_pred_leq_predI [intro!]:
  "\<lbrakk>a \<in> Int; b \<in> Int; a \<le> b\<rbrakk> \<Longrightarrow> pred[a] \<le> pred[b]"
  by simp

lemma int_succ_leq_predE [elim!]:
  "\<lbrakk>pred[a] \<le> pred[b]; a \<in> Int; b \<in> Int; a \<le> b \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by simp

lemma int_leq_succI [intro]:
  "\<lbrakk>a \<le> b; a \<in> Int; b \<in> Int\<rbrakk> \<Longrightarrow> a \<le> succ[b]"
  using int_leq_iff_zero_leq_diff[of "a" "b"] 
        int_leq_iff_zero_leq_diff[of "a" "succ[b]"]
  by simp

lemma int_pred_leqI [intro]:
  "\<lbrakk>a \<le> b; a \<in> Int; b \<in> Int\<rbrakk> \<Longrightarrow> pred[a] \<le> b"
  using int_leq_iff_zero_leq_diff[of "a" "b"] 
        int_leq_iff_zero_leq_diff[of "pred[a]" "b"]
  by simp

lemma int_pred_leq_is_leq_succ [simp]:
  assumes "a \<in> Int" and "b \<in> Int"
  shows "(pred[a] \<le> b) = (a \<le> succ[b])"
proof -
  from assms have "(pred[a] \<le> b) = (succ[pred[a]] \<le> succ[b])"
    by (intro sym[OF int_succ_leq_succ]) simp+
  with assms show ?thesis by simp
qed

lemma int_leq_pred_is_succ_leq [simp]:
  assumes "a \<in> Int" and "b \<in> Int"
  shows "(a \<le> pred[b]) = (succ[a] \<le> b)"
proof -
  from assms have "(a \<le> pred[b]) = (succ[a] \<le> succ[pred[b]])"
    by (intro sym[OF int_succ_leq_succ]) simp+
  with assms show ?thesis by simp
qed

lemma int_leq_succ_iff [simp]:
  assumes a: "a \<in> Int" and b: "b \<in> Int"
  shows "(a \<le> succ[b]) = (a \<le> b \<or> a = succ[b])"
proof -
  {
    assume "b - a = -1"
    with assms have "b = -1 + a" 
      by (simp add: add_left_diff_right)
    with assms have "a = succ[b]"
      by simp
  }
  with assms int_leq_iff_zero_leq_diff[of "a" "b"] 
       int_leq_iff_zero_leq_diff[of "a" "succ[b]"]
  show ?thesis by auto
qed

lemma int_pred_leq_iff:
  assumes a: "a \<in> Int" and b: "b \<in> Int"
  shows "(pred[a] \<le> b) = (a \<le> b \<or> a = succ[b])"
  using assms by simp

lemma int_leq_succE [elim!]:
  assumes "a \<le> succ[b]" and "a \<in> Int" and "b \<in> Int"
      and "a \<le> b \<Longrightarrow> P" and "a = succ[b] \<Longrightarrow> P"
  shows "P"
  using assms by auto

lemma int_pred_leqE [elim!]:
  assumes "pred[a] \<le> b" and "a \<in> Int" and "b \<in> Int"
      and "a \<le> b \<Longrightarrow> P" and "a = succ[b] \<Longrightarrow> P"
  shows "P"
  using assms by auto

lemma int_succ_leq_iff [simp]:
  assumes "a \<in> Int" and "b \<in> Int"
  shows "(succ[a] \<le> b) = (a < b)"
proof -
  {
    assume "succ[a] \<le> b"
    with assms have "a \<le> b"
      by (simp add: int_leq_trans[of "a" "succ[a]" "b"])
    moreover
    have "a \<noteq> b"
    proof
      assume "a = b"
      with assms int_leq_succ[of "a"] \<open>succ[a] \<le> b\<close> have "succ[a] = a"
        by (intro int_leq_antisym) simp+
      with assms show "FALSE" 
        by simp
    qed
    ultimately have "a < b"
      by (simp add: less_def)
  }
  moreover
  {
    assume "a < b" 
    have "succ[a] \<le> b"
    proof (rule int_leqI)
      from assms have "b - a \<in> Int" by simp
      thus "0 \<le> b - succ[a]"
      proof (cases)
        case 0
        with assms \<open>a < b\<close> show ?thesis 
          by (simp add: less_def)
      next
        case (pos n)
        with assms show ?thesis 
          by simp
      next
        case (neg n)
        with assms \<open>a < b\<close> show ?thesis
          by (simp add: less_def int_leq_iff_zero_leq_diff[of "a" "b"])
      qed
    qed (simp add: assms)+
  }
  ultimately show ?thesis 
    using assms by (intro boolEqual) auto
qed

lemma int_leq_pred_iff [simp]:
  assumes "a \<in> Int" and "b \<in> Int"
  shows "(a \<le> pred[b]) = (a < b)"
  using assms by simp

lemma int_leq_uminus_succ_iff [simp]:
  assumes "a \<in> Int" and "b \<in> Int"
  shows "(a \<le> -succ[b]) = (a < -b)"
  using assms by (simp add: uminusSucc)

lemma int_uminus_pred_leq_iff [simp]:
  assumes "a \<in> Int" and "b \<in> Int"
  shows "(-pred[a] \<le> b) = (-a < b)"
  using assms by (simp add: uminusPred)

lemma int_succ_leqI [intro]:
  assumes "a \<in> Int" and "b \<in> Int" and "a < b"
  shows "succ[a] \<le> b"
  using assms by simp

lemma int_succ_leqE [elim!]:
  assumes "succ[a] \<le> b" and "a \<in> Int" and "b \<in> Int"
      and "\<lbrakk>a < b\<rbrakk> \<Longrightarrow> P"
  shows "P"
  using assms by simp

lemma int_leq_predI [intro]:
  assumes "a \<in> Int" and "b \<in> Int" and "a < b"
  shows "a \<le> pred[b]"
  using assms by simp

lemma int_leq_predE [elim!]:
  assumes "a \<le> pred[b]" and "a \<in> Int" and "b \<in> Int"
      and "a < b \<Longrightarrow> P"
  shows "P"
  using assms by simp

lemma int_not_succ_leq [simp]:
  "a \<in> Int \<Longrightarrow> (succ[a] \<le> a) = FALSE"
  by auto

lemma int_not_leq_pred [simp]:
  "a \<in> Int \<Longrightarrow> (a \<le> pred[a]) = FALSE"
  by auto

lemma int_leq_limit_1:
  assumes "a \<le> b" and "\<not>(succ[a] \<le> b)" and "a \<in> Int" and "b \<in> Int"
  shows "a=b"
  using assms by (auto simp: less_def)

lemma int_leq_limit_2:
  assumes "a \<le> b" and "\<not>(a \<le> pred[b])" and "a \<in> Int" and "b \<in> Int"
  shows "a=b"
  using assms by (auto elim: int_leq_limit_1)

text \<open>
  Case distinction and induction rules involving @{text "\<le>"}.
\<close>

lemma int_leq_cases:
  assumes a: "a \<in> Int" and b: "b \<in> Int"
      and "a \<le> b \<Longrightarrow> P" and "\<lbrakk>b \<le> a; b \<noteq> a\<rbrakk> \<Longrightarrow> P"
    shows "P"
  using assms int_leq_linear[OF a b] by auto

lemma nat_leq_induct:  \<comment> \<open>sometimes called ``complete induction''\<close>
  assumes base: "P(0)"
  and step: "\<forall>n\<in>Nat : (\<forall>m\<in>Nat : m \<le> n \<Rightarrow> P(m)) \<Rightarrow> P(succ[n])"
  shows "\<forall>n\<in>Nat : P(n)"
proof -
  have "\<forall>n\<in>Nat : \<forall>m\<in>Nat : m \<le> n \<Rightarrow> P(m)"
  proof (rule natInduct)
    from base show "\<forall>m \<in> Nat : m \<le> 0 \<Rightarrow> P(m)" by auto
  next
    fix n
    assume "n \<in> Nat" "\<forall>m \<in> Nat : m \<le> n \<Rightarrow> P(m)"
    with step show "\<forall>m \<in> Nat : m \<le> succ[n] \<Rightarrow> P(m)" 
      by (auto simp del: nat_iff_int_geq0)
  qed
  thus ?thesis by auto
qed

lemma nat_leq_inductE:
  assumes "n \<in> Nat"
  and "P(0)" and "\<And>n. \<lbrakk>n \<in> Nat; \<forall>m\<in>Nat : m \<le> n \<Rightarrow> P(m)\<rbrakk> \<Longrightarrow> P(succ[n])"
  shows "P(n)"
  using assms by (blast dest: nat_leq_induct)

lemma int_leq_induct:  \<comment> \<open>analogous induction principle for the integers\<close>
  assumes base: "P(0)"
  and step: "\<forall>n\<in>Nat : (\<forall>i\<in>Int : -n \<le> i \<and> i \<le> n \<Rightarrow> P(i)) \<Rightarrow> P(succ[n]) \<and> P(-succ[n])"
  shows "\<forall>a\<in>Int : P(a)"
proof -
  have "\<forall>n\<in>Nat : \<forall>a\<in>Int : -n \<le> a \<and> a \<le> n \<Rightarrow> P(a)"
  proof (rule natInduct)
    from base show "\<forall>a \<in> Int : -0 \<le> a \<and> a \<le> 0 \<Rightarrow> P(a)"
      by (auto dest: int_leq_antisym)
  next
    fix n
    assume n: "n \<in> Nat" and ih: "\<forall>a \<in> Int : -n \<le> a \<and> a \<le> n \<Rightarrow> P(a)"
    show "\<forall>a \<in> Int : -succ[n] \<le> a \<and> a \<le> succ[n] \<Rightarrow> P(a)"
    proof (clarify)
      fix a
      assume m: "a \<in> Int" "-succ[n] \<le> a" "a \<le> succ[n]"
      from n ih step have "P(succ[n]) \<and> P(-succ[n])" by blast
      moreover {
        assume "-n \<le> a" "a \<le> n"
        with ih \<open>a \<in> Int\<close> have "P(a)" by blast
      }
      ultimately show "P(a)"
        using n m by (auto simp: uminusSucc)
    qed
  qed
  moreover
  {
    fix n
    assume "n \<in> Nat"
    hence "-n \<in> Int \<and> n \<in> Int \<and> -n \<le> -n \<and> -n \<le> n \<and> n \<le> n"
      by (simp add: int_leq_trans[of "-n" "0" "n"])
  }
  ultimately have "\<forall>n \<in> Nat : P(n) \<and> P(-n)" by blast
  thus ?thesis by (blast elim: intElim)
qed

lemma int_leq_inductE:
  assumes "a \<in> Int"
  and "P(0)" 
  and "\<And>n. \<lbrakk>n \<in> Nat; \<forall>i\<in>Int : -n \<le> i \<and> i \<le> n \<Rightarrow> P(i)\<rbrakk> \<Longrightarrow> P(succ[n])"
  and "\<And>n. \<lbrakk>n \<in> Nat; \<forall>i\<in>Int : -n \<le> i \<and> i \<le> n \<Rightarrow> P(i)\<rbrakk> \<Longrightarrow> P(-succ[n])"
  shows "P(a)"
  using assms by (blast dest: int_leq_induct)


subsection \<open> Facts about @{text "<"} over @{text Int} \<close>

text \<open> Reduce @{text "\<le>"} to @{text "<"}. \<close>

lemma int_leq_less:
  assumes "a \<in> Int" and "b \<in> Int"
  shows "a \<le> b = (a < b \<or> a = b)"
  using assms by (auto simp: less_def)

lemma int_leq_lessE:
  assumes "a \<le> b" and "a \<in> Int" and "b \<in> Int"
      and "a < b \<Longrightarrow> P" and "a=b \<Longrightarrow> P"
    shows "P"
  using assms by (auto simp: int_leq_less)

lemma int_less_iff_zero_less_diff:
  assumes "a \<in> Int" and "b \<in> Int"
  shows "(a < b) = (0 < b-a)"
  using assms unfolding less_def 
  by (auto simp: int_leq_iff_zero_leq_diff[of "a" "b"])

lemma int_lessI:
  "\<lbrakk>a \<in> Int; b \<in> Int; 0 < b-a\<rbrakk> \<Longrightarrow> a < b"
  by (simp add: int_less_iff_zero_less_diff[of "a" "b"])

lemma int_lessE:
  "\<lbrakk>a < b; a \<in> Int; b \<in> Int; 0 < b-a \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (simp add: int_less_iff_zero_less_diff[of "a" "b"])

lemma int_leq_not_less:
  assumes "a \<in> Int" and "b \<in> Int" and "a \<le> b"
  shows "(b < a) = FALSE"
  using assms by (auto simp: less_def dest: int_leq_antisym)

lemma int_less_not_leq:
  assumes "a \<in> Int" and "b \<in> Int" and "a < b"
  shows "(b \<le> a) = FALSE"
  using assms by (auto simp: less_def dest: int_leq_antisym)

text \<open>
  Declaring the above lemmas as simplification rules makes the prover
  very slow, but the instances where @{text "a"} is @{text "0"} are useful.
\<close>
lemmas zero_leq_not_less_zero [simp] = int_leq_not_less[of 0, simplified]
lemmas zero_less_not_leq_zero [simp] = int_less_not_leq[of 0, simplified]

lemma int_less_succ [simp]:
  assumes "a \<in> Int" and "b \<in> Int"
  shows "(a < succ[b]) = (a \<le> b)"
  using assms by (auto simp: less_def int_leq_succI)

lemmas int_leq_is_less_succ = sym[OF int_less_succ]

lemma int_less_succE:
  assumes "a < succ[b]" and "a \<in> Int" and "b \<in> Int"
      and "a < b \<Longrightarrow> P" and "a = b \<Longrightarrow> P"
  shows P
  using assms by (auto elim: int_leq_lessE)

lemma int_pred_less [simp]:
  assumes "a \<in> Int" and "b \<in> Int"
  shows "(pred[a] < b) = (a \<le> b)"
  using assms by (auto simp: less_def)

lemmas int_leq_is_pred_less = sym[OF int_pred_less]

lemma not_leq_less [simp]:
  assumes "a \<in> Int" and "b \<in> Int"
  shows "((a \<le> b) = FALSE) = (b < a)"
  using assms int_leq_linear[of a b]
  by (auto simp: less_def dest: int_leq_antisym)

lemma not_less_leq [simp]:
  assumes "a \<in> Int" and "b \<in> Int"
  shows "((a < b) = FALSE) = (b \<le> a)"
  using assms int_leq_linear[of a b] 
  by (auto simp: less_def dest: int_leq_antisym)

lemma int_less_uminus [simp]:
  assumes "a \<in> Int" and "b \<in> Int"
  shows "(-a < -b) = (b < a)"
  using assms by (auto simp: less_def)

lemma int_uminus_zero [simp]:
  "a \<in> Int \<Longrightarrow> (-a < 0) = (0 < a)"
  "a \<in> Int \<Longrightarrow> (0 < -a) = (a < 0)"
  by (auto simp: less_def)

text \<open> @{text "<"} and @{text "succ / pred"}. \<close>

lemma int_succ_less_succ [simp]: 
  "\<lbrakk>a \<in> Int; b \<in> Int\<rbrakk> \<Longrightarrow> (succ[a] < succ[b]) = (a < b)"
  by (auto simp: less_def int_leq_succI)

lemma int_succ_less_succI [intro]:
  "\<lbrakk>a \<in> Int; b \<in> Int; a < b\<rbrakk> \<Longrightarrow> succ[a] < succ[b]"
  by simp

lemma int_succ_less_succE [elim]:
  assumes "succ[a] < succ[b]" and "a \<in> Int" and "b \<in> Int" and "a < b \<Longrightarrow> P"
  shows "P"
  using assms by simp

lemma int_pred_less_pred [simp]: 
  "\<lbrakk>a \<in> Int; b \<in> Int\<rbrakk> \<Longrightarrow> (pred[a] < pred[b]) = (a < b)"
  by (simp add: less_def)

lemma int_pred_less_predI [intro]:
  "\<lbrakk>a \<in> Int; b \<in> Int; a < b\<rbrakk> \<Longrightarrow> pred[a] < pred[b]"
  by simp

lemma int_pred_less_predE [elim]:
  assumes "pred[a] < pred[b]" and "a \<in> Int" and "b \<in> Int" and "a < b \<Longrightarrow> P"
  shows "P"
  using assms by simp

lemma int_less_succ_same [iff]:
  "a \<in> Int \<Longrightarrow> a < succ[a]"
  by (simp add: less_def)

lemma int_pred_less_same [iff]:
  "a \<in> Int \<Longrightarrow> pred[a] < a"
  by (simp add: less_def)

lemma int_pred_less_is_less_succ [simp]:
  assumes "a \<in> Int" and "b \<in> Int"
  shows "(pred[a] < b) = (a < succ[b])"
  using assms by (auto simp: less_def)

lemma int_less_pred_is_succ_less [simp]:
  assumes "a \<in> Int" and "b \<in> Int"
  shows "(a < pred[b]) = (succ[a] < b)"
  using assms by (auto simp: less_def)

lemma succ_nat_not_neg [simp]:
  "\<lbrakk>n \<in> Int; 0 \<le> n\<rbrakk> \<Longrightarrow> (succ[n] < 0) = FALSE"
  by (auto simp: less_def)

lemma int_less_leq_not_leq:
  assumes "a \<in> Int" and "b \<in> Int"
  shows "(a < b) = (a \<le> b \<and> \<not> b \<le> a)"
  using assms by (auto simp: less_def dest: int_leq_antisym)

text \<open> Transitivity. \<close>

lemma int_less_trans [trans]:
  assumes "a < b" and "b < c" and "a \<in> Int" and "b \<in> Int" and "c \<in> Int"
  shows "a < c"
  using assms unfolding less_def
  by (auto elim!: int_leq_trans dest: int_leq_antisym)

lemma nat_less_trans_Succ:  \<comment> \<open>stronger than the above\<close>
  assumes lt1: "a < b" and lt2: "b < c"
      and a: "a \<in> Int" and b: "b \<in> Int" and c: "c \<in> Int"
  shows "succ[a] < c"
  using assms
proof -
  from a b lt1 have "succ[succ[a]] \<le> succ[b]" 
    by (auto simp: less_def int_leq_succI)
  also from b c lt2 have "\<dots> \<le> c" 
    by (auto simp: less_def)
  finally show ?thesis 
    using a b c by (auto simp: less_def)
qed

lemma int_leq_less_trans [trans]:
  assumes "a \<le> b" and "b < c" and "a \<in> Int" and "b \<in> Int" and "c \<in> Int"
  shows "a < c"
  using assms unfolding less_def
  by (auto elim!: int_leq_trans dest: int_leq_antisym)

lemma int_less_leq_trans [trans]:
  assumes "a < b" and "b \<le> c" and "a \<in> Int" and "b \<in> Int" and "c \<in> Int"
  shows "a < c"
  using assms unfolding less_def
  by (auto elim!: int_leq_trans dest: int_leq_antisym)

lemma nat_zero_less_succ [iff]:
  "\<lbrakk>n \<in> Int; 0 \<le> n\<rbrakk> \<Longrightarrow> 0 < succ[n]"
  by (simp add: int_leq_less_trans)

text \<open> Asymmetry. \<close>

lemma int_less_not_sym:
  assumes "a < b" and "a \<in> Int" and "b \<in> Int"
  shows "(b < a) = FALSE"
  using assms by (auto simp: less_def dest: int_leq_antisym)

lemma int_less_asym:
  assumes 1: "a < b" and 2: "a \<in> Int" and 3: "b \<in> Int" and 4: "\<not>P \<Longrightarrow> b < a"
  shows "P"
  using int_less_not_sym[OF 1 2 3] 4 by auto

text \<open> Linearity (totality). \<close>

lemma int_less_linear:
  assumes a: "a \<in> Int" and b: "b \<in> Int"
  shows "a < b \<or> a = b \<or> b < a"
  unfolding less_def using int_leq_linear[OF a b] by blast

lemma int_leq_less_linear:
  assumes a: "a \<in> Int" and b: "b \<in> Int"
  shows "a \<le> b \<or> b < a"
  using assms int_less_linear[OF a b] by (auto simp: less_def)

lemma int_less_cases [case_names less equal greater]:
  assumes a: "a \<in> Int" and b: "b \<in> Int"
  shows "(a < b \<Longrightarrow> P) \<Longrightarrow> (a = b \<Longrightarrow> P) \<Longrightarrow> (b < a \<Longrightarrow> P) \<Longrightarrow> P"
  using int_less_linear[OF a b] by blast

lemma int_neq_iff:
  assumes a: "a \<in> Int" and b: "b \<in> Int"
  shows "((a = b) = FALSE) = (a < b \<or> b < a)"
  using assms int_less_linear[OF a b] by auto

lemma int_neq_lessE:
  assumes "a \<noteq> b" and "a \<in> Int" and "b \<in> Int"
  shows "(a < b \<Longrightarrow> P) \<Longrightarrow> (b < a \<Longrightarrow> P) \<Longrightarrow> P"
  using assms by (auto simp: int_neq_iff)

lemma int_antisym_conv1:
  assumes "\<not> a < b" and "a \<in> Int" and "b \<in> Int"
  shows "(a \<le> b) = (a = b)"
  using assms by (auto dest: int_leq_antisym)

lemma int_antisym_conv2:
  assumes "a \<le> b" and "a \<in> Int" and "b \<in> Int"
  shows "(\<not> a < b) = (b = a)"
  using assms by (auto dest: int_leq_antisym)

lemma int_antisym_conv3:
  assumes "\<not> a < b" and "a \<in> Int" and "b \<in> Int"
  shows "(\<not> b < a) = (a = b)"
  using assms by (auto dest: int_leq_antisym)

lemma nat_gt0_not0:
  assumes "n \<in> Int" and "0 \<le> n"
  shows "(0 < n) = (n \<noteq> 0)"
  using assms by auto

lemmas nat_neq0_conv = sym[OF nat_gt0_not0, simplified, simp]

lemma nat_less_one (*[simp]*):
  assumes "n \<in> Int" and "0 \<le> n"
  shows "(n < 1) = (n = 0)"
  using assms by auto

text \<open> "Less than" is antisymmetric, sort of \<close>

lemma int_less_antisym:
  assumes "a \<in> Int" and "b \<in> Int"
  shows "\<lbrakk> \<not>(b < a); b < succ[a] \<rbrakk> \<Longrightarrow> a = b"
  using assms by (auto dest: int_leq_antisym)

text \<open> Lifting @{text "<"} monotonicity to @{text "\<le>"} monotonicity \<close>
lemma int_less_mono_imp_leq_mono:
  assumes ij: "i \<le> j" and i: "i \<in> Int" and j: "j \<in> Int"
      and f: "\<forall>a \<in> Int : f(a) \<in> Int"
      and mono: "\<And>i j. \<lbrakk>i \<in> Int; j \<in> Int; i<j\<rbrakk> \<Longrightarrow> f(i) < f(j)"
  shows "f(i) \<le> f(j)"
proof (rule int_leq_lessE[OF ij i j])
  assume "i < j"
  with i j have "f(i) < f(j)" by (rule mono)
  thus ?thesis by auto
next
  assume "i = j"
  with i f show ?thesis by auto
qed

lemma nat_less_mono_imp_leq_mono:
  assumes ij: "i \<le> j" and i: "i \<in> Nat" and j: "j \<in> Nat"
      and f: "\<forall>a \<in> Nat : f(a) \<in> Int"
      and mono: "\<And>i j. \<lbrakk>i \<in> Nat; j \<in> Nat; i<j\<rbrakk> \<Longrightarrow> f(i) < f(j)"
  shows "f(i) \<le> f(j)"
proof (rule int_leq_lessE[OF ij])
  assume "i < j"
  with i j have "f(i) < f(j)" by (rule mono)
  thus ?thesis by auto
next
  assume "i = j"
  with i f show ?thesis by (auto simp del: nat_iff_int_geq0)
qed (auto simp: i[simplified] j[simplified])

lemma int_succ_lessI:
  assumes "a \<in> Int" and "b \<in> Int" and "a < b" and "succ[a] \<noteq> b"
  shows "succ[a] < b"
  using assms by (auto simp: less_def)

lemma int_less_antisym_false: "\<lbrakk>a < b; a \<in> Int; b \<in> Int\<rbrakk> \<Longrightarrow> b < a = FALSE"
  by auto

lemma nat_less_antisym_leq_false: "\<lbrakk>a < b; a \<in> Int; b \<in> Int\<rbrakk> \<Longrightarrow> b \<le> a = FALSE"
  by auto


subsection \<open> Additional arithmetic theorems \<close>

subsubsection \<open> Monotonicity of Addition \<close>

lemma int_add_left_cancel_leq [simp]:
  assumes "i \<in> Int" and "j \<in> Int" and "k \<in> Int"
  shows "(i + j \<le> i + k) = (j \<le> k)"
  using assms by (induct i) (simp del: int_leq_succ_iff)+

lemma int_add_right_cancel_leq [simp]:
  assumes "i \<in> Int" and "j \<in> Int" and "k \<in> Int"
  shows "(j + i \<le> k + i) = (j \<le> k)"
  using assms by (induct i) (simp del: int_leq_succ_iff)+

lemma int_add_left_cancel_less [simp]:
  assumes "i \<in> Int" and "j \<in> Int" and "k \<in> Int"
  shows "(i + j < i + k) = (j < k)"
  using assms by (simp add: less_def)

lemma int_add_right_cancel_less [simp]:
  assumes "i \<in> Int" and "j \<in> Int" and "k \<in> Int"
  shows "(j + i < k + i) = (j < k)"
  using assms by (simp add: less_def)

lemma int_add_left_cancel_succ_leq [simp]:
  assumes "i \<in> Int" and "j \<in> Int" and "k \<in> Int"
  shows "(succ[i + j] \<le> i + k) = (succ[j] \<le> k)"
using assms proof (induct i)
  case (neg n) 
  then have "(-n + j \<le> pred[-n + k]) = (succ[-n+j] \<le> succ[pred[-n + k]])"
    by (intro sym[OF int_succ_leq_succ]) simp+
  with neg show ?case by simp
qed (simp del: int_leq_succ_iff)+

lemma int_add_right_cancel_succ_less [simp]:
  assumes "i \<in> Int" and "j \<in> Int" and "k \<in> Int"
  shows "(succ[j + i] \<le> k + i) = (succ[j] \<le> k)"
using assms proof (induct i)
  case (neg n)
  then have "(j - n \<le> pred[k - n]) = (succ[j-n] \<le> succ[pred[k-n]])"
    by (intro sym[OF int_succ_leq_succ]) simp+
  with neg show ?case by simp
qed (simp del: int_leq_succ_iff)+

lemma int_add_left_cancel_pred_leq [simp]:
  assumes "i \<in> Int" and "j \<in> Int" and "k \<in> Int"
  shows "(pred[i + j] \<le> i + k) = (pred[j] \<le> k)"
proof -
  from assms have "pred[i+j] = i + pred[j]" by simp
  hence "(pred[i + j] \<le> i + k) = (i + pred[j] \<le> i + k)" by simp
  also have "\<dots> = (pred[j] \<le> k)"
    using assms by (intro int_add_left_cancel_leq) simp+
  finally show ?thesis .
qed

lemma int_add_right_cancel_pred_less [simp]:
  assumes "i \<in> Int" and "j \<in> Int" and "k \<in> Int"
  shows "(pred[j + i] \<le> k + i) = (pred[j] \<le> k)"
proof -
  from assms have "pred[j+i] = pred[j] + i" by simp
  hence "(pred[j+i] \<le> k + i) = (pred[j] + i \<le> k + i)" by simp
  also have "\<dots> = (pred[j] \<le> k)"
    using assms by (intro int_add_right_cancel_leq) simp+
  finally show ?thesis .
qed

lemma int_leq_imp_add:
  assumes i: "i \<in> Int" and j: "j \<in> Int" and ij: "i \<le> j"
  shows "\<exists>k \<in> Nat : j = i+k"
proof -
  from assms have "j-i \<in> Nat"
    by (simp add: int_leq_iff_zero_leq_diff[of "i" "j"])
  moreover
  from i j have "j = i + (j-i)"
    by (simp add: add_ac)
  ultimately show ?thesis ..
qed

lemma int_less_imp_succ_add:
  assumes ij: "i < j" and i: "i \<in> Int" and j: "j \<in> Int"
  shows "\<exists>k \<in> Nat: j = succ[i + k]"
proof -
  from assms have "succ[i] \<le> j"
    by simp
  with i j have "j - succ[i] \<in> Nat"
    by (simp add: int_less_iff_zero_less_diff[of "i" "j"])
  moreover
  from i j have "j = succ[i + (j - succ[i])]"
    by (simp add: add_ac)
  ultimately show ?thesis ..
qed


subsubsection \<open> (Partially) Ordered Groups \<close>

\<comment> \<open> The two following lemmas are just ``one half'' of
     @{text int_add_left_cancel_leq} and @{text int_add_right_cancel_leq}
     proved above." \<close>
lemma add_leq_left_mono:
  assumes "a \<in> Int" and "b \<in> Int" and "c \<in> Int"
  shows "a \<le> b \<Longrightarrow> c + a \<le> c + b"
  using assms by simp

lemma add_leq_right_mono:
  assumes "a \<in> Int" and "b \<in> Int" and "c \<in> Int"
  shows "a \<le> b \<Longrightarrow> a + c \<le> b + c"
  using assms by simp

text \<open> non-strict, in both arguments \<close>
lemma add_leq_mono:
  assumes "a \<in> Int" and "b \<in> Int" and "c \<in> Int" and "d \<in> Int"
  shows "a \<le> b \<Longrightarrow> c \<le> d \<Longrightarrow> a + c \<le> b + d"
  using assms
    add_leq_right_mono[of a b c]
    add_leq_left_mono[of c d b]
    int_leq_trans[of "a + c" "b + c" "b + d"]
  by simp

\<comment> \<open> Similar for strict less than. \<close>
lemma add_less_left_mono:
  assumes "a \<in> Int" and "b \<in> Int" and "c \<in> Int"
  shows "a < b \<Longrightarrow> c + a < c + b"
  using assms by (simp add: add_leq_left_mono less_def)

lemma add_less_right_mono:
  assumes "a \<in> Int" and "b \<in> Int" and "c \<in> Int"
  shows "a < b \<Longrightarrow> a + c < b + c"
  using assms by (simp add: add_leq_right_mono less_def)

text \<open> Strict monotonicity in both arguments \<close>
lemma add_less_mono:
  assumes "a \<in> Int" and "b \<in> Int" and "c \<in> Int" and "d \<in> Int"
  shows "a < b \<Longrightarrow> c < d \<Longrightarrow> a + c < b + d"
  using assms
    add_less_right_mono[of a b c]
    add_less_left_mono[of c d b]
    int_less_trans[of "a + c" "b + c" "b + d"]
  by simp

lemma add_less_leq_mono:
  assumes "a \<in> Int" and "b \<in> Int" and "c \<in> Int" and "d \<in> Int"
  shows "a < b \<Longrightarrow> c \<le> d \<Longrightarrow> a + c < b + d"
  using assms
    add_less_right_mono[of a b c]
    add_leq_left_mono[of c d b]
    int_less_leq_trans[of "a + c" "b + c" "b + d"]
  by simp

lemma add_leq_diff1:
  assumes "a \<in> Int" and "b \<in> Int" and "c \<in> Int"
  shows "(a + b \<le> c) = (a \<le> c - b)"
proof -
  from assms have "(a + b \<le> c) = ((a + b) - b \<le> c - b)"
    by (intro sym[OF int_add_right_cancel_leq]) simp+
  with assms show ?thesis by simp
qed

lemma add_leq_diff2:
  assumes "a \<in> Int" and "b \<in> Int" and "c \<in> Int"
  shows "(a + b \<le> c) = (b \<le> c - a)"
proof -
  from assms have "(a + b \<le> c) = ((a + b) - a \<le> c - a)"
    by (intro sym[OF int_add_right_cancel_leq]) simp+
  with assms show ?thesis by simp
qed

lemma add_leq_less_mono:
  assumes "a \<in> Int" and "b \<in> Int" and "c \<in> Int" and "d \<in> Int"
  shows "a \<le> b \<Longrightarrow> c < d \<Longrightarrow> a + c < b + d"
  using assms
    add_leq_right_mono[of a b c]
    add_less_left_mono[of c d b]
    int_leq_less_trans[of "a + c" "b + c" "b + d"]
  by simp

lemma leq_add_nat1 [iff]:
  assumes "a \<in> Int" and "0 \<le> a" and "b \<in> Int"
  shows "b \<le> b + a"
  using assms add_leq_left_mono[of 0 a b] by simp

lemma leq_add_nat2 [iff]:
  assumes "a \<in> Int" and "0 \<le> a" and "b \<in> Int"
  shows "b \<le> a + b"
  using assms add_leq_right_mono [of 0 a b] by simp

lemma trans_leq_add_nat1 [simp] (* was [elim]*):
  assumes "a \<le> b" and "a \<in> Int" and "b \<in> Int" and "m \<in> Int" and "0 \<le> m"
  shows "a \<le> b+m"
  using assms by (simp add: int_leq_trans[of "a" "b" "b+m"])

lemma trans_leq_add_nat2 [simp] (* was [elim] *):
  assumes "a \<le> b" and "a \<in> Int" and "b \<in> Int" and "m \<in> Int" and "0 \<le> m"
  shows "a \<le> m+b"
  using assms by (simp add: int_leq_trans[of "a" "b" "m+b"])

lemma add_nat_leqD1 [elim]:
  assumes "a+k \<le> b" and "a \<in> Int" and "b \<in> Int" and "k \<in> Int" and "0 \<le> k"
  shows "a \<le> b"
  using assms by (simp add: int_leq_trans[of "a" "a+k" "b"])

lemma add_nat_leqD2 [elim]:
  assumes "k+a \<le> b" and "a \<in> Int" and "b \<in> Int" and "k \<in> Int" and "0 \<le> k"
  shows "a \<le> b"
  using assms by (simp add: int_leq_trans[of "a" "k+a" "b"])

lemma add_nat_pred_leqD1 [elim]:
  assumes "pred[a+k] \<le> b" and "a \<in> Int" and "b \<in> Int" and "k \<in> Int" and "0 \<le> k"
  shows "pred[a] \<le> b"
proof -
  {
    assume 1: "a + k = succ[b]"
    have "a \<le> succ[b]"
    proof (rule int_leqI)
      from assms 1 have "succ[b] - a = k"
        by (simp add: add_left_diff_right add_ac)
      with \<open>0 \<le> k\<close> show "0 \<le> succ[b] - a"
        by simp
    qed (simp add: assms)+
  }
  with assms show ?thesis 
    by (auto simp del: int_leq_succ_iff)
qed
  
lemma add_nat_pred_leqD2 [elim]:
  assumes "pred[k+a] \<le> b" and "a \<in> Int" and "b \<in> Int" and "k \<in> Int" and "0 \<le> k"
  shows "pred[a] \<le> b"
proof (rule add_nat_pred_leqD1)
  from assms show "pred[a+k] \<le> b"
    by (simp add: add_commute)
qed (simp add: assms)+

lemma less_succ_add_nat1 (*[simp]*):
  assumes "i \<in> Int" and "m \<in> Int" and "0 \<le> m"
  shows "i < succ[i + m]"
  using assms by simp

lemma less_add_Succ2 (*[simp]*):
  assumes "i \<in> Int" and "m \<in> Int" and "0 \<le> m"
  shows "i < succ[m + i]"
  using assms by simp

lemma diff_nat_leq_self1 [simp]:
  assumes "i \<in> Int" and "n \<in> Int" and "0 \<le> n"
  shows "i - n \<le> i"
proof -
  from assms have "i-n \<le> (i-n)+n"
    by (intro leq_add_nat1) simp+
  with assms show ?thesis by simp
qed

lemma diff_nat_leq_self2 [simp]:
  assumes "i \<in> Int" and "n \<in> Int" and "0 \<le> n"
  shows "-n + i \<le> i"
  using assms by (simp add: add_commute)

lemma trans_leq_diff_nat1 [simp]:
  assumes "i \<le> j" and "i \<in> Int" and "j \<in> Int" and "m \<in> Int" and "0 \<le> m"
  shows "i-m \<le> j"
  using assms by (simp add: int_leq_trans[of "i-m" "i" "j"])

lemma trans_leq_diff_nat2 [simp]:
  assumes "i \<le> j" and "i \<in> Int" and "j \<in> Int" and "m \<in> Int" and "0 \<le> m"
  shows "-m + i \<le> j"
  using assms by (simp add: int_leq_trans[of "-m + i" "i" "j"])

lemma int_leq_iff_add:
  assumes "i \<in> Int" and "j \<in> Int"
  shows "(i \<le> j) = (\<exists>k \<in> Nat: j = i + k)" (is "?lhs = ?rhs")
  using assms by (auto intro: int_leq_imp_add)

lemma int_less_iff_succ_add:
  assumes "i \<in> Int" and "j \<in> Int"
  shows "(i < j) = (\<exists>k \<in> Nat: j = succ[i + k])" (is "?lhs = ?rhs")
  using assms by (auto intro: int_less_imp_succ_add)

lemma leq_add_self1 [simp]:
  assumes "i \<in> Int" and "j \<in> Int"
  shows "(i + j \<le> i) = (j \<le> 0)"
proof -
  from assms have "(i+j \<le> i) = (i+j-i \<le> i-i)"
    by (intro sym[OF int_add_right_cancel_leq]) simp+
  with assms show ?thesis
    by simp
qed

lemma leq_add_self2 [simp]:
  assumes "i \<in> Int" and "j \<in> Int"
  shows "(j + i \<le> i) = (j \<le> 0)"
  using assms by (simp add: add_commute)

lemma trans_less_add_nat1 [simp]:
  assumes "i < j" and "i \<in> Int" and "j \<in> Int" and "m \<in> Int" and "0 \<le> m"
  shows "i < j + m"
  using assms by (simp add: int_less_leq_trans[of "i" "j" "j+m"])

lemma trans_less_add_nat2 [simp]:
  assumes "i < j" and "i \<in> Int" and "j \<in> Int" and "m \<in> Int" and "0 \<le> m"
  shows "i < m + j"
  using assms by (simp add: int_less_leq_trans[of "i" "j" "m+j"])

lemma trans_less_diff_nat1:
  assumes "i < j" and "i \<in> Int" and "j \<in> Int" and "m \<in> Int" and "0 \<le> m"
  shows "i - m < j"
  using assms by (simp add: int_leq_less_trans[of "i-m" "i" "j"])

lemma add_nat_lessD1:
  assumes "i+k < j" and "i \<in> Int" and "j \<in> Int" and "k \<in> Int" and "0 \<le> k"
  shows "i < j"
  using assms by (simp add: int_leq_less_trans[of "i" "i+k" "j"])

lemma add_lessD2:
  assumes "k+i < j" and "i \<in> Int" and "j \<in> Int" and "k \<in> Int" and "0 \<le> k"
  shows "i < j"
  using assms by (simp add: int_leq_less_trans[of "i" "k+i" "j"])

lemma nat_add_gt_0:
  assumes "m \<in> Int" and "0 \<le> m" and "n \<in> Int" and "0 \<le> n"
  shows "(m + n > 0) = (m > 0 \<or> n > 0)"
  using assms by auto

lemma add_ge_1:
  assumes "m \<in> Int" and "0 \<le> m" and "n \<in> Int" and "0 \<le> n"
  shows "(m + n \<ge> 1) = (m \<ge> 1 \<or> n \<ge> 1)"
  using assms by auto

lemma less_imp_add_positive:
  assumes "i < j" and "i \<in> Int" and "j \<in> Int"
  shows "\<exists>k \<in> Nat: 0 < k \<and> i + k = j"
proof -
  from assms obtain k where k: "k \<in> Nat" "i + succ[k] = j"
    by (auto dest: int_less_imp_succ_add)
  from k have "0 < succ[k]" "succ[k] \<in> Nat" by simp+
  with assms k show ?thesis by blast
qed


subsubsection \<open> Monotonicity of Multiplication \<close>

lemma times_leq_left_pos_mono:
  assumes 1: "a \<le> b" and a: "a \<in> Int" and b: "b \<in> Int" and c: "c \<in> Nat"
  shows "c * a \<le> c * b"
  using c by induct (simp add: add_leq_mono 1 a b)+

lemma times_leq_left_neg_mono:
  assumes 1: "a \<le> b" and a: "a \<in> Int" and b: "b \<in> Int" and c: "c \<in> Nat"
  shows "(-c) * b \<le> (-c) * a"
using c proof (induct)
  case 0
  with a b show ?case by simp
next
  case (Succ n)
  from a b 1 have "-b \<le> -a" by simp
  with a b Succ show ?case by (simp add: add_leq_mono)
qed

lemma times_leq_right_pos_mono:
  assumes 1: "a \<le> b" and a: "a \<in> Int" and b: "b \<in> Int" and c: "c \<in> Nat"
  shows "a * c \<le> b * c"
  using c by induct (simp add: add_leq_mono 1 a b)+

lemma times_leq_right_neg_mono:
  assumes 1: "a \<le> b" and a: "a \<in> Int" and b: "b \<in> Int" and c: "c \<in> Nat"
  shows "b * (-c) \<le> a * (-c)"
using c proof (induct)
  case 0
  with a b show ?case by simp
next
  case (Succ n)
  from a b 1 have "-b \<le> -a" by simp
  with a b Succ show ?case by (simp add: add_leq_mono)
qed

lemma nat_leq_times_left:
  assumes a: "a \<in> Nat" and b: "b \<in> Int" and 1: "1 \<le> b"
  shows "a \<le> a * b"
proof -
  have "1 \<in> Int" by simp
  from 1 this b a have "a * 1 \<le> a * b" by (rule times_leq_left_pos_mono)
  with a b show ?thesis by simp
qed

lemma nat_leq_times_right:
  assumes "a \<in> Nat" and "b \<in> Int" and "1 \<le> b"
  shows "a \<le> b * a"
  using assms by (simp add: nat_leq_times_left times_commute)

text \<open> Similar lemmas for @{text "<"} \<close>

lemma times_less_left_pos_mono:
  assumes 1: "a < b" and a: "a \<in> Int" and b: "b \<in> Int" and c: "c \<in> Int" and 0: "0 < c"
  shows "c * a < c * b"
proof -
  from c 0 obtain n where "n \<in> Nat" "c = succ[n]"
    by cases auto
  from \<open>n \<in> Nat\<close> have "succ[n] * a < succ[n] * b"
    by induct (simp add: add_less_mono 1 a b)+
  with \<open>c = succ[n]\<close> show ?thesis by simp
qed

lemma times_less_left_neg_mono:
  assumes 1: "a < b" and a: "a \<in> Int" and b: "b \<in> Int" and c: "c \<in> Int" and 0: "c < 0"
  shows "c * b < c * a"
proof -
  from c 0 obtain n where "n \<in> Nat" "c = -succ[n]"
    by cases auto
  from a b 1 have "-b < -a" by simp
  with \<open>n \<in> Nat\<close> have "(-succ[n]) * b < (-succ[n]) * a"
    by (induct) (simp add: add_less_mono a b)+
  with \<open>c = -succ[n]\<close> show ?thesis by simp
qed

lemma times_less_right_pos_mono:
  assumes "a < b" and a: "a \<in> Int" and b: "b \<in> Int" and c: "c \<in> Int" and "0 < c"
  shows "a * c < b * c"
  using times_less_left_pos_mono[OF assms] a b c by (simp add: times_commute)

lemma times_less_right_neg_mono:
  assumes 1: "a < b" and a: "a \<in> Int" and b: "b \<in> Int" and c: "c \<in> Int" and "c < 0"
  shows "b * c < a * c"
  using times_less_left_neg_mono[OF assms] a b c by (simp add: times_commute)

lemma nat_less_times_left:
  assumes a: "a \<in> Int" and 0: "0 < a" and b: "b \<in> Int" and 1: "1 < b"
  shows "a < a * b"
proof -
  have "1 \<in> Int" by simp
  from 1 this b a 0 have "a * 1 < a * b" by (rule times_less_left_pos_mono)
  with a b show ?thesis by simp
qed

lemma nat_less_times_right:
  assumes "a \<in> Int" and 0: "0 < a" and "b \<in> Int" and "1 < b"
  shows "a < b * a"
  using assms by (simp add: nat_less_times_left times_commute)

lemma times_leq_left_pos_cancel [simp]:
  assumes a: "a \<in> Int" and b: "b \<in> Int" and c: "c \<in> Int" and 0: "0 < c"
  shows "(c * a \<le> c * b) = (a \<le> b)" (is "?lhs = ?rhs")
proof (rule boolEqual)
  {
    assume lhs: "?lhs" and contr: "\<not>?rhs"
    from a b contr have "b < a" by simp
    from this b a c 0 have "c * b < c * a" by (rule times_less_left_pos_mono)
    with a b c have "\<not>?lhs" by simp
    from this lhs have "FALSE" ..
  }
  moreover
  from c 0 have "c \<in> Nat"
    by (simp add: less_def)
  ultimately show "?lhs \<Leftrightarrow> ?rhs" 
    using times_leq_left_pos_mono[of a b c] assms by blast
qed (simp add: a b c)+

lemma times_leq_right_pos_cancel [simp]:
  assumes a: "a \<in> Int" and b: "b \<in> Int" and c: "c \<in> Int" and 0: "0 < c"
  shows "(a * c \<le> b * c) = (a \<le> b)" (is "?lhs = ?rhs")
proof -
  from a b c have "(a * c \<le> b * c) = (c * a \<le> c * b)"
    by (simp add: times_commute)
  with assms show ?thesis
    by simp
qed

lemma times_leq_left_neg_cancel [simp]:
  assumes a: "a \<in> Int" and b: "b \<in> Int" and c: "c \<in> Int" and 0: "c < 0"
  shows "(c * a \<le> c * b) = (b \<le> a)" (is "?lhs = ?rhs")
proof (rule boolEqual)
  {
    assume lhs: "?lhs" and contr: "\<not>?rhs"
    from a b contr have "a < b" by simp
    from this a b c 0 have "c * b < c * a" by (rule times_less_left_neg_mono)
    with a b c have "\<not>?lhs" by simp
    from this lhs have "FALSE" ..
  }
  moreover
  from c 0 obtain d where "d \<in> Nat" "c = -d"
    by (cases c) force+
  ultimately show "?lhs \<Leftrightarrow> ?rhs" 
    using times_leq_left_neg_mono[of b a d] assms by blast
qed (simp add: a b c)+

lemma times_leq_right_neg_cancel [simp]:
  assumes a: "a \<in> Int" and b: "b \<in> Int" and c: "c \<in> Int" and 0: "c < 0"
  shows "(a * c \<le> b * c) = (b \<le> a)" (is "?lhs = ?rhs")
proof -
  from a b c have "(a * c \<le> b * c) = (c * a \<le> c * b)"
    by (simp add: times_commute)
  with assms show ?thesis
    by simp
qed

lemma times_less_left_pos_cancel [simp]:
  assumes "a \<in> Int" and "b \<in> Int" and "c \<in> Int" and "0 < c"
  shows "(c * a < c * b) = (a < b)"
  unfolding less_def using assms by auto

lemma times_less_left_neg_cancel [simp]:
  assumes "a \<in> Int" and "b \<in> Int" and "c \<in> Int" and "c < 0"
  shows "(c * a < c * b) = (b < a)"
  unfolding less_def using assms by auto

lemma times_less_right_pos_cancel [simp]:
  assumes "a \<in> Int" and "b \<in> Int" and "c \<in> Int" and "0 < c"
  shows "(a * c < b * c) = (a < b)"
  unfolding less_def using assms by auto

lemma times_less_right_neg_cancel [simp]:
  assumes "a \<in> Int" and "b \<in> Int" and "c \<in> Int" and "c < 0"
  shows "(a * c < b * c) = (b < a)"
  unfolding less_def using assms by auto

lemma times_pos [simp]:
  assumes a: "a \<in> Int" and b: "b \<in> Int"
  shows "(0 < a * b) = ((0 < a \<and> 0 < b) \<or> (a < 0 \<and> b < 0))"
using a proof (cases)
  case 0
  with b show ?thesis by simp
next
  case (pos n)
  hence a': "a \<in> Nat" "0 < a"
    by auto
  from a have "(0 < a * b) = (a * 0 < a * b)"
    by simp
  also from a \<open>0 < a\<close> b have "\<dots> = (0 < b)"
    by (intro times_less_left_pos_cancel) simp+
  finally show ?thesis
    using a' by simp
next
  case (neg n)
  hence a': "a \<in> Int" "a < 0"
    by auto
  from a have "(0 < a * b) = (a * 0 < a * b)"
    by simp
  also from a' b have "\<dots> = (b < 0)"
    by (intro times_less_left_neg_cancel) simp+
  finally show ?thesis
    using a' by (simp add: int_less_not_sym[of a 0])
qed

lemma times_neg:
  assumes a: "a \<in> Int" and b: "b \<in> Int"
  shows "(a * b < 0) = ((0 < a \<and> b < 0) \<or> (a < 0 \<and> 0 < b))"
proof -
  from assms have "(a * b < 0) = (0 < (-a) * b)"
    by simp
  also from assms have "\<dots> = ((0 < -a \<and> 0 < b) \<or> (-a < 0 \<and> b < 0))"
    by (intro times_pos) simp+
  finally show ?thesis
    using assms by auto
qed


subsection \<open>Intervals of integers\<close>

definition intvl :: "[c,c] \<Rightarrow> c"    ("(_ .. _)" [90,90] 70)
where "i .. j \<equiv> { k \<in> Int : i \<le> k \<and> k \<le> j }"

lemma intvlI [iff]:
  assumes "k \<in> Int" and "i \<le> k" and "k \<le> j"
  shows "k \<in> i .. j"
  using assms by (simp add: intvl_def)

lemma intvlE [elim]:
  assumes "k \<in> i .. j" and "\<lbrakk>k \<in> Int; i \<le> k; k \<le> j\<rbrakk> \<Longrightarrow> P"
  shows P
  using assms by (simp add: intvl_def)

lemma intvlIff [simp]: "(k \<in> i .. j) = (k \<in> Int \<and> i \<le> k \<and> k \<le> j)"
  by auto

lemmas
  setEqualI [where A = "i .. j" for i j, intro]
  setEqualI [where B = "i .. j" for i j, intro]

lemma gtNotinIntvl:
  assumes gt: "i > j" and k: "k \<in> i .. j" and i: "i \<in> Int" and j: "j \<in> Int"
  shows "P"
proof -
  from k have "k \<in> Int" "i \<le> k" "k \<le> j" by auto
  with i j have "i \<le> j" by (auto elim: int_leq_trans)
  with i j have "\<not>(j < i)" by simp
  from this gt show ?thesis ..
qed

lemma intvlIsEmpty:
  assumes "i \<in> Int" and "j \<in> Int" and "i > j"
  shows "i .. j = {}"
  using assms by (blast dest: gtNotinIntvl)

lemma intvlEmpty_iff:
  assumes i: "i \<in> Int" and j: "j \<in> Int"
  shows "(i .. j = {}) = (i > j)"
proof -
  {
    assume mt: "i .. j = {}"
    have "i > j"
    proof (rule contradiction)
      assume "\<not>(i > j)"
      with assms have "i \<le> j" by simp
      with i have "i \<in> i ..j" by simp
      with mt show "FALSE" by simp
    qed
  }
  moreover 
  from i j have "i > j \<Rightarrow> i..j = {}"
    by (blast dest: intvlIsEmpty)
  ultimately show ?thesis
    by blast
qed

lemma intvlSingleton [simp]:
  "i \<in> Int \<Longrightarrow> i .. i = {i}"
  by (auto dest: int_leq_antisym)

lemma intvlSucc [simp]:
  assumes "i \<in> Int" and "j \<in> Int" and "i \<le> succ[j]"
  shows "i .. succ[j] = (i..j \<union> {succ[j]})"
  using assms by auto

lemma succIntvl:
  assumes "i \<in> Int" and "j \<in> Int"
  shows "succ[i] .. j = (i .. j \<setminus> {i})"
  using assms unfolding intvl_def by auto

lemma intvlEqual_iff:
  assumes i: "i \<in> Int" and j: "j \<in> Int" and k: "k \<in> Int" and l: "l \<in> Int"
  shows "(i .. j = k .. l) = ((i > j \<and> k > l) \<or> (i = k \<and> j = l))" (is "?lhs = ?rhs")
proof (cases "i > j")
  case True
  with i j have "i .. j = {}" 
    by (simp add: intvlEmpty_iff)
  moreover
  from k l have "(k .. l = {}) = (k > l)"
    by (simp add: intvlEmpty_iff)
  ultimately show ?thesis
    using assms True by force
next
  case False
  with i j have ij: "i \<le> j" by simp
  with i j have "i \<in> i .. j" "j \<in> i .. j" by simp+
  {
    assume eq: "i..j = k..l" and idx: "i \<noteq> k \<or> j \<noteq> l"
    from eq \<open>i \<in> i..j\<close> intvlIsEmpty[OF k l] have "\<not>(k > l)"
      by auto
    with k l have "k \<in> k..l" "l \<in> k..l" by simp+
    from idx have "FALSE"
    proof
      assume "i \<noteq> k"
      from this i k show "FALSE"
      proof (rule int_neq_lessE)
        assume "i < k"
        with i k have "i \<notin> k .. l" by auto
        with eq \<open>i \<in> i .. j\<close> show "FALSE" by simp
      next
        assume "k < i"
        with i k have "k \<notin> i .. j" by auto
        with eq \<open>k \<in> k..l\<close> show "FALSE" by simp
      qed
    next
      assume "j \<noteq> l"
      from this j l show "FALSE"
      proof (rule int_neq_lessE)
        assume "j < l"
        with j l have "l \<notin> i .. j" by auto
        with eq \<open>l \<in> k ..l\<close> show "FALSE" by simp
      next
        assume "l < j"
        with j l have "j \<notin> k..l" by auto
        with eq \<open>j \<in> i..j\<close> show "FALSE" by simp
      qed
    qed
  }
  thus ?thesis using False by auto
qed

lemma zerotoInj [simp]:
  assumes "l \<in> Nat" and "m \<in> Int" and "n \<in> Int"
  shows "(0 .. l = m .. n) = (m=0 \<and> l=n)"
using assms by (auto simp: intvlEqual_iff)

lemma zerotoInj' [simp]:
  assumes "k \<in> Int" and "l \<in> Int" and "n \<in> Nat"
  shows "(k .. l = 0 .. n) = (k=0 \<and> l=n)"
using assms by (auto simp: intvlEqual_iff)

lemma zerotoEmpty [simp]:
  assumes "m \<in> Nat"
  shows "succ[m] .. 0 = {}"
  using assms by (intro intvlIsEmpty) auto

lemma onetoInj [simp]:
  assumes "l \<in> Nat" and "m \<in> Int" and "n \<in> Int" and "l \<noteq> 0 \<or> 1 \<le> l"
  shows "(1 .. l = m .. n) = (m=1 \<and> l=n)"
  using assms by (auto simp: intvlEqual_iff)

lemma onetoInj' [simp]:
  assumes "k \<in> Int" and "l \<in> Int" and "n \<in> Nat" and "n\<noteq>0 \<or> 1 \<le> n"
  shows "(k .. l = 1 .. n) = (k=1 \<and> l=n)"
  using assms by (auto simp: intvlEqual_iff)

lemma SuccInIntvlSucc:
  assumes "m \<le> k" and "k \<in> Int" and "m \<in> Int" and "n \<in> Int"
  shows "(succ[k] \<in> m .. succ[n]) = (k \<in> m .. n)"
  using assms by auto

lemma SuccInIntvlSuccSucc:
  assumes "i \<in> Int" and "j \<in> Int" and "k \<in> Int"
  shows "(succ[i] \<in> succ[j] .. succ[k]) = (i \<in> j .. k)"
  using assms by auto

end
