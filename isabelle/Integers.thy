(*  Title:      Integers.thy
    Author:     Hernan Vanzetto, LORIA
    Copyright (C) 2009-2011  INRIA and Microsoft Corporation
    License:    BSD
    Version:    Isabelle2011-1
    Time-stamp: <2011-10-11 17:40:02 merz>

*)

section \<open> The Integers as a superset of natural numbers \<close>

theory Integers
imports Tuples NatArith
begin

subsection \<open> The minus sign \<close>

consts
  "minus" :: "c \<Rightarrow> c"                ("-._" [75] 75)

syntax  (* -- syntax for negative naturals *)
   "-.0"  :: "c"   ("-.0")
   "-.1"  :: "c"   ("-.1")
   "-.2"  :: "c"   ("-.2")
translations
   "-.0"  \<rightleftharpoons>  "-.(0)"
   "-.1"  \<rightleftharpoons>  "-.(1)"
   "-.2"  \<rightleftharpoons>  "-.(2)"

(* lemma eq_imp_negeq: "n = m \<Longrightarrow> -.n = -.m" by simp *)

axiomatization where
  neg0 [simp]: "-.0 = 0"
and
  neg_neg [simp]: "-.-.n = n"
and
  negNotInNat [simp]: "-.(Succ[n]) \<notin> Nat"

lemma negNat_noteq_Nat [simp]:
  "\<lbrakk>m \<in> Nat; n \<in> Nat\<rbrakk> \<Longrightarrow> (-. Succ[m] = Succ[n]) = FALSE"
proof (rule contradiction)
  assume "(-. Succ[m] = Succ[n]) \<noteq> FALSE"
    and m: "m \<in> Nat" and n: "n \<in> Nat"
  hence "-. Succ[m] = Succ[n]" by auto
  hence "-. Succ[m] \<in> Nat" using n by auto
  with negNotInNat[of m] show FALSE by simp
qed

lemma negNat_noteq_Nat2 [simp]:
  assumes m: "m \<in> Nat" and n: "n \<in> Nat"
  shows "(Succ[m] = -. Succ[n]) = FALSE"
proof auto
  assume "Succ[m] = -. Succ[n]"
  hence "-. Succ[n] = Succ[m]" by simp
  with m n show "FALSE" by simp
qed

lemma nat_not_eq_inv: "n \<in> Nat \<Longrightarrow> n = 0 \<or> -.n \<noteq> n"
  using not0_implies_Suc[of n] by auto

lemma minusInj [dest]:
  assumes hyp: "-.n = -.m"
  shows "n = m"
proof -
  from hyp have "-.-.n = -.-.m" by simp
  thus ?thesis by simp
qed

lemma minusInj_iff [simp]:
  "-.x = -.y = (x = y)"
by auto

lemma neg0_imp_0 [simp]: "-.n = 0 = (n = 0)"
proof auto
  assume "-.n = 0"
  hence "-.-.n = 0" by simp
  thus "n = 0" by simp
qed

lemma neg0_eq_0 [dest]: "-.n = 0 \<Longrightarrow> (n = 0)"
by simp

lemma notneg0_imp_not0 [dest]: "-.n \<noteq> 0 \<Longrightarrow> n \<noteq> 0"
by auto

lemma not0_imp_notNat [simp]: "n \<in> Nat \<Longrightarrow> n \<noteq> 0 \<Longrightarrow> -.n \<notin> Nat"
  using not0_implies_Suc[of n] by auto

lemma negSuccNotZero [simp]: "n \<in> Nat \<Longrightarrow> (-. Succ[n] = 0) = FALSE"
by auto

lemma negSuccNotZero2 [simp]: "n \<in> Nat \<Longrightarrow> (0 = -. Succ[n]) = FALSE"
proof auto
  assume n: "n \<in> Nat" and 1: "0 = -. Succ[n]"
  from 1 have "-. Succ[n] = 0" by simp
  with n show FALSE by simp
qed

lemma negInNat_imp_false [dest]: "-.Succ[n] \<in> Nat \<Longrightarrow> FALSE"
  using negNotInNat[of n] by simp

lemma negInNatFalse [simp]: "-.Succ[n] \<in> Nat = FALSE"
  using negNotInNat[of n] by auto

lemma n_negn_inNat_is0 [simp]:
  assumes "n \<in> Nat"
  shows "-.n \<in> Nat = (n = 0)"
using assms by (cases "n", auto)

lemma minus_sym: "-.a = b = (a = -.b)"
by auto

lemma negNat_exists: "-.n \<in> Nat \<Longrightarrow> \<exists>k \<in> Nat: n = -.k"
by force

lemma nat_eq_negnat_is_0 [simp]:
  assumes "n \<in> Nat"
  shows "(n = -.n) = (n = 0)"
using assms by (cases "n", auto)

(* used for simplification in additions *)
lemma (*[simp]*) "\<exists>x \<in> Nat : -.1 = -.x" by auto
lemma (*[simp]*) "x \<in> Nat \<Longrightarrow> (1 = -.x) = FALSE" by (auto simp: sym[OF minus_sym])


subsection \<open> The set of Integers \<close>

definition Int
where "Int \<equiv> Nat \<union> {-.n : n \<in> Nat}"

lemma natInInt [simp]: "n \<in> Nat \<Longrightarrow> n \<in> Int"
by (simp add: Int_def)

lemma intDisj: "n \<in> Int \<Longrightarrow> n \<in> Nat \<or> n \<in> {-.n : n \<in> Nat}"
by (auto simp: Int_def)

lemma negint_eq_int [simp]: "-.n \<in> Int = (n \<in> Int)"
unfolding Int_def by force

lemma intCases [case_names Positive Negative, cases set: Int]:
  assumes n: "n \<in> Int"
  and sc: "n \<in> Nat \<Longrightarrow> P"
  and nsc: "\<And>m. \<lbrakk>m \<in> Nat; n = -.m\<rbrakk> \<Longrightarrow> P"
  shows "P"
using assms unfolding Int_def by auto

(* -- Integer cases over two parameters *)
lemma intCases2:
  assumes m: "m \<in> Int" and n: "n \<in> Int"
    and pp: "\<And>m n. \<lbrakk>m \<in> Nat; n \<in> Nat\<rbrakk> \<Longrightarrow> P(m,n)"
    and pn: "\<And>m n. \<lbrakk>m \<in> Nat; n \<in> Nat\<rbrakk> \<Longrightarrow> P(m,-.n)"
    and np: "\<And>m n. \<lbrakk>m \<in> Nat; n \<in> Nat\<rbrakk> \<Longrightarrow> P(-.m,n)"
    and nn: "\<And>m n. \<lbrakk>m \<in> Nat; n \<in> Nat\<rbrakk> \<Longrightarrow> P(-.m,-.n)"
  shows "P(m,n)"
using m proof (cases "m")
  assume "m \<in> Nat"
  from n this pp pn show "P(m,n)" by (cases "n", auto)
next
  fix m'
  assume "m' \<in> Nat" "m = -. m'"
  from n this np nn show "P(m,n)" by (cases "n", auto)
qed

lemma intCases3:
  assumes m: "m \<in> Int" and n: "n \<in> Int" and p: "p \<in> Int"
    and ppp: "\<And>m n p. \<lbrakk>m \<in> Nat; n \<in> Nat; p \<in> Nat\<rbrakk> \<Longrightarrow> P(m,n,p)"
    and ppn: "\<And>m n p. \<lbrakk>m \<in> Nat; n \<in> Nat; p \<in> Nat\<rbrakk> \<Longrightarrow> P(m,n,-.p)"
    and pnp: "\<And>m n p. \<lbrakk>m \<in> Nat; n \<in> Nat; p \<in> Nat\<rbrakk> \<Longrightarrow> P(m,-.n,p)"
    and pnn: "\<And>m n p. \<lbrakk>m \<in> Nat; n \<in> Nat; p \<in> Nat\<rbrakk> \<Longrightarrow> P(m,-.n,-.p)"
    and npp: "\<And>m n p. \<lbrakk>m \<in> Nat; n \<in> Nat; p \<in> Nat\<rbrakk> \<Longrightarrow> P(-.m,n,p)"
    and npn: "\<And>m n p. \<lbrakk>m \<in> Nat; n \<in> Nat; p \<in> Nat\<rbrakk> \<Longrightarrow> P(-.m,n,-.p)"
    and nnp: "\<And>m n p. \<lbrakk>m \<in> Nat; n \<in> Nat; p \<in> Nat\<rbrakk> \<Longrightarrow> P(-.m,-.n,p)"
    and nnn: "\<And>m n p. \<lbrakk>m \<in> Nat; n \<in> Nat; p \<in> Nat\<rbrakk> \<Longrightarrow> P(-.m,-.n,-.p)"
  shows "P(m,n,p)"
proof (rule intCases2[OF m n])
  fix m n
  assume "m \<in> Nat" and "n \<in> Nat"
  from p this ppp ppn show "P(m,n,p)" by (cases "p", auto)
next
  fix m n
  assume "m \<in> Nat" and "n \<in> Nat"
  from p this pnp pnn show "P(m, -.n, p)" by (cases "p", auto)
next
  fix m n
  assume "m \<in> Nat" and "n \<in> Nat"
  from p this npp npn show "P(-.m, n, p)" by (cases "p", auto)
next
  fix m n
  assume "m \<in> Nat" and "n \<in> Nat"
  from p this nnp nnn show "P(-.m, -.n, p)" by (cases "p", auto)
qed

lemma int_eq_negint_is_0 [simp]: "n \<in> Int \<Longrightarrow> n = -.n = (n = 0)"
by(rule intCases, auto)

lemma intNotNatIsNeg: "\<lbrakk>n \<notin> Nat; n \<in> Int\<rbrakk> \<Longrightarrow> \<exists>k \<in> Nat: n = -.k"
unfolding Int_def by auto

lemma intNotNatIsNegNat: "\<lbrakk>n \<notin> Nat; n \<in> Int\<rbrakk> \<Longrightarrow> -.n \<in> Nat"
unfolding Int_def by auto


subsection \<open> Predicates ''is positive'' and 'is negative' \<close>

definition isPos       (* -- Predicate ''is positive'' *)
where "isPos(n) \<equiv> \<exists>k \<in> Nat: n = Succ[k]"

definition isNeg       (* -- Predicate ''is negative'' *)
where "isNeg(n) \<equiv> \<exists>k \<in> Nat: n = -.Succ[k]"

lemma boolify_isPos [simp]: "boolify(isPos(n)) = (isPos(n))"
by (simp add: isPos_def)

lemma isPos_isBool [intro!,simp]: "isBool(isPos(n))"
by (simp add: isPos_def)

lemma boolify_isNeg [simp]: "boolify(isNeg(n)) = (isNeg(n))"
by (simp add: isNeg_def)

lemma isNeg_isBool [intro!,simp]: "isBool(isNeg(n))"
by (simp add: isNeg_def)

lemma zeroNotPos [dest]: "isPos(0) \<Longrightarrow> FALSE" by (auto simp: isPos_def)
lemma zeroNotNeg [dest]: "isNeg(0) \<Longrightarrow> FALSE" by (auto simp: isNeg_def)

lemma natIsPos [simp]: "n \<in> Nat \<Longrightarrow> isPos(Succ[n])" by(simp add: isPos_def)
lemma negIsNeg [simp]: "n \<in> Nat \<Longrightarrow> isNeg(-.Succ[n])" by(simp add: isNeg_def)

lemma negIsNotPos [simp]: "n \<in> Nat \<Longrightarrow> isPos(-.Succ[n]) = FALSE"
by(simp add: isPos_def)

(*lemma isPos_eq_inNat1: "isPos(n) = (n \<in> Nat \\ {0})"
  unfolding isPos_def using not0_implies_Suc[of n] by auto*)

lemma isPos_eq_inNat1: "isPos(n) = (n \<in> Nat \<and> n \<noteq> 0)"
unfolding isPos_def using not0_implies_Suc[of n] by auto

(*lemma isNeg_eq_inNegNat:
  "isNeg(n) = (n \<in> {-.n : n \<in> Nat } \\ {0})"
  unfolding isNeg_def by force*)

lemma isNeg_eq_inNegNat:
  "isNeg(n) = (n \<in> {-.n : n \<in> Nat } \<and> n \<noteq> 0)"
unfolding isNeg_def by force

lemma intIsPos_isNat: "n \<in> Int \<Longrightarrow> isPos(n) \<Longrightarrow> n \<in> Nat"
by(auto simp: isPos_def)

lemma negNotNat_isNat:
  assumes n: "n \<in> Int" shows "(-.n \<in> Nat) = FALSE \<Longrightarrow> n \<in> Nat"
using n by (cases, auto)

lemma noNatisNeg [simp]:
  "n \<in> Nat \<Longrightarrow> isNeg(n) = FALSE" (* -- No natural number is negative *)
unfolding isNeg_def using negNotInNat by blast

lemma negNat_isNeg [intro]: "\<lbrakk>m \<in> Nat; m \<noteq> 0\<rbrakk> \<Longrightarrow> isNeg(-.m)"
unfolding isNeg_eq_inNegNat by auto

lemma nat_is_0_or_pos: "(n = 0 \<or> isPos(n)) = (n \<in> Nat)"
unfolding isPos_def by force

lemma isNeg_dichotomy (*[simp]*): "n \<in> Int \<Longrightarrow> isNeg(-.n) \<Longrightarrow> isNeg(n) = FALSE"
unfolding isNeg_def by auto

lemma isPos_isNeg_false [simp]: "n \<in> Int \<Longrightarrow> isPos(n) \<Longrightarrow> isNeg(n) = FALSE"
 unfolding isPos_def by force

(*lemma notPosIsNegPos:
  "n \<in> Int \\ {0} \<Longrightarrow> \<not> isPos(n) \<Longrightarrow> isPos(-.n)"
unfolding isPos_eq_inNat1 using intNotNatIsNegNat by auto*)

lemma isPos_neg_isNeg [simp]:
  assumes n: "n \<in> Int" shows "isPos(-.n) = isNeg(n)"
by (auto simp: minus_sym isPos_def isNeg_def)

lemma notIsNeg0_isPos:
  assumes n: "n \<in> Int"
  shows "\<lbrakk>\<not> isNeg(n); n \<noteq> 0\<rbrakk> \<Longrightarrow> isPos(n)"
using n by (cases, auto simp: isPos_eq_inNat1 dest: negNat_isNeg)

lemma notIsPos_notNat [simp]: "\<lbrakk>\<not> isPos(n); n \<noteq> 0\<rbrakk> \<Longrightarrow> n \<in> Nat = FALSE"
by (auto simp: isPos_eq_inNat1)

lemma intThenPosZeroNeg:
  assumes n: "n \<in> Int"
  shows "isNeg(n) \<or> n = 0 \<or> isPos(n)"
by (auto elim: notIsNeg0_isPos[OF n])


subsection \<open> Signum function and absolute value \<close>

definition sgn                 (* -- signum function *)
where "sgn(n) \<equiv> IF n = 0 THEN 0 ELSE (IF isPos(n) THEN 1 ELSE -.1)"

definition abs                 (* -- absolute value *)
where "abs(n) \<equiv> IF sgn(n) = -.1 THEN -.n ELSE n"

lemma sgnInInt [simp]: "n \<in> Int \<Longrightarrow> sgn(n) \<in> Int"
by (auto simp: sgn_def)

lemma sgn0 [simp]: "sgn(0) = 0"
by (simp add: sgn_def)

lemma sgnPos [simp]: "n \<in> Nat \<Longrightarrow> sgn(Succ[n]) = 1"
by (simp add: sgn_def)

lemma sgnNeg [simp]: "n \<in> Nat \<Longrightarrow> sgn(-.Succ[n]) = -.1"
by (simp add: sgn_def)

lemma sgn0_imp_0: "sgn(n) = 0 \<Longrightarrow> n = 0"
by (auto simp: sgn_def)

lemma sgn0_iff_0 [simp]: "(sgn(n) = 0) = (n = 0)"
by (auto simp: sgn_def)

lemma sgn1_imp_pos (*[simp]*): "sgn(n) = 1 \<Longrightarrow> n \<in> Nat \<and> n \<noteq> 0"
unfolding sgn_def isPos_eq_inNat1 by auto

(*lemma neg_imp_negSuc (*[simp]*):
  assumes h:"n \<in> {-.n : n \<in> Nat } \\ {0}" shows "isNeg(n)"
unfolding isNeg_def
proof -
  from h have 1:"\<exists>k \<in> Nat : n = -.k" and 2:"n \<noteq> 0" by auto
  from 1 obtain k where k:"k \<in> Nat" and 3:"n = -.k" by auto
  with 2 have "k \<noteq> 0" by auto
  with k not0_implies_Suc[of k] have "\<exists>m \<in> Nat : k = Succ[m]" by auto
  with 3 show "\<exists>k \<in> Nat : n = -.(Succ[k])" by auto
qed*)

lemma sgnm1_imp_neg:
  assumes n:"n \<in> Int" shows "sgn(n) = -.1 \<Longrightarrow> isNeg(n)"
unfolding sgn_def using intThenPosZeroNeg[OF n] by auto

lemma isPos_sgn [simp]: "isPos(sgn(n)) = isPos(n)"
unfolding isPos_def sgn_def by force

lemma sgnNat_is_0or1 (*[simp]*):
  "n \<in> Nat \<Longrightarrow> sgn(n) = 0 \<or> sgn(n) = 1"
unfolding sgn_def isPos_eq_inNat1 by auto

lemma sgnNat_not0:
  "\<lbrakk>n \<in> Nat; sgn(n) \<noteq> 0\<rbrakk> \<Longrightarrow> sgn(n) = 1"
using sgnNat_is_0or1[of n] by auto

lemma sgnNat_not1:
  "\<lbrakk>n \<in> Nat; sgn(n) \<noteq> 1\<rbrakk> \<Longrightarrow> n = 0"
using sgnNat_is_0or1[of n] by auto

lemma sgnNat_not_neg [simp]:
  "n \<in> Nat \<Longrightarrow> sgn(n) = -.1 = FALSE"
unfolding sgn_def isPos_eq_inNat1 by auto

lemma notNat_imp_sgn_neg1 [intro]: "n \<notin> Nat \<Longrightarrow> sgn(n) = -.1"
unfolding sgn_def isPos_eq_inNat1 by auto

lemma eqSgnNat_imp_nat: "sgn(m) = sgn(n) \<Longrightarrow> m \<in> Nat \<Longrightarrow> n \<in> Nat"
unfolding sgn_def isPos_eq_inNat1 by auto

lemma eqSgn_imp_0_nat [simp]: "n \<in> Nat \<Longrightarrow> sgn(n) = sgn(-.n) = (n = 0)"
unfolding sgn_def isPos_def by force

lemma eqSgn_imp_0_nat2 [simp]: "n \<in> Nat \<Longrightarrow> sgn(-.n) = sgn(n) = (n = 0)"
unfolding sgn_def isPos_def by force

lemma eqSgn_imp_0 [simp]: "n \<in> Int \<Longrightarrow> sgn(n) = sgn(-.n) = (n = 0)"
by(rule intCases, auto)

(*lemma notSgnNegs [simp]: "n \<in> Int \\ {0} \<Longrightarrow> sgn(n) = sgn(-.n) = FALSE"
  by(rule intCases[of n], simp_all) *)

lemma sgn_eq_neg1_is_not_nat (*[simp]*): "(sgn(n) = -.1) = (n \<notin> Nat \<and> n \<noteq> 0)"
unfolding sgn_def isPos_eq_inNat1 by auto

lemma sgn_not_neg1_is_nat [simp]: "((sgn(n) = -.1) = FALSE) = (n \<in> Nat)"
by (auto simp: sgn_eq_neg1_is_not_nat)

lemma sgn_neg_eq_1_false: "\<lbrakk>sgn(-.m) = 1; m \<in> Nat\<rbrakk> \<Longrightarrow> P"
unfolding sgn_def by auto

lemma sgn_minus [simp]:
  assumes n: "n \<in> Int"
  shows "sgn(-.n) = -.sgn(n)"
unfolding sgn_def using n by (cases, auto)

text \<open> Absolute value \<close>

lemma absIsNat [simp]:
  assumes n: "n \<in> Int" shows "abs(n) \<in> Nat"
unfolding abs_def using intNotNatIsNegNat[OF _ n] by auto

lemma absNat [simp]: "n \<in> Nat \<Longrightarrow> abs(n) = n"
unfolding abs_def by auto

lemma abs0 [simp]: "abs(0) = 0"
unfolding abs_def by simp

(**
lemma absn0 [simp]: "abs(-.0) = 0"
by simp
**)

lemma abs_negNat [simp]: "n \<in> Nat \<Longrightarrow> abs(-.n) = n"
unfolding abs_def by (auto dest: sgnNat_not1)

lemma abs_neg [simp]:
  assumes n: "n \<in> Int" shows "abs(-.n) = abs(n)"
unfolding abs_def using n by (auto dest: sgnNat_not1)


subsection \<open> Orders on integers \<close>

text \<open>
  We distinguish four cases, depending on the arguments being in
  Nat or negative.
\<close>

lemmas int_leq_pp_def = nat_leq_def
  (* -- 'positive-positive' case, ie: both arguments are naturals *)

axiomatization where
  int_leq_pn_def [simp]: "\<lbrakk>a \<in> Nat; b \<in> Nat\<rbrakk> \<Longrightarrow> a \<le> -.b = FALSE"
and
  int_leq_np_def [simp]: "\<lbrakk>a \<in> Nat; b \<in> Nat\<rbrakk> \<Longrightarrow> -.a \<le> b = TRUE"
and
  int_leq_nn_def [simp]: "\<lbrakk>a \<in> Nat; b \<in> Nat\<rbrakk> \<Longrightarrow> -.a \<le> -.b = (b \<le> a)"

(* lemmas int_leq_def = int_leq_pn_def int_leq_np_def int_leq_nn_def *)

lemma int_boolify_leq [simp]:
  "\<lbrakk>a \<in> Int; b \<in> Int\<rbrakk> \<Longrightarrow> boolify(a \<le> b) = (a \<le> b)"
by(rule intCases2[of a b], simp_all)

lemma int_leq_isBool [intro!,simp]:
  "\<lbrakk>a \<in> Int; b \<in> Int\<rbrakk> \<Longrightarrow> isBool(a \<le> b)"
unfolding isBool_def by auto

lemma int_leq_refl [iff]: "n \<in> Int \<Longrightarrow> n \<le> n"
by(rule intCases, auto)

lemma eq_leq_bothE: (* -- reduce equality over integers to double inequality *)
  assumes "m \<in> Int" and "n \<in> Int" and "m = n" and "\<lbrakk>m \<le> n; n \<le> m\<rbrakk> \<Longrightarrow> P"
  shows "P"
using assms by simp

lemma neg_le_iff_le [simp]:
  "\<lbrakk>m \<in> Int; n \<in> Int \<rbrakk> \<Longrightarrow> -.n \<le> -.m = (m \<le> n)"
by(rule intCases2[of m n], simp_all)


subsection \<open> Addition of integers \<close>

text \<open>
  Again, we distinguish four cases in the definition of @{text "a + b"},
  according to each argument being positive or negative.
\<close>

(* cf. NatArith *)
(** The following is rejected by Isabelle because the two definitions
    are not distinguishable by argument types.
defs (unchecked overloaded)
  int_add_def: "\<lbrakk>a \<in> Int; b \<in> Int \<rbrakk> \<Longrightarrow> a + b \<equiv>
    IF a \<in> Nat \<and> b \<in> Nat THEN addnat(a)[b]
    ELSE IF isNeg(a) \<and> isNeg(b) THEN -.(addnat(-.a)[-.b])
    ELSE IF isNeg(a) THEN IF -.a \<le> b THEN b -- a ELSE -.(a -- b)
    ELSE IF a \<le> -.b THEN -.(b -- a) ELSE a -- b"
**)

lemmas
  int_add_pp_def = nat_add_def  (* -- both numbers are positive, ie. naturals *)

axiomatization where
int_add_pn_def: "\<lbrakk>a \<in> Nat; b \<in> Nat\<rbrakk> \<Longrightarrow> a + (-.b) \<equiv> IF a \<le> b THEN -.(b -- a) ELSE a -- b"
and
int_add_np_def: "\<lbrakk>a \<in> Nat; b \<in> Nat\<rbrakk> \<Longrightarrow> (-.a) + b \<equiv> IF b \<le> a THEN -.(a -- b) ELSE b -- a"
and
int_add_nn_def [simp]: "\<lbrakk>a \<in> Nat; b \<in> Nat\<rbrakk> \<Longrightarrow> (-.a) + (-.b) = -.(a + b)"

lemmas int_add_def = int_add_pn_def int_add_np_def (*int_add_nn_def*)
  (* -- When we use these definitions, we don't want to unfold the 'pp' case *)

lemma int_add_neg_eq_natDiff [simp]: "\<lbrakk>n \<le> m; m \<in> Nat; n \<in> Nat\<rbrakk> \<Longrightarrow> m + (-.n) = m -- n"
by (auto simp: int_add_pn_def dest: nat_leq_antisym)

text \<open> Closure \<close>

lemma addIsInt [simp]: "\<lbrakk>m \<in> Int; n \<in> Int\<rbrakk> \<Longrightarrow> m + n \<in> Int"
by (rule intCases2[of m n], auto simp: int_add_def)

text \<open> Neutral element \<close>

lemma add_0_right_int [simp]: "n \<in> Int \<Longrightarrow> n + 0 = n"
by(rule intCases, auto simp add: int_add_np_def)
lemma add_0_left_int [simp]: "n \<in> Int \<Longrightarrow> 0 + n = n"
by(rule intCases, auto simp add: int_add_pn_def)

text \<open> Additive inverse element \<close>

lemma add_inverse_nat [simp]: "n \<in> Nat \<Longrightarrow> n + -.n = 0"
by(simp add: int_add_pn_def)

lemma add_inverse2_nat [simp]: "n \<in> Nat \<Longrightarrow> -.n + n = 0"
by(simp add: int_add_np_def)

lemma add_inverse_int [simp]: "n \<in> Int \<Longrightarrow> n + -.n = 0"
by (rule intCases, auto simp: int_add_def)

lemma add_inverse2_int [simp]: "n \<in> Int \<Longrightarrow> -.n + n = 0"
by (rule intCases, auto simp: int_add_def)

text \<open> Commutativity \<close>

lemma add_commute_pn_nat: "\<lbrakk>m \<in> Nat; n \<in> Nat\<rbrakk> \<Longrightarrow> m + -.n = -.n + m"
by(simp add: int_add_def)

lemma add_commute_int: "\<lbrakk>m \<in> Int; n \<in> Int\<rbrakk> \<Longrightarrow> m + n = n + m"
  by(rule intCases2[of m n], auto simp add: int_add_def add_commute_nat)

text \<open> Associativity \<close>

lemma add_pn_eq_adiff [simp]:
  "\<lbrakk>m \<le> n; m \<in> Nat; n \<in> Nat\<rbrakk> \<Longrightarrow> m + -.n = -.(n -- m)"
by (simp add: int_add_def)

lemma adiff_add_assoc5:
  assumes m: "m \<in> Nat" and n: "n \<in> Nat" and p: "p \<in> Nat"
  shows "\<lbrakk>n \<le> p;  p \<le> m + n;  m \<le> p -- n\<rbrakk> \<Longrightarrow> -.(p -- n -- m) = m + n -- p"
apply (induct p n rule: diffInduct)
using assms by (auto dest: nat_leq_antisym)

lemma adiff_add_assoc6:
  assumes m: "m \<in> Nat" and n: "n \<in> Nat" and p: "p \<in> Nat"
  shows "\<lbrakk>n \<le> p; m + n \<le> p; p -- n \<le> m\<rbrakk> \<Longrightarrow> m -- (p -- n) = -.(p -- (m + n))"
apply (induct p n rule: diffInduct)
using assms by (auto dest: nat_leq_antisym)

lemma adiff_add_assoc7:
  assumes m: "m \<in> Nat" and n: "n \<in> Nat" and p: "p \<in> Nat"
  shows "\<lbrakk>p + n \<le> m; m \<le> n\<rbrakk> \<Longrightarrow> -.(m -- (p + n)) = n -- m + p"
apply (induct n m rule: diffInduct)
using assms by simp_all

lemma adiff_add_assoc8:
  assumes m: "m \<in> Nat" and n: "n \<in> Nat" and p: "p \<in> Nat"
  shows "\<lbrakk>n \<le> m; p \<le> m -- n; p \<le> m; m -- p \<le> n\<rbrakk> \<Longrightarrow> m -- n -- p = -.(n -- (m -- p))"
using adiff_add_assoc6[OF n p m] apply simp
using leq_adiff_right_add_left[OF _ p m n] add_commute_nat[OF p n] apply simp
by(rule adiff_adiff_left_nat[OF m n p])

declare leq_neq_iff_less [simplified,simp]

lemma int_add_assoc1:
  assumes m: "m \<in> Nat" and n: "n \<in> Nat" and p: "p \<in> Nat"
  shows "m + (n + -.p) = (m + n) + -.p"
apply(rule nat_leq_cases[OF p n])
  using assms apply simp_all
  apply(rule nat_leq_cases[of p "m + n"], simp_all)
    apply(simp add: adiff_add_assoc[OF _ m n p])
  apply(rule nat_leq_cases[of p "m + n"], simp+)
    apply(rule nat_leq_cases[of "p -- n" m], simp+)
      apply(rule adiff_add_assoc3, simp+)
      apply(rule adiff_add_assoc5, simp+)
    apply(rule nat_leq_cases[of "p -- n" m], simp_all)
      apply(rule adiff_add_assoc6, simp_all)
      apply(simp only: add_commute_nat[of m n])
      apply(rule adiff_adiff_left_nat, simp+)
done

lemma int_add_assoc2:
  assumes m: "m \<in> Nat" and n: "n \<in> Nat" and p: "p \<in> Nat"
  shows "m + (-.p + n) = (m + -.p) + n"
using assms apply (simp add: add_commute_int[of "-.p" n])
  using int_add_assoc1[OF m n p] apply simp
  apply(rule nat_leq_cases[of p "m + n"], simp_all)
    apply(rule nat_leq_cases[OF p m], simp_all)
      apply(rule adiff_add_assoc2, simp_all)
      apply (simp add: add_commute_int[of "-.(p -- m)" n])
      apply(simp only: add_commute_nat[OF m n])
      apply(rule nat_leq_cases[of "p -- m" n], simp_all)
	apply(rule adiff_add_assoc3[symmetric], simp+)
	apply(rule adiff_add_assoc5[symmetric], simp+)
  apply(rule nat_leq_cases[OF p m], simp_all)
    apply (simp add: add_commute_nat[OF m n])
    apply (simp add: add_commute_int[of "-.(p -- m)" n])
    apply(rule nat_leq_cases[of "p -- m" n], simp_all)
      apply(simp add: add_commute_nat[OF m n])
      apply(rule adiff_add_assoc6[symmetric], simp+)
      apply(rule adiff_adiff_left_nat[symmetric], simp+)
done

declare leq_neq_iff_less [simplified,simp del]

lemma int_add_assoc3:
  assumes m: "m \<in> Nat" and n: "n \<in> Nat" and p: "p \<in> Nat"
  shows "m + -.(n + p) = m + -.n + -.p"
apply(rule nat_leq_cases[of "n + p" m])
  using assms apply simp_all
  apply(rule nat_leq_cases[OF n m], simp_all)
    apply(rule nat_leq_cases[of p "m -- n"], simp_all)
      apply(rule adiff_adiff_left_nat[symmetric], simp+)
      using adiff_add_assoc6 add_commute_nat[OF n p] apply simp
      using adiff_add_assoc2[OF _ p n m, symmetric] apply (simp add: adiff_is_0_eq')
  apply(rule nat_leq_cases[OF n m], simp_all)
    apply(rule nat_leq_cases[of p "m -- n"], simp_all)
    using adiff_add_assoc5[symmetric] add_commute_nat[OF n p] apply simp
    using adiff_add_assoc3[symmetric] add_commute_nat[OF n p] apply simp
    using adiff_add_assoc2[symmetric] add_commute_nat[OF n p] apply simp
done

lemma int_add_assoc4:
  assumes m: "m \<in> Nat" and n: "n \<in> Nat" and p: "p \<in> Nat"
  shows "-.m + (n + p) = (-.m + n) + p"
using assms add_commute_int[of "-.m" "n + p"] add_commute_int[of "-.m" n] apply simp
apply(rule nat_leq_cases[of m "n + p" ], simp_all)
  apply(rule nat_leq_cases[OF m n], simp_all)
    apply(rule adiff_add_assoc2, simp+)
    apply(simp add: add_commute_int[of "-.(m -- n)" p])
    apply(rule nat_leq_cases[of "m -- n" p], simp_all)
      apply(simp only: add_commute_nat[of n p])
      apply(simp only: adiff_add_assoc3[symmetric])
      apply(simp only: add_commute_nat[of n p])
      apply(simp only: adiff_add_assoc5[symmetric])
  apply(rule nat_leq_cases[OF m n], simp_all)
    apply(simp only: add_commute_nat[of n p])
    apply(rule adiff_add_assoc7, simp_all)
    apply(simp add: add_commute_int[of "-.(m -- n)" p])
    apply(rule nat_leq_cases[of "m -- n" p], simp+)
      apply(simp only: add_commute_nat[of n p])
      apply(simp only: adiff_add_assoc6[symmetric])
      apply(simp only: add_commute_nat[of n p])
        apply(simp add: add_commute_nat[of p n])
	apply(rule adiff_adiff_left_nat[symmetric], simp+)
done

lemma int_add_assoc5:
  assumes m: "m \<in> Nat" and n: "n \<in> Nat" and p: "p \<in> Nat"
  shows "-.m + (n + -.p) = -.m + n + -.p"
using assms
apply(simp add: add_commute_int[of "-.m" "n + -.p"] add_commute_int[of "-.m" n])
apply(rule nat_leq_cases[OF p n], simp_all)
  apply(rule nat_leq_cases[of m "n -- p"], simp+)
    apply(rule nat_leq_cases[of m n], simp+)
      apply(rule nat_leq_cases[of p "n -- m"], simp_all)
	apply(rule adiff_commute_nat[OF n p m])
	apply(rule adiff_add_assoc8, simp+)
	using nat_leq_trans[of n m "n -- p"] apply simp
	using leq_adiff_right_imp_0[OF _ _ n p] nat_leq_antisym[of m n] apply simp
    apply(rule nat_leq_cases[OF m n], simp_all)
      apply(rule nat_leq_cases[of p "n -- m"], simp_all)
	apply(rule adiff_add_assoc8[symmetric], simp_all)
	using leq_adiff_left_add_right[OF _ p n m]
	  add_commute_nat[OF p m]
	  apply(simp add: adiff_add_assoc3)
	  apply(simp add: adiff_add_assoc4)
    apply(rule nat_leq_cases[of m n], simp_all)
      apply(rule nat_leq_cases[of p "n -- m"], simp+)
	using nat_leq_trans[of n p "n -- m"] apply simp
	using leq_adiff_right_imp_0[OF _ _ n m] apply simp
	using nat_leq_antisym[of n p] apply simp
	apply(rule minusInj, simp)
	apply(rule adiff_add_assoc4[symmetric], simp+)
	apply(simp add: adiff_add_assoc2[symmetric])
	apply(simp add: add_commute_nat)
done

lemma int_add_assoc6:
  assumes m: "m \<in> Nat" and n: "n \<in> Nat" and p: "p \<in> Nat"
  shows "-.m + (-.n + p) = -.(m + n) + p"
using assms
  add_commute_int[of "-.n" p]
  add_commute_int[of "-.m" "p + -.n"]
  add_commute_int[of "-.(m + n)" p] apply simp
apply(rule nat_leq_cases[OF n p], simp_all)
  apply(rule nat_leq_cases[of m "p -- n"], simp+)
    apply(rule nat_leq_cases[of "m + n" p], simp+)
      apply(simp only: add_commute_nat[of m n])
      apply(rule adiff_adiff_left_nat, simp_all)
      apply(simp only: minus_sym[symmetric])
      apply(rule adiff_add_assoc5, simp_all)
    apply(rule nat_leq_cases[of "m + n" p], simp_all)
      apply(simp only: minus_sym)
      apply(rule adiff_add_assoc6, simp_all)
      apply(rule adiff_add_assoc3, simp_all)
    apply(rule nat_leq_cases[of "m + n" p], simp_all)
      apply(simp only: minus_sym)
      apply(rule adiff_add_assoc7[symmetric], simp_all)
      apply(simp add: add_commute_nat[of "n -- p" m])
      apply(rule adiff_add_assoc[symmetric], simp+)
done

lemma add_assoc_int:
  assumes m: "m \<in> Int" and n: "n \<in> Int" and p: "p \<in> Int"
  shows "m + (n + p) = (m + n) + p"
using m n p
by (rule intCases3,
    auto simp: add_assoc_nat int_add_assoc1 int_add_assoc2 int_add_assoc3
               int_add_assoc4 int_add_assoc5 int_add_assoc6)

text \<open> Minus sign distributes over addition \<close>

lemma minus_distrib_pn_int [simp]:
  "m \<in> Nat \<Longrightarrow> n \<in> Nat \<Longrightarrow> -.(m + -.n) = -.m + n"
apply(simp add: add_commute_int[of "-.m" n])
apply(rule nat_leq_cases[of n m], simp_all)
done

lemma minus_distrib_np_int [simp]:
  "m \<in> Nat \<Longrightarrow> n \<in> Nat \<Longrightarrow> -.(-.m + n) = m + -.n"
by(simp add: add_commute_int)

lemma int_add_minus_distrib [simp]:
  assumes m: "m \<in> Int" and n: "n \<in> Int"
  shows "-.(m + n) = -.m + -.n"
by (rule intCases2[OF m n], simp_all)


subsection \<open> Multiplication of integers \<close>

axiomatization where
  int_mult_pn_def: "\<lbrakk>a \<in> Nat; b \<in> Nat\<rbrakk> \<Longrightarrow> a * -.b = -.(a * b)"
and
  int_mult_np_def: "\<lbrakk>a \<in> Nat; b \<in> Nat\<rbrakk> \<Longrightarrow> -.a * b = -.(a * b)"
and
  int_mult_nn_def [simp]: "\<lbrakk>a \<in> Nat; b \<in> Nat\<rbrakk> \<Longrightarrow> -.a * -.b = a * b"

lemmas int_mult_def = int_mult_pn_def int_mult_np_def (*int_mult_nn_def*)

text \<open> Closure \<close>

lemma multIsInt [simp]: "\<lbrakk>a \<in> Int; b \<in> Int\<rbrakk> \<Longrightarrow> a * b \<in> Int"
by (rule intCases2[of a b], simp_all add: int_mult_def)

text \<open> Neutral element \<close>

lemma mult_0_right_int [simp]: "a \<in> Int \<Longrightarrow> a * 0 = 0"
by (rule intCases[of a], simp_all add: int_mult_np_def)

lemma mult_0_left_int [simp]: "a \<in> Int \<Longrightarrow> 0 * a = 0"
by (rule intCases[of a], simp_all add: int_mult_pn_def)

text \<open> Commutativity \<close>

lemma mult_commute_int: "\<lbrakk>a \<in> Int; b \<in> Int\<rbrakk> \<Longrightarrow> a * b = b * a"
by (rule intCases2[of a b], simp_all add: int_mult_def mult_commute_nat)

text \<open> Identity element \<close>

lemma mult_1_right_int [simp]: "a \<in> Int \<Longrightarrow> a * 1 = a"
by (rule intCases[of a], simp_all add: int_mult_def)

lemma mult_1_left_int [simp]: "a \<in> Int \<Longrightarrow> 1 * a = a"
by (rule intCases[of a], simp_all add: int_mult_def)

text \<open> Associativity \<close>

lemma mult_assoc_int:
  assumes m: "m \<in> Int" and n: "n \<in> Int" and p: "p \<in> Int"
  shows "m * (n * p) = (m * n) * p"
by(rule intCases3[OF m n p], simp_all add: mult_assoc_nat int_mult_def)

text \<open> Distributivity \<close>

lemma ppn_distrib_left_nat: (* ppn stands for m=positive, n=positive, p=negative *)
  assumes m: "m \<in> Nat" and n: "n \<in> Nat" and p: "p \<in> Nat"
  shows "m * (n + -.p) = m * n + -.(m * p)"
apply(rule nat_leq_cases[OF p n])
  apply(rule nat_leq_cases[of "m * p" "m * n"])
  using assms apply(simp_all add: adiff_mult_distrib2_nat int_mult_def)
done

lemma npn_distrib_left_nat:
  assumes m: "m \<in> Nat" and n: "n \<in> Nat" and p: "p \<in> Nat"
  shows "-.m * (n + -.p) = -.(m * n) + m * p"
using assms apply (simp add: add_commute_int[of "-.(m * n)" "m * p"])
apply(rule nat_leq_cases[OF p n])
  apply(rule nat_leq_cases[of "m * p" "m * n"], simp_all)
    apply (auto simp: adiff_mult_distrib2_nat int_mult_def dest: nat_leq_antisym)
done

lemma nnp_distrib_left_nat:
  assumes m: "m \<in> Nat" and n: "n \<in> Nat" and p: "p \<in> Nat"
  shows "-.m * (-.n + p) = m * n + -.(m * p)"
using assms apply (simp add: add_commute_int[of "-.n" p])
apply(rule nat_leq_cases[OF p n])
  apply(rule nat_leq_cases[of "m * p" "m * n"], simp_all)
    apply (auto simp: adiff_mult_distrib2_nat int_mult_def dest: nat_leq_antisym)
done

lemma distrib_left_int:
  assumes m: "m \<in> Int" and n: "n \<in> Int" and p: "p \<in> Int"
  shows "m * (n + p) = (m * n + m * p)"
apply(rule intCases3[OF m n p],
  simp_all only: int_mult_def int_add_nn_def int_mult_nn_def addIsNat)
      apply(rule add_mult_distrib_left_nat, assumption+)
      apply(rule ppn_distrib_left_nat, assumption+)
      apply(simp add: add_commute_int, rule ppn_distrib_left_nat, assumption+)
      apply(simp only: int_add_nn_def multIsNat add_mult_distrib_left_nat)+
      apply(rule npn_distrib_left_nat, assumption+)
      apply(rule nnp_distrib_left_nat, assumption+)
      apply(simp only: add_mult_distrib_left_nat)
done

lemma pnp_distrib_right_nat:
  assumes m: "m \<in> Nat" and n: "n \<in> Nat" and p: "p \<in> Nat"
  shows "(m + -.n) * p = m * p + -.(n * p)"
apply(rule nat_leq_cases[OF n m])
  apply(rule nat_leq_cases[of "n * p" "m * p"])
  using assms apply(simp_all add: adiff_mult_distrib_nat int_mult_def)
done

lemma pnn_distrib_right_nat:
  assumes m: "m \<in> Nat" and n: "n \<in> Nat" and p: "p \<in> Nat"
  shows "(m + -.n) * -.p = -.(m * p) + n * p"
using assms apply (simp add: add_commute_int[of "-.(m * p)" "n * p"])
apply(rule nat_leq_cases[OF n m])
  apply(rule nat_leq_cases[of "n * p" "m * p"])
  apply (auto simp: adiff_mult_distrib_nat int_mult_def dest: nat_leq_antisym)
done

lemma npn_distrib_right_nat:
  assumes m: "m \<in> Nat" and n: "n \<in> Nat" and p: "p \<in> Nat"
  shows "(-.m + n) * -.p = m * p + -.(n * p)"
using assms apply (simp add: add_commute_int[of "-.m" n])
apply(rule nat_leq_cases[OF n m])
  apply(rule nat_leq_cases[of "n * p" "m * p"])
  apply (auto simp: adiff_mult_distrib_nat int_mult_def dest: nat_leq_antisym)
done

lemma distrib_right_int:
  assumes m: "m \<in> Int" and n: "n \<in> Int" and p: "p \<in> Int"
  shows "(m + n) * p = (m * p + n * p)"
apply(rule intCases3[OF m n p],
  simp_all only: int_mult_def int_add_nn_def int_mult_nn_def addIsNat)
      apply(rule add_mult_distrib_right_nat, assumption+)
      apply(simp only: int_add_nn_def multIsNat add_mult_distrib_right_nat)
      apply(rule pnp_distrib_right_nat, assumption+)
      apply(rule pnn_distrib_right_nat, assumption+)
      apply(simp add: add_commute_int, rule pnp_distrib_right_nat, assumption+)
      apply(rule npn_distrib_right_nat, assumption+)
      apply(simp only: int_add_nn_def multIsNat add_mult_distrib_right_nat)
      apply(simp only: add_mult_distrib_right_nat)
done

text \<open> Minus sign distributes over multiplication \<close>

lemma minus_mult_left_int:
  assumes m: "m \<in> Int" and n: "n \<in> Int"
  shows "-.(m * n) = -.m * n"
by (rule intCases2[OF m n], simp_all add: int_mult_def)

lemma minus_mult_right_int:
  assumes m: "m \<in> Int" and n: "n \<in> Int"
  shows "-.(m * n) = m * -.n"
by (rule intCases2[OF m n], simp_all add: int_mult_def)


subsection \<open> Difference of integers \<close>

text \<open>
  Difference over integers is simply defined as addition of the complement.
  Note that this difference, noted @{text "-"}, is different from the
  difference over natural numbers, noted @{text "--"}, even for two natural
  numbers, because the latter cuts off at $0$.
\<close>

definition diff          (infixl "-" 65)
where int_diff_def: "\<lbrakk>m \<in> Int; n \<in> Int\<rbrakk> \<Longrightarrow> m - n = m + -.n"

lemma diffIsInt [simp]:  (* -- Closure *)
  "\<lbrakk>m \<in> Int; n \<in> Int\<rbrakk> \<Longrightarrow> m - n \<in> Int"
by (simp add: int_diff_def)

lemma diff_neg_is_add [simp]: "\<lbrakk>m \<in> Int; n \<in> Int\<rbrakk> \<Longrightarrow> m - -.n = m + n"
by (simp add: int_diff_def)

lemma diff_0_right_int [simp]: "m \<in> Int \<Longrightarrow> m - 0 = m"
by (simp add: int_diff_def)

lemma diff_0_left_int [simp]: "n \<in> Int \<Longrightarrow> 0 - n = -.n"
by (simp add: int_diff_def)

lemma diff_self_eq_0_int [simp]: "m \<in> Int \<Longrightarrow> m - m = 0"
by (simp add: int_diff_def)

lemma neg_diff_is_diff [simp]: "\<lbrakk>m \<in> Int; n \<in> Int\<rbrakk> \<Longrightarrow> -.(m - n) = n - m"
using assms by (simp add: int_diff_def add_commute_int)

lemma diff_nat_is_add_neg: "\<lbrakk>m \<in> Nat; n \<in> Nat\<rbrakk> \<Longrightarrow> m - n = m + -.n"
by (simp add: int_diff_def)

(**
lemma diff_neg_nat_is_add [simp]: "\<lbrakk>m \<in> Nat; n \<in> Nat\<rbrakk> \<Longrightarrow> m - -.n = m + n"
by simp
**)

end
