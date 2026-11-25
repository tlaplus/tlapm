(*  Title:      TLA+/IntegerDivision.thy
    Author:     Stephan Merz, Inria Nancy
    Copyright (C) 2009-2025  INRIA and Microsoft Corporation
    License:    BSD
    Version:    Isabelle2025
*)

section \<open> The division operators div and mod on the integers \<close>

theory IntegerDivision
imports IntegerArithmetic
begin

subsection \<open> The divisibility relation \<close>

definition dvd          (infixl "dvd" 50)
where "a \<in> Int \<Longrightarrow> b \<in> Int \<Longrightarrow> b dvd a \<equiv> (\<exists>k \<in> Int : a = b * k)"

lemma boolify_dvd [simp]:
  assumes "a \<in> Int" and "b \<in> Int"
  shows "boolify(b dvd a) = (b dvd a)"
using assms by (simp add: dvd_def)

lemma dvdIsBool [intro!,simp]:
  assumes a: "a \<in> Int" and b: "b \<in> Int"
  shows "isBool(b dvd a)"
using assms by (simp add: dvd_def)

lemma [intro!]:
  "\<lbrakk>isBool(P); isBool(a dvd b); (a dvd b) \<Leftrightarrow> P\<rbrakk> \<Longrightarrow> (a dvd b) = P"
  "\<lbrakk>isBool(P); isBool(a dvd b); P \<Leftrightarrow> (a dvd b)\<rbrakk> \<Longrightarrow> P = (a dvd b)"
by auto

lemma dvdI [intro]:
  assumes a: "a \<in> Int" and b: "b \<in> Int" and k: "k \<in> Int"
  shows "a = b * k \<Longrightarrow> b dvd a"
unfolding dvd_def[OF a b] using k by blast

lemma dvdE [elim]:
  assumes "b dvd a" and "a \<in> Int" and "b \<in> Int"
  shows "(\<And>k. \<lbrakk>k \<in> Int; a = b * k\<rbrakk> \<Longrightarrow> P) \<Longrightarrow> P"
using assms by (auto simp: dvd_def)

lemma dvd_refl [iff]:
  assumes a: "a \<in> Int"
  shows "a dvd a"
proof -
  from a have "a = a*1" by simp
  with a show ?thesis by blast
qed

lemma dvd_trans [trans]:
  assumes a: "a \<in> Int" and b: "b \<in> Int" and c: "c \<in> Int"
    and 1: "a dvd b" and 2: "b dvd c"
  shows "a dvd c"
proof -
  from a b 1 obtain k where k: "k \<in> Int" and "b = a * k" by blast
  moreover
  from b c 2 obtain l where l: "l \<in> Int" and "c = b * l" by blast
  ultimately have h: "c = a * (k * l)"
    using a b c by (simp add: times_assoc)
  thus ?thesis using a c k l by blast
qed

lemma dvd_0_left_iff [simp]:
  assumes "a \<in> Int"
  shows "(0 dvd a) = (a = 0)"
using assms by auto

lemma dvd_0_right [iff]:
  assumes a: "a \<in> Int" shows "a dvd 0"
using assms by force

lemma one_dvd [iff]:
  assumes a: "a \<in> Int"
  shows "1 dvd a"
using assms by force

lemma dvd_mult (*[simp]*):
  assumes dvd: "a dvd c" and a: "a \<in> Int" and b: "b \<in> Int" and c: "c \<in> Int"
  shows "a dvd (b * c)"
proof -
  from dvd a c obtain k where k: "k \<in> Int" and "c = a*k" by blast
  with a b c have "b*c = a * (b*k)" by (simp add: times_left_commute)
  with a b c k show ?thesis by blast
qed

lemma dvd_mult2 (*[simp]*):
  assumes dvd: "a dvd b" and a: "a \<in> Int" and b: "b \<in> Int" and c: "c \<in> Int"
  shows "a dvd (b * c)"
using times_commute[OF b c] dvd_mult[OF dvd a c b] by simp

lemma dvd_triv_right [iff]:
  assumes a: "a \<in> Int" and b: "b \<in> Int"
  shows "a dvd (b * a)"
using assms by (intro dvd_mult) simp+

lemma dvd_triv_left [iff]:
  assumes a: "a \<in> Int" and b: "b \<in> Int"
  shows "a dvd a * b"
using assms by (intro dvd_mult2) simp+

lemma mult_dvd_mono:
  assumes a: "a \<in> Int" and b: "b \<in> Int" and c: "c \<in> Int" and d: "d \<in> Int"
    and 1: "a dvd b" and 2: "c dvd d"
  shows "(a * c) dvd (b * d)"
proof -
  from a b 1 obtain b' where b': "b = a * b'" "b' \<in> Int" by blast
  from c d 2 obtain d' where d': "d = c * d'" "d' \<in> Int" by blast
  with b' a b c d
    times_assoc[of a b' "c * d'"]
    times_left_commute[of b' c d']
    times_assoc[of a c "b' * d'"]
  have "b * d = (a * c) * (b' * d')" by simp
  with a c b' d' show ?thesis by blast
qed

lemma dvd_mult_left:
  assumes a: "a \<in> Int" and b: "b \<in> Int" and c: "c \<in> Int"
    and h: "a * b dvd c"
  shows "a dvd c"
proof -
  from h a b c obtain k where k: "k \<in> Int" "c = a*(b*k)"
    by (auto simp add: times_assoc)
  with a b c show ?thesis by blast
qed

lemma dvd_mult_right:
  assumes a: "a \<in> Int" and b: "b \<in> Int" and c: "c \<in> Int" and h: "a*b dvd c"
  shows "b dvd c"
proof -
  from h a b c have "b*a dvd c" by (simp add: times_ac)
  with b a c show ?thesis by (rule dvd_mult_left)
qed

lemma dvd_0_left:
  assumes "a \<in> Int"
  shows "0 dvd a \<Longrightarrow> a = 0"
  using assms by simp

lemma dvd_add [iff]:
  assumes a: "a \<in> Int" and b: "b \<in> Int" and c: "c \<in> Int"
    and 1: "a dvd b" and 2: "a dvd c"
  shows "a dvd (b + c)"
proof -
  from a b 1 obtain b' where b': "b' \<in> Int" "b = a * b'" by blast
  from a c 2 obtain c' where c': "c' \<in> Int" "c = a * c'" by blast
  from a b c b' c'
  have "b + c = a * (b' + c')" by (simp add: add_times_distrib_left)
  with a b' c' show ?thesis by blast
qed

subsection \<open> Division and modulus on @{const Int} \<close>

text \<open>
  \tlaplus{} defines integer division only for the case
  where the divisor is positive. Two different extensions
  are commonly introduced for negative divisors, and we 
  leave this case undefined in order to avoid confusion.
\<close>

definition div       (infixr "div" 70)
where int_div_def: "\<lbrakk>a \<in> Int; b \<in> Int\<rbrakk> \<Longrightarrow> 
      a div b \<equiv> CHOOSE q \<in> Int : \<exists>r \<in> 0 .. (b-1) : a = b * q + r"

definition mod       (infixr "%" 70)
where "a % b \<equiv> a - b * (a div b)"

lemma div_exists:
  assumes a: "a \<in> Int" and b: "b \<in> Int" "0 < b"
  shows "\<exists>q \<in> Int : \<exists>r \<in> 0 .. (b-1) : a = b * q + r"
using a proof induct
  case 0
  from b have "0 = b * 0 + 0" "0 \<in> 0 .. (b-1)" by simp+
  thus ?case by blast
next
  case (pos n)
  then obtain q r where qr: "q \<in> Int" "r \<in> 0 .. (b-1)" "n = b * q + r"
    by blast
  show ?case
  proof (cases "r = b-1")
    case True
    with \<open>n \<in> Nat\<close> b qr 
    have "succ[n] = b * succ[q] + 0" "0 \<in> 0 .. (b-1)"
      by simp+
    with \<open>q \<in> Int\<close> show ?thesis by blast
  next
    case False
    with b qr 
    have "succ[r] \<in> 0 .. (b-1)" "succ[n] = b * q + succ[r]"
      by (auto simp: less_def)
    with \<open>q \<in> Int\<close> show ?thesis by blast
  qed
next
  case (neg n)
  then obtain q r where qr: "q \<in> Int" "r \<in> 0 .. (b-1)" "-n = b * q + r"
    by blast
  show ?case
  proof (cases "r = 0")
    case True
    with \<open>n \<in> Nat\<close> b qr 
    have "-succ[n] = b * pred[q] + (b - 1)" "b-1 \<in> 0 .. (b-1)"
      by (simp add: uminusSucc[of n])+
    with \<open>q \<in> Int\<close> show ?thesis by blast
  next
    case False
    with b qr \<open>n \<in> Nat\<close>
    have "pred[r] \<in> 0 .. (b-1)" "-succ[n] = b * q + pred[r]"
      by (auto simp: uminusSucc[of n])
    with \<open>q \<in> Int\<close> show ?thesis by blast
  qed
qed

lemma div_mod_unique:
  assumes qr: "a = b * q + r" "q \<in> Int" "r \<in> 0 .. (b-1)" 
      and qr': "a = b * q' + r'" "q' \<in> Int" "r' \<in> 0 .. (b-1)"
      and ab: "a \<in> Int" "b \<in> Int" "0 < b"
  shows "q' = q" "r' = r"
proof -
  {
    fix x x' y y'
    assume xy: "x \<in> Int" "x' \<in> Int" "y \<in> Nat" "y' \<in> Nat"
       and y': "y' < b"
       and eq: "b * x + y = b * x' + y'"
    have "x \<le> x'"
    proof (rule contradiction)
      assume "\<not>(x \<le> x')"
      with xy obtain k where k: "k \<in> Nat" "x = succ[x' + k]"
        by (auto dest: int_less_imp_succ_add)
      with xy ab eq have "b*x' + (b*k + b + y) = b*x' + y'"
        by (simp add: add_times_distrib_left add_assoc)
      with xy ab k have "b*k + b + y = y'" by simp
      with xy ab k y' have "(b*k + y) + b < b" by (simp add: add_ac)
      with xy ab k add_less_right_mono[of "(b*k + y) + b" "b" "-b"]
      have "b*k + y < 0" by simp
      moreover
      from xy ab k times_leq_right_pos_mono[of "0" "b" "k"]
      have "0 \<le> b*k + y" by (simp add: less_def)
      ultimately show "FALSE"
        using xy ab k by simp
    qed
  }
  from this[of q q' r r'] this[of q' q r' r] assms
  show 1: "q' = q" by (auto dest: int_leq_antisym)
  with add_right_diff_left[of a "b*q" r] add_right_diff_left[of a "b*q'" r'] assms
  show "r' = r" by simp
qed

lemma div_type [iff]:
  assumes ab: "a \<in> Int" "b \<in> Int" and "0 < b"
  shows "a div b \<in> Int"
  using div_exists[OF assms] unfolding int_div_def[OF ab]
  by (rule bChooseI2)

lemma mod_type [iff]:
  assumes "a \<in> Int" and "b \<in> Int" and "0 < b"
  shows "a % b \<in> Int"
  using assms unfolding mod_def by simp

lemma mod_range:
  assumes ab: "a \<in> Int" "b \<in> Int" and "0 < b"
  shows "a % b \<in> 0 .. (b-1)"
proof -
  from assms have "a div b \<in> Int" by simp
  from div_exists[OF assms]
  have "\<exists>r \<in> 0 .. (b-1) : a = b * (a div b) + r"
    unfolding int_div_def[OF ab] by (rule bChooseI2)
  then obtain r where "r \<in> 0 .. (b-1)" "a = b * (a div b) + r"
    by blast
  with assms show ?thesis
    by (simp add: mod_def add_right_diff_left[of "a" "b * (a div b)" r])
qed

lemma mod_div_equality:
  assumes "a \<in> Int" and "b \<in> Int" and "0 < b"
  shows "(a % b) + b * (a div b) = a"
  using assms unfolding mod_def by simp 

lemma mod_div_equality2:
  assumes "a \<in> Int" and "b \<in> Int" and "0 < b"
  shows "b * (a div b) + (a % b) = a"
  using assms by (simp add: mod_div_equality add_commute)

lemma mod_div_equality3:
  assumes "a \<in> Int" and "b \<in> Int" and "0 < b"
  shows "(a div b) * b + (a % b) = a"
  using assms by (simp add: mod_div_equality2 times_commute)

lemma mod_div_equality4:
  assumes "a \<in> Int" and "b \<in> Int" and "0 < b"
  shows "(a % b) + (a div b) * b = a"
  using assms by (simp add: mod_div_equality times_commute)

lemma div_equal:
  assumes "a = b*q + r" and "a \<in> Int" and "b \<in> Int" and "0 < b"
      and "q \<in> Int" and "r \<in> 0 .. (b-1)"
  shows "a div b = q"
  using assms mod_div_equality2[of a b] mod_range[of a b]
        div_mod_unique[of a b q r "a div b" "a % b"]
  by auto

lemma mod_equal:
  assumes "a = b*q + r" and "a \<in> Int" and "b \<in> Int" and "0 < b"
      and "q \<in> Int" and "r \<in> 0 .. (b-1)"
  shows "a % b = r"
  using assms mod_div_equality2[of a b] mod_range[of a b]
        div_mod_unique[of a b q r "a div b" "a % b"]
  by auto


text \<open> ``Recursive'' laws about @{text div} and @{text "%"}. \<close>

lemma div_mod_nat_less_divisor:
  assumes "a \<in> 0 .. (b-1)" "b \<in> Int" "0 < b"
  shows "a div b = 0" "a % b = a"
proof -
  from assms have 1: "a = b*0 + a" by simp
  from 1[THEN div_equal] assms show "a div b = 0" 
    by blast
  from 1[THEN mod_equal] assms show "a % b = a" 
    by blast
qed

lemma div_is_zero_iff [simp]:
  assumes "a \<in> Int" and "b \<in> Int" and "0 < b"
  shows "(a div b = 0) = (a \<in> 0 .. (b-1))"
  using assms mod_div_equality2[of a b] mod_range[of a b]
  by (auto simp: div_mod_nat_less_divisor)

lemma mod_is_self_iff [simp]:
  assumes "a \<in> Int" and "b \<in> Int" and "0 < b"
  shows "(a % b = a) = (a \<in> 0 .. (b-1))"
  using assms mod_div_equality2[of a b] mod_range[of a b]
  by (auto simp: div_mod_nat_less_divisor)

lemma div_mod_minus_less_divisor:
  assumes "a \<in> (-b) .. (-1)" "b \<in> Int" "0 < b"
  shows "a div b = -1" "a % b = b+a"
proof -
  from assms have "0 \<le> b+a"
    using add_leq_left_mono[of "-b" "a" "b"] by simp
  moreover
  from assms have "b+a < b"
    using int_leq_pred_iff[of a 0] add_less_left_mono[of a 0 b]
    by (simp add: pred0)
  ultimately have 1: "b+a \<in> 0 .. (b-1)"
    using assms by simp
  from assms have 2: "a = b*(-1) + (b+a)" by (simp add: add_assoc)
  from 1 2[THEN div_equal] assms show "a div b = -1"
    by blast
  from 1 2[THEN mod_equal] assms show "a % b = b+a"
    by blast
qed

lemma div_is_minusone_iff [simp]:
  assumes "a \<in> Int" "b \<in> Int" "0 < b"
  shows "(a div b = -1) = (a \<in> (-b) .. (-1))"
proof -
  {
    assume "a div b = -1"
    with assms mod_div_equality2[of a b]
    have 1: "a = -b + (a % b)" by simp
    from assms mod_range[of a b] have "-b \<le> -b + (a % b)"
      by simp
    moreover
    from assms mod_range[of a b] have "-b + (a % b) < -b + b"
      by (intro add_leq_less_mono) simp+
    ultimately have "a \<in> (-b) .. (-1)"
      using assms 1 by simp
  }
  moreover
  {
    assume "a \<in> (-b) .. (-1)"
    with assms div_mod_minus_less_divisor[of a b] have "a div b = -1"
      by blast
  }
  ultimately show ?thesis
    using assms by blast
qed

lemma div_mod_plus_divisor1 [simp]:
  assumes "a \<in> Int" "b \<in> Int" "0 < b"
  shows "(a+b) div b = succ[a div b]" "(a+b) % b = a % b"
proof -
  from assms have "a = b * (a div b) + (a % b)"
    by (simp add: mod_div_equality2)
  with assms have "a+b = b * (a div b) + (a % b) + b"
    by simp
  with assms have 1: "a+b = b * succ[a div b] + (a % b)"
    by (simp add: add_ac)
  from 1[THEN div_equal] assms mod_range[of a b] 
  show "(a+b) div b = succ[a div b]" 
    by blast
  from 1[THEN mod_equal] assms mod_range[of a b] 
  show "(a+b) % b = a % b" 
    by blast
qed

lemma div_mod_plus_divisor2 [simp]:
  assumes "a \<in> Int" "b \<in> Int" "0 < b"
  shows "(b+a) div b = succ[a div b]" "(b+a) % b = a % b"
  using assms by (simp add: add_commute)+

lemma div_mod_minus_divisor1 [simp]:
  assumes "a \<in> Int" "b \<in> Int" "0 < b"
  shows "(a-b) div b = pred[a div b]" "(a-b) % b = a % b"
proof -
  from assms have "a = b * (a div b) + (a % b)"
    by (simp add: mod_div_equality2)
  with assms have "a-b = b * (a div b) + (a % b) - b"
    by simp
  with assms have 1: "a-b = b * pred[a div b] + (a % b)"
    by (simp add: add_right_commute)
  from 1[THEN div_equal] assms mod_range[of a b] 
  show "(a-b) div b = pred[a div b]" 
    by blast
  from 1[THEN mod_equal] assms mod_range[of a b] 
  show "(a-b) % b = a % b" 
    by blast
qed

lemma div_mod_minus_divisor2 [simp]:
  assumes "a \<in> Int" "b \<in> Int" "0 < b"
  shows "(-b + a) div b = pred[a div b]" "(-b + a) % b = a % b"
  using assms by (simp add: add_commute)+


subsection \<open> Facts about @{text div} and @{text "%"} \<close>

lemma div_times_divisor1 [simp]:
  assumes a: "a \<in> Int" and b: "b \<in> Int" "0 < b" and c: "c \<in> Int"
  shows "(a + c*b) div b = c + (a div b)"
  using c by (induct) (simp add: a b add_assoc)+

lemma div_times_divisor2 [simp]:
  assumes a: "a \<in> Int" and b: "b \<in> Int" "0 < b" and c: "c \<in> Int"
  shows "(a + b*c) div b = c + (a div b)"
  using c by (induct) (simp add: a b add_assoc)+

lemma div_times_divisor3 [simp]:
  assumes a: "a \<in> Int" and b: "b \<in> Int" "0 < b" and c: "c \<in> Int"
  shows "(b*c + a) div b = c + (a div b)"
  using assms by (simp add: add_commute)

lemma div_times_divisor4 [simp]:
  assumes a: "a \<in> Int" and b: "b \<in> Int" "0 < b" and c: "c \<in> Int"
  shows "(c*b + a) div b = c + (a div b)"
  using assms by (simp add: add_commute)

lemma mod_times_divisor1 [simp]:
  assumes a: "a \<in> Int" and b: "b \<in> Int" "0 < b" and c: "c \<in> Int"
  shows "(a + c*b) % b = a % b"
  using c by (induct) (simp add: a b add_assoc)+

lemma mod_times_divisor2 [simp]:
  assumes a: "a \<in> Int" and b: "b \<in> Int" "0 < b" and c: "c \<in> Int"
  shows "(a + b*c) % b = a % b"
  using c by (induct) (simp add: a b add_assoc)+

lemma mod_times_divisor3 [simp]:
  assumes "a \<in> Int" and "b \<in> Int" "0 < b" and "c \<in> Int"
  shows "(b*c + a) % b = a % b"
  using assms by (simp add: add_commute)

lemma mod_times_divisor4 [simp]:
  assumes "a \<in> Int" and "b \<in> Int" "0 < b" and "c \<in> Int"
  shows "(c*b + a) % b = a % b"
  using assms by (simp add: add_commute)

lemma times_div_self1 [simp]:
  assumes "a \<in> Int" "b \<in> Int" "0 < b"
  shows "(a*b) div b = a"
  using assms div_times_divisor1[of 0 b a] by simp

lemma times_div_self2 [simp]:
  assumes "a \<in> Int" "b \<in> Int" "0 < b"
  shows "(b*a) div b = a"
  using assms by (simp add: times_commute)

lemma times_mod_self1 [simp]:
  assumes "a \<in> Int" "b \<in> Int" "0 < b"
  shows "(a*b) % b = 0"
  using assms mod_times_divisor1[of 0 b a] by simp

lemma times_mod_self2 [simp]:
  assumes "a \<in> Int" "b \<in> Int" "0 < b"
  shows "(b*a) % b = 0"
  using assms by (simp add: times_commute)

lemma div_mod_by_one [simp]:
  "a \<in> Int \<Longrightarrow> a div 1 = a"
  "a \<in> Int \<Longrightarrow> a % 1 = 0"
  using times_div_self1[of a 1] times_mod_self1[of a 1] by simp+

lemma div_mod_by_self [simp]:
  "\<lbrakk>a \<in> Int; 0 < a\<rbrakk> \<Longrightarrow> a div a = 1"
  "\<lbrakk>a \<in> Int; 0 < a\<rbrakk> \<Longrightarrow> a % a = 0"
  using times_div_self1[of 1 a] times_mod_self1[of 1 a] by simp+

lemma mod_div_same [simp]:
  assumes "a \<in> Int" and "b \<in> Int" and "0 < b"
  shows "(a % b) div b = 0"
  using assms mod_range[of a b] by simp

lemma mod_mod_same [simp]:
  assumes "a \<in> Int" and "b \<in> Int" and "0 < b"
  shows "(a % b) % b = a % b"
  using assms mod_times_divisor1[of "a % b" "b" "a div b"] mod_range[of a b]
  by simp

lemma div_mod_decomposition:
  assumes a: "a \<in> Int" and b: "b \<in> Int" "0 < b"
  obtains q r where "q \<in> Int" and "r \<in> 0 .. (b-1)"
      and "q = a div b" and "r = a % b" and "a = b*q + r"
  using assms mod_div_equality2[of a b, THEN sym] mod_range[of a b] 
  by blast


subsection \<open>Further arithmetic laws for division and modulus\<close>

lemma add_div:
  assumes "a \<in> Int" and "b \<in> Int" and "c \<in> Int" and "0 < c"
  shows "(a + b) div c = a div c + b div c + (a%c + b%c) div c"
proof -
  from assms have "a + b = (c * (a div c) + a%c) + (c * (b div c) + b%c)"
    by (simp add: mod_div_equality2)
  with assms have "a + b = c * (a div c + b div c) + (a%c + b%c)"
    by (simp add: add_times_distrib_left add_commute add_left_commute)
  with assms show ?thesis by simp
qed

lemma add_mod:
  assumes "a \<in> Int" and "b \<in> Int" and "c \<in> Int" and "0 < c"
  shows "(a + b) % c = ((a % c) + (b % c)) % c"
proof -
  from assms have "(a%c + b%c) % c = (c * (a div c + b div c) + (a%c + b%c)) % c"
    by simp
  moreover
  from assms have "c * (a div c + b div c) + (a%c + b%c)
       = (c * (a div c) + a%c) + (c * (b div c) + b%c)"
    by (simp add: add_times_distrib_left add_commute add_left_commute)
  with assms have "c * (a div c + b div c) + (a%c + b%c) = a+b"
    by (simp add: mod_div_equality2)
  ultimately show ?thesis by simp
qed

lemma times_div:
  assumes "a \<in> Int" and "b \<in> Int" and "c \<in> Int" and "0 < c"
  shows "(a * b) div c = a * (b div c) + (a div c) * (b%c) + ((a%c) * (b%c)) div c"
proof -
  from assms have "a * b = (c * (a div c) + a%c) * (c * (b div c) + b%c)"
    by (simp add: mod_div_equality2)
  also from assms 
  have "\<dots> = (c * (a div c) + a%c) * (c * (b div c)) + (c * (a div c) + a%c) * (b%c)"
    by (simp add: add_times_distrib_left)
  also from assms
  have "\<dots> = (c * (a div c) * (c * (b div c))
              + (a%c) * (c * (b div c)))
           + (c * (a div c) * (b%c) + (a%c) * (b%c))"
    by (simp add: add_times_distrib_right)
  also from assms
  have "\<dots> = (c * c * (a div c) * (b div c)
              + (a%c) * c * (b div c))
           + (c * (a div c) * (b%c) + (a%c) * (b%c))"
    by (simp add: times_assoc times_right_commute)
  also from assms
  have "\<dots> = (c * c * (a div c) + (a%c) * c) * (b div c)
           + (c * (a div c) * (b%c) + (a%c) * (b%c))"
    by (simp add: add_times_distrib_right)
  also from assms
  have "\<dots> = (c * c * (a div c) + c * (a%c)) * (b div c)
           + (c * (a div c) * (b%c) + (a%c) * (b%c))"
    by (simp add: times_commute)
  also from assms
  have "\<dots> = (c * (c * (a div c)) + c * (a%c)) * (b div c)
           + (c * ((a div c) * (b%c)) + (a%c) * (b%c))"
    by (simp add: times_assoc)
  also from assms
  have "\<dots> = (c * (c * (a div c) + (a%c))) * (b div c)
           + (c * ((a div c) * (b%c)) + (a%c) * (b%c))"
    by (simp add: add_times_distrib_left)
  finally have "a * b = c * (a * (b div c)) + (c * ((a div c) * (b%c)) + (a%c) * (b%c))"
    using assms mod_div_equality2[of a c]
    by (simp add: times_assoc)
  with assms have "(a * b) div c = a * (b div c) + (c * ((a div c) * (b%c)) + (a%c) * (b%c)) div c"
    by simp
  moreover
  from assms 
  have "(c * ((a div c) * (b%c)) + (a%c) * (b%c)) div c = (a div c) * (b%c) + ((a%c) * (b%c)) div c"
    by simp
  ultimately
  have "(a * b) div c = a * (b div c) + ((a div c) * (b%c) + ((a%c) * (b%c)) div c)"
    by simp
  with assms show ?thesis by (simp add: add_assoc)
qed

lemma times_mod:
  assumes "a \<in> Int" and "b \<in> Int" and "c \<in> Int" and "0 < c"
  shows "(a * b) % c = ((a % c) * (b % c)) % c"
proof -
  from assms
  have "((a % c) * (b % c)) % c
      = (c * ((a div c) * c * (b div c) + (a div c) * (b % c) + (a % c) * (b div c))
         + (a % c) * (b % c)) % c"
    by simp
  moreover
  from assms
  have "c * ((a div c) * c * (b div c) + (a div c) * (b % c) + (a % c) * (b div c))
        + (a % c) * (b % c)
        = (c * (a div c) + a % c) * (c * (b div c) + b % c)"
    by (simp add: add_times_distrib_left add_times_distrib_right 
                  times_commute times_left_commute 
                  add_commute add_left_commute)
  with assms
  have "c * ((a div c) * c * (b div c) + (a div c) * (b % c) + (a % c) * (b div c))
        + (a % c) * (b % c)
        = a * b"
    by (simp add: mod_div_equality2)
  ultimately show ?thesis by simp
qed

lemma uminus_div1:
  assumes "a \<in> Int" and "b \<in> Int" and "0 < b"
  shows "(-a) div b = -(a div b) + (-(a%b)) div b"
proof -
  from assms have "-a = -(b * (a div b) + a%b)"
    by (simp add: mod_div_equality2)
  with assms have "-a = b * (-(a div b)) - (a % b)"
    by simp
  with assms show ?thesis 
    by (simp del: times_uminus_right)
qed

lemma uminus_div2:
  assumes "a \<in> Int" and "b \<in> Int" and "0 < b"
  shows "(-a) div b = -(a div b) + (IF a%b = 0 THEN 0 ELSE -1)"
proof (cases "a % b = 0")
  case True
  with assms show ?thesis by (simp add: uminus_div1)
next
  case False
  with assms mod_range[of a b] have "-(a % b) \<in> (-b) .. (-1)"
    by auto
  with assms have "(-(a % b)) div b = -1"
    by (simp add: div_mod_minus_less_divisor)
  with assms False uminus_div1[of a b]
  show ?thesis by simp
qed

lemma uminus_mod1:
  assumes "a \<in> Int" and "b \<in> Int" and "0 < b"
  shows "(-a) % b = (-(a % b)) % b"
proof -
  from assms have "(-a) % b = (-(b * (a div b) + a % b)) % b"
    by (simp add: mod_div_equality2)
  moreover
  from assms have "-(b * (a div b) + a % b) = b * (-(a div b)) - a % b"
    by simp
  ultimately show ?thesis
    using assms mod_times_divisor3[of "-(a % b)" "b" "-(a div b)"]
    by simp
qed

lemma uminus_mod2:
  assumes "a \<in> Int" and "b \<in> Int" and "0 < b"
  shows "(-a) % b = (IF a % b = 0 THEN 0 ELSE b - (a%b))"
proof (cases "a % b = 0")
  case True
  with assms show ?thesis by (simp add: uminus_mod1)
next
  case False
  with assms mod_range[of a b] have "-(a % b) \<in> (-b) .. (-1)"
    by auto
  with assms have "(-(a % b)) % b = b - (a % b)"
    by (simp add: div_mod_minus_less_divisor)
  with assms uminus_mod1[of a b] False 
  show ?thesis by simp
qed


subsection \<open>Divisibility and @{text div} / @{text mod}\<close>

lemma dvd_is_mod0:
  assumes "a \<in> Int" and "b \<in> Int" and "0 < b"
  shows "(b dvd a) = (a % b = 0)"
  using assms mod_div_equality2[of a b] by auto

lemma dvd_times_div_self:
  assumes "b dvd a" and "a \<in> Int" and "b \<in> Int" and "0 < b"
  shows "b * (a div b) = a"
  using assms dvd_is_mod0[of a b] mod_div_equality2[of a b] by simp

lemma dvd_times_div_distrib:
  assumes dvd: "b dvd a" and a: "a \<in> Int" and b: "b \<in> Int" "0 < b" and c: "c \<in> Int"
  shows "c * (a div b) = (c*a) div b"
proof -
  from dvd a b obtain d where d: "d \<in> Int" "a = b*d" by auto
  with a b c have "c*a = b * (c*d)" by (simp add: times_left_commute)
  with a b c d show ?thesis by simp
qed

lemma dvd_mod_imp_dvd:
  assumes "a dvd (c % b)" and "a dvd b"
      and a: "a \<in> Int" and b: "b \<in> Int" "0 < b" and c: "c \<in> Int"
    shows "a dvd c"
proof -
  from assms have "a dvd ((c div b) * b + c % b)"
    by (simp add: dvd_mult)
  with a b c show ?thesis 
    by (simp add: mod_div_equality3)
qed

end
