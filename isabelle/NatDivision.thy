(*  Title:      TLA+/NatDivision.thy
    Author:     Hernan Vanzetto
    Copyright (C) 2009-2011  INRIA and Microsoft Corporation
    License:    BSD
    Version:    Isabelle2011-1
    Time-stamp: <2011-10-11 17:39:56 merz>
*)

section \<open> The division operators div and mod on Naturals \<close>

theory NatDivision
imports NatArith Tuples
begin

subsection \<open> The divisibility relation \<close>

definition dvd          (infixl "dvd" 50)
where "a \<in> Nat \<Longrightarrow> b \<in> Nat \<Longrightarrow> b dvd a \<equiv> (\<exists>k \<in> Nat : a = b * k)"

lemma boolify_dvd [simp]:
  assumes "a \<in> Nat" and "b \<in> Nat"
  shows "boolify(b dvd a) = (b dvd a)"
using assms by (simp add: dvd_def)

lemma dvdIsBool [intro!,simp]:
  assumes a: "a \<in> Nat" and b: "b \<in> Nat"
  shows "isBool(b dvd a)"
using assms by (simp add: dvd_def)

lemma [intro!]:
  "\<lbrakk>isBool(P); isBool(a dvd b); (a dvd b) \<Leftrightarrow> P\<rbrakk> \<Longrightarrow> (a dvd b) = P"
  "\<lbrakk>isBool(P); isBool(a dvd b); P \<Leftrightarrow> (a dvd b)\<rbrakk> \<Longrightarrow> P = (a dvd b)"
by auto

lemma dvdI [intro]:
  assumes a: "a \<in> Nat" and b: "b \<in> Nat" and k: "k \<in> Nat"
  shows "a = b * k \<Longrightarrow> b dvd a"
unfolding dvd_def[OF a b] using k by blast

lemma dvdE [elim]:
  assumes "b dvd a" and "a \<in> Nat" and "b \<in> Nat"
  shows "(\<And>k. \<lbrakk>k \<in> Nat; a = b * k\<rbrakk> \<Longrightarrow> P) \<Longrightarrow> P"
using assms by (auto simp add: dvd_def)

lemma dvd_refl [iff]:
  assumes a: "a \<in> Nat"
  shows "a dvd a"
proof -
  from a have "a = a*1" by simp
  with a show ?thesis by blast
qed

lemma dvd_trans [trans]:
  assumes a: "a \<in> Nat" and b: "b \<in> Nat" and c: "c \<in> Nat"
    and 1: "a dvd b" and 2: "b dvd c"
  shows "a dvd c"
proof -
  from a b 1 obtain k where k: "k \<in> Nat" and "b = a * k" by blast
  moreover
  from b c 2 obtain l where l: "l \<in> Nat" and "c = b * l" by blast
  ultimately have h:"c = a * (k * l)"
    using a b c by (simp add: mult_assoc_nat)
  thus ?thesis using a c k l by blast
qed

lemma dvd_0_left_iff [simp]:
  assumes "a \<in> Nat"
  shows "(0 dvd a) = (a = 0)"
using assms by force

lemma dvd_0_right [iff]:
  assumes a: "a \<in> Nat" shows "a dvd 0"
using assms by force

lemma one_dvd [iff]:
  assumes a: "a \<in> Nat"
  shows "1 dvd a"
using assms by force

lemma dvd_mult (*[simp]*):
  assumes dvd: "a dvd c" and a: "a \<in> Nat" and b: "b \<in> Nat" and c: "c \<in> Nat"
  shows "a dvd (b * c)"
proof -
  from dvd a c obtain k where k: "k \<in> Nat" and "c = a*k" by blast
  with a b c have "b*c = a * (b*k)" by (simp add: mult_left_commute_nat)
  with a b c k show ?thesis by blast
qed

lemma dvd_mult2 (*[simp]*):
  assumes dvd: "a dvd b" and a: "a \<in> Nat" and b: "b \<in> Nat" and c: "c \<in> Nat"
  shows "a dvd (b * c)"
using mult_commute_nat[OF b c] dvd_mult[OF dvd a c b] by simp

lemma dvd_triv_right [iff]:
  assumes a: "a \<in> Nat" and b: "b \<in> Nat"
  shows "a dvd (b * a)"
using assms by (intro dvd_mult, simp+)

lemma dvd_triv_left [iff]:
  assumes a: "a \<in> Nat" and b: "b \<in> Nat"
  shows "a dvd a * b"
using assms by (intro dvd_mult2, simp+)

lemma mult_dvd_mono:
  assumes a: "a \<in> Nat" and b: "b \<in> Nat" and c: "c \<in> Nat" and d: "d \<in> Nat"
    and 1: "a dvd b" and 2: "c dvd d"
  shows "(a * c) dvd (b * d)"
proof -
  from a b 1 obtain b' where b': "b = a * b'" "b' \<in> Nat" by blast
  from c d 2 obtain d' where d': "d = c * d'" "d' \<in> Nat" by blast
  with b' a b c d
    mult_assoc_nat[of a b' "c * d'"]
    mult_left_commute_nat[of b' c d']
    mult_assoc_nat[of a c "b' * d'"]
  have "b * d = (a * c) * (b' * d')" by simp
  with a c b' d' show ?thesis by blast
qed

lemma dvd_mult_left:
  assumes a: "a \<in> Nat" and b: "b \<in> Nat" and c: "c \<in> Nat"
    and h: "a * b dvd c"
  shows "a dvd c"
proof -
  from h a b c obtain k where k: "k \<in> Nat" "c = a*(b*k)"
    by (auto simp add: mult_assoc_nat)
  with a b c show ?thesis by blast
qed

lemma dvd_mult_right:
  assumes a: "a \<in> Nat" and b: "b \<in> Nat" and c: "c \<in> Nat" and h: "a*b dvd c"
  shows "b dvd c"
proof -
  from h a b c have "b*a dvd c" by (simp add: mult_ac_nat)
  with b a c show ?thesis by (rule dvd_mult_left)
qed

lemma dvd_0_left:
  assumes "a \<in> Nat"
  shows "0 dvd a \<Longrightarrow> a = 0"
using assms by simp

lemma dvd_add [iff]:
  assumes a: "a \<in> Nat" and b: "b \<in> Nat" and c: "c \<in> Nat"
    and 1: "a dvd b" and 2: "a dvd c"
  shows "a dvd (b + c)"
proof -
  from a b 1 obtain b' where b': "b' \<in> Nat" "b = a * b'" by blast
  from a c 2 obtain c' where c': "c' \<in> Nat" "c = a * c'" by blast
  from a b c b' c'
  have "b + c = a * (b' + c')" by (simp add: add_mult_distrib_left_nat)
  with a b' c' show ?thesis by blast
qed

subsection \<open> Division on @{const Nat} \<close>

text \<open>
  We define division and modulo over @{const Nat} by means
  of a characteristic relation with two input arguments
  @{term "m"}, @{term "n"} and two output arguments
  @{term "q"}(uotient) and @{term "r"}(emainder).

  The following definition works for natural numbers, but also for
  possibly negative integers. Obviously, the second disjunct cannot
  hold for natural numbers.
\<close>

definition divmod_rel where
  "divmod_rel(m,n,q,r) \<equiv> m = q * n + r
                       \<and> ((0 < n \<and> 0 \<le> r \<and> r < n) \<or> (n < 0 \<and> r \<le> 0 \<and> n < r))"

text \<open> @{const divmod_rel} is total if $n$ is non-zero. \<close>

lemma divmod_rel_ex:
  assumes m: "m \<in> Nat" and n: "n \<in> Nat" and pos: "0 < n"
  obtains q r where "q \<in> Nat" "r \<in> Nat" "divmod_rel(m,n,q,r)"
proof -
  have "\<exists>q,r \<in> Nat : m = q*n + r \<and> r < n"
  using m proof (induct)
    case 0
    from n pos have "0 = 0 * n + 0 \<and> 0 < n" by simp
    then show ?case by blast
  next
    fix m'
    assume m': "m' \<in> Nat" and ih: "\<exists>q, r \<in> Nat : m' = q*n + r \<and> r < n"
    from ih obtain q' r'
      where h1: "m' = q' * n + r'" and h2: "r' < n"
      and q': "q' \<in> Nat" and r': "r' \<in> Nat" by blast
    show "\<exists>q, r \<in> Nat : Succ[m'] = q * n + r \<and> r < n"
    proof (cases "Succ[r'] < n")
      case True
      from h1 h2 m' q' n r' have "Succ[m'] = q' * n + Succ[r']" by simp
      with True q' r' show ?thesis by blast
    next
      case False
      with n r' have "n \<le> Succ[r']" by (simp add: nat_not_less[simplified])
      with r' n h2 have "n = Succ[r']" by (intro nat_leq_antisym, simp+)
      with h1 m' q' r' have "Succ[m'] = Succ[q'] * n + 0" by (simp add: add_ac_nat)
      with pos q' show ?thesis by blast
    qed
  qed
  with pos that show ?thesis by (auto simp: divmod_rel_def)
qed

text \<open> @{const divmod_rel} has unique solutions in the natural numbers. \<close>
lemma divmod_rel_unique_div:
  assumes 1: "divmod_rel(m,n,q,r)" and 2: "divmod_rel(m,n,q',r')"
    and m: "m \<in> Nat" and n: "n \<in> Nat"
    and q: "q \<in> Nat" and r: "r \<in> Nat" and q': "q' \<in> Nat" and r': "r' \<in> Nat"
  shows "q = q'"
proof -
  from n 1 have pos: "0 < n" and mqr: "m = q*n+r" and rn: "r < n"
    by (auto simp: divmod_rel_def)
  from n 2 have mqr': "m = q'*n+r'" and rn': "r' < n"
    by (auto simp: divmod_rel_def)
  {
    fix x y x' y'
    assume nat: "x \<in> Nat" "y \<in> Nat" "x' \<in> Nat" "y' \<in> Nat"
      and eq: "x*n + y = x'*n + y'" and less: "y' < n"
    have "x \<le> x'"
    proof (rule contradiction)
      assume "\<not>(x \<le> x')"
      with nat have "x' < x" by (simp add: nat_not_leq[simplified])
      with nat obtain k where k: "k \<in> Nat" "x = Succ[x'+k]"
        by (auto simp: less_iff_Succ_add)
      with eq nat n have "x'*n + (k*n + n + y) = x'*n + y'"
        by (simp add: add_mult_distrib_right_nat add_assoc_nat)
      with nat k n have "k*n + n + y = y'" by simp
      with less k n nat have "(k*n + y) + n < n" by (simp add: add_ac_nat)
      with k n nat show "FALSE" by simp
    qed
  }
  from this[OF q r q' r'] this[OF q' r' q r] q q' mqr mqr' rn rn'
  show ?thesis by (intro nat_leq_antisym, simp+)
qed

lemma divmod_rel_unique_mod:
  assumes "divmod_rel(m,n,q,r)" and "divmod_rel(m,n,q',r')"
    and "m \<in> Nat" and "n \<in> Nat" and "q \<in> Nat" and "r \<in> Nat" and "q' \<in> Nat" and "r' \<in> Nat"
  shows "r = r'"
proof -
  from assms have "q = q'" by (rule divmod_rel_unique_div)
  with assms show ?thesis by (auto simp: divmod_rel_def)
qed

text \<open>
  We instantiate divisibility on the natural numbers by
  means of @{const divmod_rel}:
\<close>

definition divmodNat
where "divmodNat(m,n) \<equiv> CHOOSE z \<in> Nat \<times> Nat : divmod_rel(m,n,z[1],z[2])"

lemma divmodNatPairEx:
  assumes "m \<in> Nat" and "n \<in> Nat" and "0 < n"
  shows "\<exists>z \<in> Nat \<times> Nat : divmod_rel(m,n,z[1],z[2])"
proof -
  from assms obtain q r where "q \<in> Nat" "r \<in> Nat" "divmod_rel(m,n,q,r)"
    by (rule divmod_rel_ex)
  thus ?thesis unfolding two_def by force
qed

lemma divmodNatInNatNat:
  assumes m: "m \<in> Nat" and n: "n \<in> Nat" and pos: "0 < n"
  shows "divmodNat(m,n) \<in> Nat \<times> Nat"
unfolding divmodNat_def by (rule bChooseI2[OF divmodNatPairEx[OF assms]])

lemma divmodNat_divmod_rel [rule_format]:
  assumes m: "m \<in> Nat" and n: "n \<in> Nat" and pos: "0 < n"
  shows "z = divmodNat(m,n) \<Rightarrow> divmod_rel(m,n,z[1],z[2])"
unfolding divmodNat_def by (rule bChooseI2[OF divmodNatPairEx[OF assms]], auto)

lemma divmodNat_unique:
  assumes h: "divmod_rel(m,n,q,r)"
      and m: "m \<in> Nat" and n: "n \<in> Nat" and pos: "0 < n"
      and q: "q \<in> Nat" and r: "r \<in> Nat"
  shows "divmodNat(m,n) = \<langle>q,r\<rangle>"
unfolding divmodNat_def
proof (rule bChooseI2[OF divmodNatPairEx[OF m n pos]])
  fix z
  assume "z \<in> Nat \<times> Nat" and "divmod_rel(m,n,z[1],z[2])"
  with m n q r h show "z = \<langle>q,r\<rangle>"
    unfolding two_def
    by (auto elim!: inProdE elim: divmod_rel_unique_div divmod_rel_unique_mod)
qed

text \<open>
  We now define division and modulus over natural numbers.
\<close>

definition div       (infixr "div" 70)
where div_nat_def: "\<lbrakk>m \<in> Nat; n \<in> Nat\<rbrakk> \<Longrightarrow> m div n \<equiv> divmodNat(m,n)[1]"

definition mod       (infixr "mod" 70)
where mod_nat_def: "\<lbrakk>m \<in> Nat; n \<in> Nat\<rbrakk> \<Longrightarrow> m mod n \<equiv> divmodNat(m,n)[2]"


lemma divIsNat [iff]:
  assumes "m \<in> Nat" and "n \<in> Nat" and "0 < n"
  shows "m div n \<in> Nat"
using divmodNatInNatNat[OF assms] assms by (auto simp: div_nat_def)

lemma modIsNat [iff]:
  assumes "m \<in> Nat" and "n \<in> Nat" and "0 < n"
  shows "m mod n \<in> Nat"
using divmodNatInNatNat[OF assms] assms by (auto simp: mod_nat_def two_def)

lemma divmodNat_div_mod:
  assumes m: "m \<in> Nat" and n: "n \<in> Nat" and pos: "0 < n"
  shows "divmodNat(m,n) = \<langle>m div n, m mod n\<rangle>"
unfolding div_nat_def[OF m n] mod_nat_def[OF m n] two_def
using divmodNatInNatNat[OF assms]
by force

lemma divmod_rel_div_mod_nat:
  assumes "m \<in> Nat" and "n \<in> Nat" and "0 < n"
  shows "divmod_rel(m, n, m div n, m mod n)"
using divmodNat_divmod_rel[OF assms sym[OF divmodNat_div_mod[OF assms]]]
by (auto simp: two_def)

lemma div_nat_unique:
  assumes h: "divmod_rel(m,n,q,r)"
    and m: "m \<in> Nat" and n: "n \<in> Nat" and pos: "0 < n" and q: "q \<in> Nat" and r: "r \<in> Nat"
  shows "m div n = q"
unfolding div_nat_def[OF m n] using divmodNat_unique[OF assms] by simp

lemma mod_nat_unique:
  assumes h: "divmod_rel(m,n,q,r)"
    and m: "m \<in> Nat" and n: "n \<in> Nat" and pos: "0 < n" and q: "q \<in> Nat" and r: "r \<in> Nat"
  shows "m mod n = r"
unfolding mod_nat_def[OF m n] two_def using divmodNat_unique[OF assms] by simp

lemma mod_nat_less_divisor:
  assumes m: "m \<in> Nat" and n: "n \<in> Nat" and pos: "0 < n"
  shows "m mod n < n"
using assms divmod_rel_div_mod_nat[OF assms] by (simp add: divmod_rel_def)

text \<open> ``Recursive'' computation of @{text div} and @{text mod}. \<close>

lemma divmodNat_base:
  assumes m: "m \<in> Nat" and n: "n \<in> Nat" and less: "m < n"
  shows "divmodNat(m,n) = \<langle>0, m\<rangle>"
proof -
  from assms have pos: "0 < n" by (intro nat_leq_less_trans[of "0" "m" "n"], simp+)
  let ?dm = "divmodNat(m,n)"
  from m n pos have 1: "divmod_rel(m,n,?dm[1],?dm[2])"
    by (simp add: divmodNat_divmod_rel)
  from m n pos have 2: "?dm \<in> Nat \<times> Nat" by (rule divmodNatInNatNat)
  with 1 2 less n have "?dm[1] * n < n"
    unfolding two_def
    by (auto simp: divmod_rel_def elim!: add_lessD1)
  with 2 n have 3: "?dm[1] = 0" by (intro mult_less_self_right, auto)

  with 1 2 m n have "?dm[2] = m" by (auto simp: divmod_rel_def two_def)

  with 3 prodProj[OF 2] show ?thesis by simp
qed

lemma divmodNat_step:
  assumes m: "m \<in> Nat" and n: "n \<in> Nat" and pos: "0 < n" and geq: "n \<le> m"
  shows "divmodNat(m,n) = \<langle>Succ[(m -- n) div n], (m -- n) mod n\<rangle>"
proof -
  from m n pos have 1: "divmod_rel(m, n, m div n, m mod n)"
    by (rule divmod_rel_div_mod_nat)
  have 2: "m div n \<noteq> 0"
  proof
    assume "m div n = 0"
    with 1 m n pos have "m < n" by (auto simp: divmod_rel_def)
    with geq m n show "FALSE" by (auto simp: nat_less_leq_not_leq)
  qed
  with m n pos obtain k where k1: "k \<in> Nat" and k2: "m div n = Succ[k]"
    using not0_implies_Suc[of "m div n"] by auto
  with 1 m n pos have "m = n + k*n + m mod n"
    by (auto simp: divmod_rel_def add_commute_nat)
  moreover
  from m n k1 pos geq have "... -- n = k*n + m mod n"
    by (simp add: adiff_add_assoc2)
  ultimately
  have "m -- n = k*n + m mod n" by simp
  with pos m n 1 have "divmod_rel(m -- n, n, k, m mod n)"
    by (auto simp: divmod_rel_def)

  with k1 m n pos have "divmodNat(m -- n, n) = \<langle>k, m mod n\<rangle>"
    by (intro divmodNat_unique, simp+)
  moreover
  from m n pos have "divmodNat(m -- n, n) = \<langle>(m--n) div n, (m--n) mod n\<rangle>"
    by (intro divmodNat_div_mod, simp+)
  ultimately
  have "m div n = Succ[(m--n) div n]" and "m mod n = (m--n) mod n"
    using m n k2 by auto
  thus ?thesis by (simp add: divmodNat_div_mod[OF m n pos])
qed


text \<open> The ''recursion'' equations for @{text div} and @{text mod} \<close>

lemma div_nat_less [simp]:
  assumes m: "m \<in> Nat" and n: "n \<in> Nat" and less: "m < n"
  shows "m div n = 0"
proof -
  from assms have pos: "0 < n" by (intro nat_leq_less_trans[of "0" "m" "n"], simp+)
  from divmodNat_base[OF m n less] divmodNat_div_mod[OF m n pos] show ?thesis
    by simp
qed

lemma div_nat_geq:
  assumes m: "m \<in> Nat" and n: "n \<in> Nat" and pos: "0 < n" and geq: "n \<le> m"
  shows "m div n = Succ[(m -- n) div n]"
using divmodNat_step[OF assms] divmodNat_div_mod[OF m n pos]
by simp

lemma mod_nat_less [simp]:
  assumes m: "m \<in> Nat" and n: "n \<in> Nat" and less: "m < n"
  shows "m mod n = m"
proof -
  from assms have pos: "0 < n" by (intro nat_leq_less_trans[of "0" "m" "n"], simp+)
  from divmodNat_base[OF m n less] divmodNat_div_mod[OF m n pos] show ?thesis
    by simp
qed

lemma mod_nat_geq:
  assumes m: "m \<in> Nat" and n: "n \<in> Nat" and pos: "0 < n" and geq: "n \<le> m"
  shows "m mod n = (m -- n) mod n"
using divmodNat_step[OF assms] divmodNat_div_mod[OF m n pos]
by simp


subsection \<open> Facts about @{const div} and @{const mod} \<close>

lemma mod_div_nat_equality [simp]:
  assumes "m \<in> Nat" and "n \<in> Nat" and "0 < n"
  shows "(m div n) * n + m mod n = m"
using divmod_rel_div_mod_nat [OF assms] by (simp add: divmod_rel_def)

lemma mod_div_nat_equality2 [simp]:
  assumes "m \<in> Nat" and "n \<in> Nat" and "0 < n"
  shows "n * (m div n) + m mod n = m"
using assms mult_commute_nat[of "n" "m div n"] by simp

lemma mod_div_nat_equality3 [simp]:
  assumes m: "m \<in> Nat" and n: "n \<in> Nat" and "0 < n"
  shows "m mod n + (m div n) * n = m"
using assms add_commute_nat[of "m mod n"] by simp

lemma mod_div_nat_equality4 [simp]:
  assumes m: "m \<in> Nat" and n: "n \<in> Nat" and "0 < n"
  shows "m mod n + n * (m div n) = m"
using assms mult_commute_nat[of "n" "m div n"] by simp

(** immediate consequence of above
lemma div_mod_nat_equality:
  assumes "m \<in> Nat" and "n \<in> Nat" and "0 < n"
  shows "((m div n) * n + m mod n) + k = m + k"
using assms by simp

lemma div_mod_nat_equality2:
  assumes "m \<in> Nat" and "n \<in> Nat" and "0 < n"
  shows "(n * (m div n) + m mod n) + k = m + k"
using assms by simp
**)

lemma div_nat_mult_self1 [simp]:
  assumes q: "q \<in> Nat" and m: "m \<in> Nat" and n: "n \<in> Nat" and pos: "0 < n"
  shows "(q + m * n) div n = m + (q div n)" (is "?P(m)")
using m proof (induct m)
  from assms show "?P(0)" by simp
next
  fix k
  assume k: "k \<in> Nat" and ih: "?P(k)"
  from n q k have "n \<le> q + (k*n + n)" by (simp add: add_assoc_nat)
  with q k n pos have "(q + (k*n + n)) div n = Succ[(q + k*n) div n]"
    by (simp add: div_nat_geq add_assoc_nat)
  with ih q m n k pos show "?P(Succ[k])" by simp
qed

lemma div_nat_mult_self2 [simp]:
  assumes "q \<in> Nat" and "n \<in> Nat" and "m \<in> Nat" and "0 < n"
  shows "(q + n * m) div n = m + q div n"
using assms by (simp add: mult_commute_nat)

lemma div_nat_mult_self3 [simp]:
  assumes "q \<in> Nat" and "n \<in> Nat" and "m \<in> Nat" and "0 < n"
  shows "(m * n + q) div n = m + q div n"
using assms by (simp add: add_commute_nat)

lemma div_nat_mult_self4 [simp]:
  assumes "q \<in> Nat" and "n \<in> Nat" and "m \<in> Nat" and "0 < n"
  shows "(n * m + q) div n = m + q div n"
using assms by (simp add: add_commute_nat)

lemma div_nat_0:
  assumes "n \<in> Nat" and "0 < n"
  shows "0 div n = 0"
using assms by simp

lemma mod_0:
  assumes "n \<in> Nat" and "0 < n"
  shows "0 mod n = 0"
using assms by simp

lemma mod_nat_mult_self1 [simp]:
  assumes q: "q \<in> Nat" and m: "m \<in> Nat" and n: "n \<in> Nat" and pos: "0 < n"
  shows "(q + m * n) mod n = q mod n"
proof -
  from assms have "m*n + q = q + m*n"
    by (simp add: add_commute_nat)
  also from assms have "... = ((q + m*n) div n) * n + (q + m*n) mod n"
    by (intro sym[OF mod_div_nat_equality], simp+)
  also from assms have "... = (m + q div n) * n + (q + m*n) mod n"
    by simp
  also from assms have "... = m*n + ((q div n) * n + (q + m*n) mod n)"
    by (simp add: add_mult_distrib_right_nat add_assoc_nat)
  finally have "q = (q div n) * n + (q + m*n) mod n"
    using assms by simp
  with q n pos have "(q div n) * n + (q + m*n) mod n = (q div n) * n + q mod n"
    by simp
  with assms show ?thesis by (simp del: mod_div_nat_equality)
qed

lemma mod_nat_mult_self2 [simp]:
  assumes "q \<in> Nat" and "m \<in> Nat" and "n \<in> Nat" and "0 < n"
  shows "(q + n * m) mod n = q mod n"
using assms by (simp add: mult_commute_nat)

lemma mod_nat_mult_self3 [simp]:
  assumes "q \<in> Nat" and "m \<in> Nat" and "n \<in> Nat" and "0 < n"
  shows "(m * n + q) mod n = q mod n"
using assms by (simp add: add_commute_nat)

lemma mod_nat_mult_self4 [simp]:
  assumes "q \<in> Nat" and "m \<in> Nat" and "n \<in> Nat" and "0 < n"
  shows "(n * m + q) mod n = q mod n"
using assms by (simp add: add_commute_nat)

lemma div_nat_mult_self1_is_id [simp]:
  assumes "m \<in> Nat" and "n \<in> Nat" and "0 < n"
  shows "(m * n) div n = m"
using assms div_nat_mult_self1 [of 0 m n] by simp

lemma div_nat_mult_self2_is_id [simp]:
  assumes "m \<in> Nat" and "n \<in> Nat" and "0 < n"
  shows "(n * m) div n = m"
using assms div_nat_mult_self2[of 0 n m] by simp

lemma mod_nat_mult_self1_is_0 [simp]:
  assumes "m \<in> Nat" and "n \<in> Nat" and "0 < n"
  shows "(m * n) mod n = 0"
using assms mod_nat_mult_self1 [of 0 m n] by simp

lemma mod_nat_mult_self2_is_0 [simp]:
  assumes "m \<in> Nat" and "n \<in> Nat" and "0 < n"
  shows "(n * m) mod n = 0"
using assms mod_nat_mult_self2 [of 0 m n] by simp

lemma div_nat_by_1 [simp]:
  assumes "m \<in> Nat"
  shows "m div 1 = m"
using assms div_nat_mult_self1_is_id [of m 1] by simp

lemma mod_nat_by_1 [simp]:
  assumes "m \<in> Nat"
  shows "m mod 1 = 0"
using assms mod_nat_mult_self1_is_0[of m 1] by simp

lemma mod_nat_self [simp]:
  assumes "n \<in> Nat" and "0 < n"
  shows "n mod n = 0"
using assms mod_nat_mult_self1_is_0[of 1] by simp

lemma div_nat_self [simp]:
  assumes "n \<in> Nat" and "0 < n"
  shows "n div n = 1"
using assms div_nat_mult_self1_is_id [of 1 n] by simp

lemma div_nat_add_self1 [simp]:
  assumes m: "m \<in> Nat" and n: "n \<in> Nat" and pos: "0 < n"
  shows "(m + n) div n = m div n + 1"
using assms div_nat_mult_self1[OF m oneIsNat n pos] by simp

lemma div_nat_add_self2 [simp]:
  assumes m: "m \<in> Nat" and n: "n \<in> Nat" and pos: "0 < n"
  shows "(n + m) div n = m div n + 1"
using assms div_nat_mult_self3[OF m n oneIsNat pos] by simp

lemma mod_nat_add_self1 [simp]:
  assumes m: "m \<in> Nat" and n: "n \<in> Nat" and pos: "0 < n"
  shows "(m + n) mod n = m mod n"
using assms mod_nat_mult_self1[OF m oneIsNat n pos] by simp

lemma mod_nat_add_self2 [simp]:
  assumes m: "m \<in> Nat" and n: "n \<in> Nat" and pos: "0 < n"
  shows "(n + m) mod n = m mod n"
using assms mod_nat_mult_self3[OF m oneIsNat n pos] by simp

lemma div_mod_nat_decomp:
  assumes m: "m \<in> Nat" and n: "n \<in> Nat" and pos: "0 < n"
  obtains q r where "q \<in> Nat" and "r \<in> Nat"
    and "q = m div n" and "r = m mod n" and "m = q * n + r"
proof -
  from m n pos have "m = (m div n) * n + (m mod n)" by simp
  with assms that show ?thesis by blast
qed

lemma dvd_nat_eq_mod_eq_0:
  assumes "m \<in> Nat" and "n \<in> Nat" and "0 < m"
  shows "(m dvd n) = (n mod m = 0)" (is "?lhs = ?rhs")
proof -
  from assms have 1: "?lhs \<Rightarrow> ?rhs" by auto
  have 2: "?rhs \<Rightarrow> ?lhs"
  proof
    assume mod: "n mod m = 0"
    with assms mod_div_nat_equality[of n m] have "(n div m) * m = n" by simp
    with assms have "n = m * (n div m)" by (simp add: mult_commute_nat)
    with assms show "m dvd n" by blast
  qed
  from 1 2 assms show ?thesis by blast
qed

lemma mod_div_nat_trivial [simp]:
  assumes "m \<in> Nat" and "n \<in> Nat" and "0 < n"
  shows "(m mod n) div n = 0"
proof -
  from assms
  have "m div n + (m mod n) div n = (m mod n + (m div n) * n) div n"
    by (simp add: mod_nat_less_divisor)
  also from assms have "... = m div n + 0" by simp
  finally show ?thesis
    using assms by simp
qed

lemma mod_mod_nat_trivial [simp]:
  assumes "m \<in> Nat" and "n \<in> Nat" and "0 < n"
  shows "(m mod n) mod n = m mod n"
proof -
  from assms mod_nat_mult_self1[of "m mod n" "m div n" "n"]
  have "(m mod n) mod n = (m mod n + (m div n) * n) mod n" by simp
  also from assms have "... = m mod n" by simp
  finally show ?thesis .
qed

lemma dvd_nat_imp_mod_0:
  assumes "n dvd m" and "m \<in> Nat" and "n \<in> Nat" and "0 < n"
  shows "m mod n = 0"
using assms by (simp add: dvd_nat_eq_mod_eq_0)

lemma dvd_nat_div_mult_self:
  assumes dvd: "n dvd m" and m: "m \<in> Nat" and n: "n \<in> Nat" and pos: "0 < n"
  shows "(m div n) * n = m"
using assms
  dvd_nat_imp_mod_0[OF assms]
  mod_div_nat_equality[OF m n pos]
by simp

lemma dvd_nat_div_mult:
  assumes dvd: "n dvd m" and m: "m \<in> Nat" and n: "n \<in> Nat" and pos: "0 < n"
      and k: "k \<in> Nat"
  shows "(m div n) * k = (m * k) div n"
proof -
  from dvd m n obtain l where l: "l \<in> Nat" "m = n*l" by auto
  with m n k have "m * k = n * (l*k)" by (simp add: mult_assoc_nat)
  with m n k l pos show ?thesis by simp
qed

lemma div_nat_dvd_div [simp]:
  assumes 1: "a dvd b" and 2: "a dvd c"
      and a: "a \<in> Nat" and b: "b \<in> Nat" and c: "c \<in> Nat" and pos: "0 < a"
  shows "(b div a) dvd (c div a) = (b dvd c)"
proof (auto)
  assume lhs: "(b div a) dvd (c div a)"
  with a b c pos have "((b div a) * a) dvd ((c div a) * a)"
    by (intro mult_dvd_mono, simp+)
  moreover
  from 1 a b pos have "(b div a) * a = b" by (simp add: dvd_nat_div_mult_self)
  moreover
  from 2 a c pos have "(c div a) * a = c" by (simp add: dvd_nat_div_mult_self)
  ultimately show "b dvd c" by simp
next
  assume rhs: "b dvd c"
  with b c obtain k where k: "k \<in> Nat" "c = b*k" by auto
  from 1 a b obtain l where l: "l \<in> Nat" "b = a*l" by auto
  with a pos have 3: "b div a = l" by simp
  from 2 a c obtain m where m: "m \<in> Nat" "c = a*m" by auto
  with a pos have 4: "c div a = m" by simp
  from k l m a pos mult_assoc_nat[of a l k, symmetric] have "m = l*k" by auto
  with k l m have "l dvd m" by auto
  with 3 4 show "(b div a) dvd (c div a)" by simp
qed (auto simp: assms)

lemma dvd_mod_nat_imp_dvd:
  assumes 1: "k dvd (m mod n)" and 2: "k dvd n"
      and k: "k \<in> Nat" and m: "m \<in> Nat" and n: "n \<in> Nat" and pos: "0 < n"
  shows "k dvd m"
proof -
  from assms have "k dvd ((m div n) * n + m mod n)"
    by (simp add: dvd_mult del: mod_div_nat_equality)
  with m n pos show ?thesis by simp
qed

(*** TODO
text \<open> Addition respects modular equivalence. \<close>

text \<open> Multiplication respects modular equivalence. \<close>

text \<open> Negation respects modular equivalence. \<close>

text \<open> Subtraction respects modular equivalence. \<close>
*)

end
