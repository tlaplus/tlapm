(*  Title:      TLA+/Peano.thy
    Author:     Stephan Merz, LORIA
    Copyright (C) 2008-2020  INRIA and Microsoft Corporation
    License:    BSD
    Version:    Isabelle2020
*)

section \<open> Peano's axioms and natural numbers \<close>

theory Peano
imports FixedPoints Functions
begin

text \<open>
  As a preparation for the definition of numbers and arithmetic
  in \tlaplus{}, we state Peano's axioms for natural numbers and
  prove the existence of a structure satisfying them. The presentation
  of the axioms is somewhat simplified compared to the \tlaplus{} book.
  (Moreover, the existence of such a structure is assumed, but not
  proven in the book.)
\<close>

subsection \<open> The Peano Axioms \<close>

definition PeanoAxioms :: "[c,c,c] \<Rightarrow> c" where
  \<comment> \<open>parameters: the set of natural numbers, zero, and successor function\<close>
  "PeanoAxioms(N,Z,Sc) \<equiv>
      Z \<in> N
   \<and> Sc \<in> [N \<rightarrow> N]
   \<and> (\<forall>n \<in> N : Sc[n] \<noteq> Z)
   \<and> (\<forall>m,n \<in> N: Sc[m] = Sc[n] \<Rightarrow> m = n)
   \<and> (\<forall>S \<in> SUBSET N : Z \<in> S \<and> (\<forall>n\<in>S : Sc[n] \<in> S) \<Rightarrow> N \<subseteq> S)"

text \<open>
  The existence of a structure satisfying Peano's axioms is proven
  following the standard ZF construction where @{text "{}"} is zero,
  @{text "i \<union> {i}"} is taken as the successor of any natural
  number @{text i}, and the set of natural numbers is defined as
  the least set that contains zero and is closed under successor
  (this is a subset of the infinity set asserted to exist in ZF
  set theory). In \tlaplus{}, natural numbers are defined by a sequence
  of @{text CHOOSE}'s below, so there is no commitment to that
  particular structure.
\<close>

theorem peanoExists: "\<exists>N,Z,Sc : PeanoAxioms(N,Z,Sc)"
proof -
  let ?sc = "\<lambda>n. addElt(n,n)"  \<comment> \<open> successor \emph{operator} \<close>
  define expand where "expand \<equiv> \<lambda>S. {{}} \<union> { ?sc(n) : n \<in> S}"
  define N where "N \<equiv> lfp(infinity, expand)"
  define Z where "Z \<equiv> {}"
  define Sc where "Sc \<equiv> [n \<in> N \<mapsto> ?sc(n)]"  \<comment> \<open>successor \emph{function}\<close>
  have mono: "Monotonic(infinity, expand)"
    using infinity by (auto simp: Monotonic_def expand_def)
  hence expandN: "expand(N) \<subseteq> N"
    by (unfold N_def, rule lfpPreFP)
  from expandN have 1: "Z \<in> N"
    by (auto simp: expand_def Z_def)
  have 2: "Sc \<in> [N \<rightarrow> N]"
  proof (unfold Sc_def, rule functionInFuncSet)
    show "\<forall>n \<in> N : ?sc(n) \<in> N" using expandN by (auto simp: expand_def)
  qed
  have 3: "\<forall>m\<in>N : Sc[m] \<noteq> Z"
    unfolding Z_def Sc_def by auto
  have 4: "\<forall>m,n \<in> N : Sc[m] = Sc[n] \<Rightarrow> m = n"
  proof (clarify)
    fix m n
    assume "m \<in> N" and "n \<in> N" and "Sc[m] = Sc[n]"
    hence eq: "?sc(m) = ?sc(n)" by (simp add: Sc_def)
    show "m = n"
    proof (rule setEqual)
      show "m \<subseteq> n"
      proof (rule subsetI)
	fix x
	assume x: "x \<in> m" show "x \<in> n"
	proof (rule contradiction)
	  assume "x \<notin> n"
	  with x eq have "n \<in> m" by auto
          moreover
	  from eq have "m \<in> ?sc(n)" by auto
          ultimately
	  show "FALSE" by (blast elim: inAsym)
	qed
      qed
    next
      show "n \<subseteq> m"
      proof (rule subsetI)
	fix x
	assume x: "x \<in> n" show "x \<in> m"
	proof (rule contradiction)
	  assume "x \<notin> m"
	  with x eq have "m \<in> n" by auto
          moreover
          from eq have "n \<in> ?sc(m)" by auto
          ultimately
	  show "FALSE" by (blast elim: inAsym)
	qed
      qed
    qed
  qed
  have 5: "\<forall>S \<in> SUBSET N : Z \<in> S \<and> (\<forall>n\<in>S : Sc[n] \<in> S) \<Rightarrow> N \<subseteq> S"
  proof (clarify del: subsetI)
    fix S
    assume sub: "S \<subseteq> N" and Z: "Z \<in> S" and Sc: "\<forall>n\<in>S : Sc[n] \<in> S"
    show "N \<subseteq> S"
    proof (unfold N_def, rule lfpLB)
      show "expand(S) \<subseteq> S"
      proof (auto simp: expand_def)
	from Z show "{} \<in> S" by (simp add: Z_def)
      next
	fix n
	assume n: "n \<in> S"
	with Sc have "Sc[n] \<in> S" ..
	moreover
	from n sub have "n \<in> N" by auto
	hence "Sc[n] = ?sc(n)" by (simp add: Sc_def)
	ultimately show "?sc(n) \<in> S" by simp
      qed
    next
      have "N \<subseteq> infinity"
	by (unfold N_def, rule lfpSubsetDomain)
      with sub show "S \<subseteq> infinity" by auto
    qed
  qed
  from 1 2 3 4 5 have "PeanoAxioms(N,Z,Sc)"
    unfolding PeanoAxioms_def by blast
  thus ?thesis by blast
qed

lemma peanoInduct:
  assumes pa: "PeanoAxioms(N,Z,Sc)"
  and "S \<subseteq> N" and "Z \<in> S" and "\<And>n. n \<in> S \<Longrightarrow> Sc[n] \<in> S"
  shows "N \<subseteq> S"
proof -
  from pa have "\<forall>S \<in> SUBSET N : Z \<in> S \<and> (\<forall>n\<in>S : Sc[n] \<in> S) \<Rightarrow> N \<subseteq> S"
    unfolding PeanoAxioms_def by blast
  with assms show ?thesis by blast
qed


subsection \<open> Natural numbers: definition and elementary theorems \<close>

text \<open>
  The structure of natural numbers is now defined to be some set,
  zero, and successor satisfying Peano's axioms.
\<close>

definition Succ :: "c"
where "Succ \<equiv> CHOOSE Sc : \<exists>N,Z : PeanoAxioms(N,Z,Sc)"

definition Nat :: "c"
where "Nat \<equiv> DOMAIN Succ"

definition zero :: "c"                ("0")
where "0 \<equiv> CHOOSE Z : PeanoAxioms(Nat, Z, Succ)"

abbreviation "one \<equiv> Succ[0]"
notation "one"                        ("1")
abbreviation "two \<equiv> Succ[1]"
notation "two"                        ("2")
abbreviation "three \<equiv> Succ[2]"
notation "three"                      ("3")
abbreviation "four \<equiv> Succ[3]"
notation "four"                       ("4")
abbreviation "five \<equiv> Succ[4]"
notation "five"                       ("5")
abbreviation "six \<equiv> Succ[5]"
notation "six"                        ("6")
abbreviation "seven \<equiv> Succ[6]"
notation "seven"                      ("7")
abbreviation "eight \<equiv> Succ[7]"
notation "eight"                      ("8")
abbreviation "nine \<equiv> Succ[8]"
notation "nine"                       ("9")
abbreviation "ten \<equiv> Succ[9]"
notation "ten"                       ("10")
abbreviation "eleven \<equiv> Succ[10]"
notation "eleven"                    ("11")
abbreviation "twelve \<equiv> Succ[11]"
notation "twelve"                    ("12")
abbreviation "thirteen \<equiv> Succ[12]"
notation "thirteen"                  ("13")
abbreviation "fourteen \<equiv> Succ[13]"
notation "fourteen"                  ("14")
abbreviation "fifteen \<equiv> Succ[14]"
notation "fifteen"                   ("15")


lemma peanoNatZeroSucc: "PeanoAxioms(Nat, 0, Succ)"
proof -
  have "\<exists>N,Z : PeanoAxioms(N,Z,Succ)"
  proof (unfold Succ_def, rule chooseI_ex)
    from peanoExists show "\<exists>Sc,N,Z : PeanoAxioms(N,Z,Sc)" by blast
  qed
  then obtain N Z where PNZ: "PeanoAxioms(N,Z,Succ)" by blast
  hence "Succ \<in> [N \<rightarrow> N]"
    by (simp add: PeanoAxioms_def)
  hence "N = Nat"
    by (simp add: Nat_def)
  with PNZ have "PeanoAxioms(Nat, Z, Succ)" by simp
  thus ?thesis by (unfold zero_def, rule chooseI)
qed

lemmas
  setEqualI [where A = "Nat", intro!]
  setEqualI [where B = "Nat", intro!]

lemma zeroIsNat [intro!,simp]: "0 \<in> Nat"
using peanoNatZeroSucc by (simp add: PeanoAxioms_def)

lemma succInNatNat [intro!,simp]: "Succ \<in> [Nat \<rightarrow> Nat]"
using peanoNatZeroSucc by (simp add: PeanoAxioms_def)

lemma succIsAFcn [intro!,simp]: "isAFcn(Succ)"
using succInNatNat by blast

\<comment> \<open>@{text "DOMAIN Succ = Nat"}\<close>
lemmas domainSucc [intro!,simp] = funcSetDomain[OF succInNatNat]
\<comment> \<open>@{text "n \<in> Nat \<Longrightarrow> Succ[n] \<in> Nat"}\<close>
lemmas succIsNat [intro!,simp] = funcSetValue[OF succInNatNat]

lemma oneIsNat [intro!,simp]: "1 \<in> Nat"
by simp

lemma twoIsNat [intro!,simp]: "2 \<in> Nat"
by simp

lemma [simp]:
  assumes "n \<in> Nat"
  shows "(Succ[n] = 0) = FALSE"
using assms peanoNatZeroSucc by (auto simp: PeanoAxioms_def)

lemma [simp]:
  assumes n: "n \<in> Nat"
  shows "(0 = Succ[n]) = FALSE"
using assms by (auto dest: sym)

lemma succNotZero (*[elim] \<comment> don't: produces "ignoring weak elimination rule"*):
  "\<lbrakk>Succ[n] = 0; n \<in> Nat\<rbrakk> \<Longrightarrow> P"
  "\<lbrakk>0 = Succ[n]; n \<in> Nat\<rbrakk> \<Longrightarrow> P"
by (simp+)

lemma succInj [dest]:
  assumes "Succ[m] = Succ[n]" and "m \<in> Nat" and "n \<in> Nat"
  shows "m=n"
using peanoNatZeroSucc assms by (auto simp: PeanoAxioms_def)

lemma succInjIff [simp]:
  assumes "m \<in> Nat" and "n \<in> Nat"
  shows "(Succ[m] = Succ[n]) = (m = n)"
using assms by auto

lemma natInduct:
  assumes z: "P(0)"
  and sc: "\<And>n. \<lbrakk>n \<in> Nat; P(n)\<rbrakk> \<Longrightarrow> P(Succ[n])"
  shows "\<forall>n\<in>Nat : P(n)"
proof -
  let ?P = "{n \<in> Nat : P(n)}"
  from peanoNatZeroSucc have "Nat \<subseteq> ?P"
    by (rule peanoInduct, auto simp: z sc)
  thus ?thesis by auto
qed

\<comment> \<open>version of above suitable for the inductive reasoning package\<close>
lemma natInductE [case_names 0 Succ, induct set: Nat]:
  assumes "n \<in> Nat" and "P(0)" and "\<And>n. \<lbrakk>n \<in> Nat; P(n)\<rbrakk> \<Longrightarrow> P(Succ[n])"
  shows "P(n)"
using bspec[OF natInduct, where P=P] assms by blast

(*** EXAMPLE INDUCTION PROOFS ***

lemma "\<forall>n\<in>Nat : n=0 \<or> (\<exists>m \<in> Nat : n = Succ[m])"
by (rule natInduct, auto)

lemma
  assumes 1: "n \<in> Nat"
  shows "n=0 \<or> (\<exists>m \<in> Nat : n = Succ[m])"
using 1 by (induct, auto)

*** END EXAMPLE ***)

lemma natCases [case_names 0 Succ, cases set: Nat]:
  assumes n: "n \<in> Nat"
  and z: "n=0 \<Longrightarrow> P" and sc: "\<And>m. \<lbrakk>m \<in> Nat; n = Succ[m]\<rbrakk> \<Longrightarrow> P"
  shows "P"
proof -
  from n have "n=0 \<or> (\<exists>m \<in> Nat : n = Succ[m])"
    by (induct, auto)
  thus ?thesis
  proof
    assume "n=0" thus "P" by (rule z)
  next
    assume "\<exists>m\<in>Nat : n = Succ[m]"
    then obtain m where "m \<in> Nat" and "n = Succ[m]" ..
    thus "P" by (rule sc)
  qed
qed
    
lemma succIrrefl:
  assumes n: "n \<in> Nat"
  shows "Succ[n] \<noteq> n"
using n by (induct, auto)

lemma succIrreflE (*[elim] -- don't: "ignoring weak elimination rule" *):
  "\<lbrakk>Succ[n] = n; n \<in> Nat\<rbrakk> \<Longrightarrow> P"
  "\<lbrakk>n = Succ[n]; n \<in> Nat\<rbrakk> \<Longrightarrow> P"
by (auto dest: succIrrefl)

lemma succIrrefl_iff [simp]:
  "n \<in> Nat \<Longrightarrow> (Succ[n] = n) = FALSE"
  "n \<in> Nat \<Longrightarrow> (n = Succ[n]) = FALSE"
by (auto dest: succIrrefl)


text \<open>Induction over two parameters along the ``diagonal''.\<close>
lemma diffInduction:
  assumes b1: "\<forall>m\<in>Nat : P(m,0)" and b2: "\<forall>n\<in>Nat : P(0, Succ[n])"
  and step: "\<forall>m,n\<in>Nat : P(m,n) \<Rightarrow> P(Succ[m], Succ[n])"
  shows "\<forall>m,n\<in>Nat : P(m,n)"
proof (rule natInduct)
  show "\<forall>n\<in>Nat : P(0,n)"
    using b1 b2 by (intro natInduct, auto)
next
  fix m
  assume m: "m \<in> Nat" and ih: "\<forall>n\<in>Nat : P(m,n)"
  show "\<forall>n\<in>Nat : P(Succ[m],n)"
  proof (rule bAllI)
    fix n
    assume "n \<in> Nat" thus "P(Succ[m],n)"
    proof (cases)
      case 0 with b1 m show ?thesis by auto
    next
      case Succ with step ih m show ?thesis by auto
    qed
  qed
qed

lemma diffInduct:
  assumes n: "n \<in> Nat" and m: "m \<in> Nat"
  and b1: "\<And>m. m\<in>Nat \<Longrightarrow> P(m,0)" and b2: "\<And>n. n\<in>Nat \<Longrightarrow> P(0, Succ[n])"
  and step: "\<And>m n. \<lbrakk>m \<in> Nat; n\<in>Nat; P(m,n) \<rbrakk> \<Longrightarrow> P(Succ[m], Succ[n])"
  shows "P(m,n)"
proof -
  have "\<forall>m,n\<in>Nat : P(m,n)"
    by (rule diffInduction, auto intro: b1 b2 step)
  with n m show ?thesis by blast
qed

lemma not0_implies_Suc: 
  "\<lbrakk>n \<in> Nat; n \<noteq> 0\<rbrakk> \<Longrightarrow> \<exists>m \<in> Nat: n = Succ[m]"
by(rule natCases, auto)

subsection \<open> Initial intervals of natural numbers and ``less than'' \<close>

text \<open>
  The set of natural numbers up to (and including) a given $n$ is
  inductively defined as the smallest set of natural numbers that
  contains $n$ and that is closed under predecessor.

  NB: ``less than'' is not first-order definable from the Peano axioms,
  a set-theoretic definition such as the following seems to be unavoidable.
\<close>

definition upto :: "c \<Rightarrow> c"
where "upto(n) \<equiv> lfp(Nat, \<lambda>S. {n} \<union> { k \<in> Nat : Succ[k] \<in> S })"

lemmas
  setEqualI [where A = "upto(n)" for n, intro!]
  setEqualI [where B = "upto(n)" for n, intro!]

lemma uptoNat: "upto(n) \<subseteq> Nat"
  unfolding upto_def by (rule lfpSubsetDomain)

lemma uptoPred:
  assumes Suc: "Succ[m] \<in> upto(n)" and m: "m \<in> Nat" and n: "n \<in> Nat"
  shows "m \<in> upto(n)"
proof -
  let ?f = "\<lambda>S. {n} \<union> {k\<in>Nat : Succ[k] \<in> S}"
  from n have mono: "Monotonic(Nat, ?f)"
    unfolding Monotonic_def by blast
  from m Suc have 1: "m \<in> ?f(upto(n))" by auto
  from mono have 2: "?f(upto(n)) \<subseteq> upto(n)"
    unfolding upto_def by (rule lfpPreFP)
  from 1 2 show ?thesis by blast
qed

lemma uptoZero: "upto(0) = {0}"
proof (rule setEqual)
  have "{0} \<union> { k \<in> Nat : Succ[k] \<in> {0} } \<subseteq> {0}" by auto
  thus "upto(0) \<subseteq> {0}"
    unfolding upto_def by (rule lfpLB, auto)
next
  show "{0} \<subseteq> upto(0)"
    unfolding upto_def by (rule lfpGLB, auto)
qed

lemma uptoSucc:
  assumes n: "n \<in> Nat"
  shows "upto(Succ[n]) = upto(n) \<union> {Succ[n]}" (is "?lhs = ?rhs")
proof -
  let ?preds = "\<lambda>S. {k \<in> Nat : Succ[k] \<in> S}"
  let ?f = "\<lambda>S k. {k} \<union> ?preds(S)"
  have mono: "\<And>k. k \<in> Nat \<Longrightarrow> Monotonic(Nat, \<lambda>S. ?f(S,k))"
    by (auto simp: Monotonic_def)
  \<comment> \<open>``$\subseteq$''\<close>
  from n have "?preds(?rhs) \<subseteq> ?f(upto(n), n)" by auto
  also have "\<dots> \<subseteq> upto(n)"
    by (unfold upto_def, rule lfpPreFP, rule mono, rule n)
  finally have "?f(?rhs, Succ[n]) \<subseteq> ?rhs" by auto
  moreover from n have "?rhs \<subseteq> Nat"
    by (intro unionLUB, auto elim: uptoNat[THEN subsetD])
  ultimately have 1: "?lhs \<subseteq> ?rhs"
    by (unfold upto_def[where n="Succ[n]"], rule lfpLB)
  \<comment> \<open>``$\supseteq$''\<close>
  from n mono have 2: "?f(?lhs, Succ[n]) \<subseteq> ?lhs"
    unfolding upto_def by (intro lfpPreFP, blast)
  with n have "?f(?lhs, n) \<subseteq> ?lhs" by auto
  moreover have "?lhs \<subseteq> Nat" by (rule uptoNat)
  ultimately have 3: "upto(n) \<subseteq> ?lhs"
    unfolding upto_def[where n=n] by (rule lfpLB)
  from 2 have 4: "Succ[n] \<in> ?lhs" by auto
  from 3 4 have "?rhs \<subseteq> ?lhs" by auto
  with 1 show ?thesis by (rule setEqual)
qed

lemma uptoRefl:
  assumes n: "n \<in> Nat"
  shows "n \<in> upto(n)"
using n proof (cases)
  case 0 thus ?thesis by (simp add: uptoZero)
next
  case Succ thus ?thesis by (auto simp: uptoSucc)
qed

lemma zeroInUpto:
  assumes n: "n \<in> Nat"
  shows "0 \<in> upto(n)"
using n by (induct, auto simp: uptoZero uptoSucc)

lemma SuccNotUptoZero:
  assumes "n \<in> Nat" and "Succ[n] \<in> upto(0)"
  shows "P"
using assms by (auto simp: uptoZero)

lemma uptoTrans:
  assumes "k \<in> upto(m)" and "m \<in> upto(n)" and "n \<in> Nat"
  shows "k \<in> upto(n)"
proof -
  have "\<forall>n\<in>Nat : m \<in> upto(n) \<Rightarrow> upto(m) \<subseteq> upto(n)"
    by (rule natInduct, auto simp: uptoZero uptoSucc)
  with assms show ?thesis by blast
qed

lemma succNotinUpto:
  assumes n: "n \<in> Nat"
  shows "Succ[n] \<notin> upto(n)"
using n proof (induct)
  show "1 \<notin> upto(0)" by (auto simp: uptoZero)
next
  fix n
  assume n: "n \<in> Nat" and ih: "Succ[n] \<notin> upto(n)"
  show "Succ[Succ[n]] \<notin> upto(Succ[n])"
  proof (auto simp: uptoSucc n)
    assume "Succ[Succ[n]] \<in> upto(n)"
    with n have "Succ[n] \<in> upto(n)"
      by (auto elim: uptoPred)
    with ih show "FALSE" ..
  qed
qed

lemma uptoLimit:
  assumes m: "m \<in> upto(n)" and suc: "Succ[m] \<notin> upto(n)" and n: "n \<in> Nat"
  shows "m=n"
proof -
  from m uptoNat have mNat: "m \<in> Nat" by blast
  from n have "\<forall>m\<in>Nat: m \<in> upto(n) \<and> Succ[m] \<notin> upto(n) \<Rightarrow> m=n" (is "?P(n)")
    by (induct, auto simp: uptoZero uptoSucc)
  with mNat m suc show ?thesis by blast
qed

lemma uptoAntisym:
  assumes mn: "m \<in> upto(n)" and nm: "n \<in> upto(m)"
  shows "m=n"
proof -
  from mn uptoNat have m: "m \<in> Nat" by blast
  from nm uptoNat have n: "n \<in> Nat" by blast
  have "\<forall>m,n\<in>Nat : m \<in> upto(n) \<and> n \<in> upto(m) \<Rightarrow> m=n" (is "\<forall>m,n\<in>Nat : ?P(m,n)")
  proof (rule natInduct)
    show "\<forall>n\<in>Nat : ?P(0,n)" by (auto simp: uptoZero)
  next
    fix m
    assume m: "m \<in> Nat" and ih: "\<forall>n\<in>Nat : ?P(m,n)"
    show "\<forall>n\<in>Nat : ?P(Succ[m],n)"
    proof (auto simp: uptoSucc m)
      fix n
      assume "Succ[m] \<in> upto(n)" and "n \<in> upto(m)"
      from this m have "Succ[m] \<in> upto(m)" by (rule uptoTrans)
      with m show "Succ[m] = n" \<comment> \<open>contradiction\<close>
        by (blast dest: succNotinUpto)
    qed
  qed
  with m n mn nm show ?thesis by blast
qed

lemma uptoInj [simp]:
  assumes n: "n \<in> Nat" and m: "m \<in> Nat"
  shows "(upto(n) = upto(m)) = (n = m)"
proof (auto)
  assume 1: "upto(n) = upto(m)"
  from n have "n \<in> upto(n)" by (rule uptoRefl)
  with 1 have "n \<in> upto(m)" by auto
  moreover
  from m have "m \<in> upto(m)" by (rule uptoRefl)
  with 1 have "m \<in> upto(n)" by auto
  ultimately
  show "n = m" by (rule uptoAntisym)
qed

lemma uptoLinear:
  assumes m: "m \<in> Nat" and n: "n \<in> Nat"
  shows "m \<in> upto(n) \<or> n \<in> upto(m)" (is "?P(m,n)")
using m proof induct
  from n show "?P(0,n)" by (auto simp: zeroInUpto)
next
  fix k
  assume k: "k \<in> Nat" and ih: "?P(k,n)"
  from k show "?P(Succ[k],n)"
  proof (auto simp: uptoSucc)
    assume kn: "(Succ[k] \<in> upto(n)) = FALSE"
    show "n \<in> upto(k)"
    proof (rule contradiction)
      assume c: "n \<notin> upto(k)"
      with ih have "k \<in> upto(n)" by simp
      from this kn n have "k = n" by (rule uptoLimit[simplified])
      with n have "n \<in> upto(k)" by (simp add: uptoRefl)
      with c show "FALSE" ..
    qed
  qed
qed


subsection \<open> Primitive Recursive Functions \<close>

text \<open>
  We axiomatize a primitive recursive scheme for functions 
  with one argument and domain on natural numbers. Later, we 
  use it to define addition, multiplication and difference.
\<close>

(** FIXME: replace axiom with proper fixpoint definition **)

axiomatization where
  primrec_nat: "\<exists>f : isAFcn(f) \<and> DOMAIN f = Nat
                   \<and> f[0] = e \<and> (\<forall>n \<in> Nat : f[Succ[n]] = h(n,f[n]))"

lemma bprimrec_nat: 
  assumes e: "e \<in> S" and suc: "\<forall>n \<in> Nat : \<forall>x \<in> S : h(n,x) \<in> S"
  shows "\<exists>f \<in> [Nat \<rightarrow> S] : f[0] = e \<and> (\<forall>n \<in> Nat: f[Succ[n]] = h(n,f[n]))"
proof -
  from primrec_nat[of e h] obtain f where
    1: "isAFcn(f)" and 2: "DOMAIN f = Nat"
    and 3: "f[0] = e" and 4: "\<forall>n\<in>Nat : f[Succ[n]] = h(n,f[n])"
    by blast
  have "\<forall>n\<in>Nat : f[n] \<in> S"
  proof (rule natInduct)
    from 3 e show "f[0] \<in> S" by simp
  next
    fix n
    assume "n \<in> Nat" and "f[n] \<in> S"
    with suc 4 show "f[Succ[n]] \<in> S" by force
  qed
  with 1 2 3 4 show ?thesis
    by blast
qed

lemma primrec_natE:
  assumes e: "e \<in> S" and suc: "\<forall>n \<in> Nat : \<forall>x \<in> S : h(n,x) \<in> S"
  and f: "f = (CHOOSE g \<in> [Nat \<rightarrow> S] : g[0] = e \<and> (\<forall>n \<in> Nat: g[Succ[n]] = h(n,g[n])))"
         (is "f = ?g")
  and maj: "\<lbrakk> f \<in> [Nat \<rightarrow> S]; f[0] = e; \<forall>n \<in> Nat : f[Succ[n]] = h(n, f[n]) \<rbrakk> \<Longrightarrow> P"
  shows "P"
proof -
  from e suc have "\<exists> g \<in> [Nat \<rightarrow> S] : g[0] = e \<and> (\<forall>n \<in> Nat: g[Succ[n]] = h(n,g[n]))"
    by (rule bprimrec_nat)
  hence "?g \<in> [Nat \<rightarrow> S] \<and> ?g[0] = e \<and> (\<forall>n \<in> Nat: ?g[Succ[n]] = h(n,?g[n]))"
    by (rule bChooseI2, auto)
  with f maj show ?thesis by blast
qed

lemma bprimrecType_nat:
  assumes "e \<in> S" and "\<forall>n \<in> Nat : \<forall>x \<in> S : h(n,x) \<in> S"
  shows "(CHOOSE f \<in> [Nat \<rightarrow> S] : f[0] = e \<and> 
                                 (\<forall>n \<in> Nat: f[Succ[n]] = h(n,f[n])))
         \<in> [Nat \<rightarrow> S]"
by (rule primrec_natE[OF assms], auto)

end
