(*  Title:      TLA+/Integers.thy
    Author:     Stephan Merz, LORIA
    Copyright (C) 2008-2021  INRIA and Microsoft Corporation
    License:    BSD
    Version:    Isabelle2021-1
*)

section \<open> The set of integer numbers \<close>

theory Integers
imports FixedPoints Functions
begin

subsection \<open>Extended Peano axioms\<close>

text \<open>
  We extend the standard Peano axioms by a complement operation
  for constructing negative integers, and we prove the existence
  of a structure satisfying these axioms.
\<close>

definition ExtendedPeano :: "[c,c,c,c,c] \<Rightarrow> c" where
  \<comment> \<open>Parameters: the set of integer and natural numbers, zero, 
      and successor and complement functions.\<close>
  "ExtendedPeano(I,N,Z,sc,cp) \<equiv>
      Z \<in> N
   \<and>  sc \<in> [N \<rightarrow> N]
   \<and> (\<forall>n \<in> N : sc[n] \<noteq> Z)
   \<and> (\<forall>m,n \<in> N : sc[m] = sc[n] \<Rightarrow> m = n)
   \<and> (\<forall>S \<in> SUBSET N : Z \<in> S \<and> (\<forall>n\<in>S : sc[n] \<in> S) \<Rightarrow> N \<subseteq> S)
   \<and> cp \<in> [I \<rightarrow> I]
   \<and> I = N \<union> {cp[n] : n \<in> N}
   \<and> cp[Z] = Z
   \<and> (\<forall>k \<in> N : cp[k] \<in> N \<Rightarrow> k = Z)
   \<and> (\<forall>k,l \<in> I : cp[k] = cp[l] \<Rightarrow> k = l)
   \<and> (\<forall>k \<in> I : cp[cp[k]] = k)"

text \<open>
  We now prove the existence of a structure satisfying the
  extended Peano axioms. For @{text N}, we take the standard
  ZF construction where @{text "{}"} is zero, where
  @{text "i \<union> {i}"} is the successor of any natural number
  @{text i}, and where the set @{text N} is defined as
  the least set that contains zero and is closed under successor
  (this is a subset of the infinity set asserted to exist in ZF
  set theory). We then pick a value @{text e} that does not
  occur in the construction of @{text N} and define the
  complement function by adding or removing that value to / from
  the set representing the argument. Later, integers are defined 
  using a sequence of @{text CHOOSE}'s, so there is no commitment 
  to that particular structure.
\<close>

theorem extendedPeanoExists: "\<exists>I,N,Z,sc,cp : ExtendedPeano(I,N,Z,sc,cp)"
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
        with Sc have "Sc[n] \<in> S" by (rule bspec)
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

  define e where "e \<equiv> CHOOSE e : e \<notin> UNION {n : n \<in> N}"
  define cp where "cp \<equiv> \<lambda>n. IF n = Z THEN n ELSE IF e \<in> n THEN n \<setminus> {e} ELSE n \<union> {e}"
  define I where "I \<equiv> N \<union> {cp(n) : n \<in> N}"
  let ?cp = "[k \<in> I \<mapsto> cp(k)]"

  have "\<exists>e : e \<notin> UNION {n : n \<in> N}" by (blast intro: inIrrefl)
  hence "e \<notin> UNION {n : n \<in> N}" unfolding e_def by (rule chooseI_ex)
  hence e: "\<forall>n \<in> N : e \<notin> n" by blast

  have cpZ: "cp(Z) = Z" by (simp add: cp_def)

  have diff: "\<forall>k \<in> I \<setminus> {Z} : cp(k) \<noteq> k"
  proof (clarify)
    fix k
    assume "k \<in> I" "k \<noteq> Z" "cp(k) = k"
    show "FALSE"
    proof (cases "k \<in> N")
      case True
      with e \<open>k \<noteq> Z\<close> \<open>cp(k) = k\<close> show ?thesis 
        by (auto simp: cp_def)
    next
      case False
      with \<open>k \<in> I\<close> obtain n where "n \<in> N" "k = cp(n)" by (auto simp: I_def)
      with \<open>k \<noteq> Z\<close> have "n \<noteq> Z" by (auto simp: cp_def)
      with e \<open>n \<in> N\<close> \<open>k = cp(n)\<close> \<open>k \<noteq> Z\<close> \<open>cp(k) = k\<close> show ?thesis
        by (auto simp: cp_def)
    qed
  qed

  from e have cpN: "\<forall>n \<in> N : cp(cp(n)) = n" 
    by (auto simp: Z_def cp_def)

  from e have cpNN: "\<forall>k \<in> N : cp(k) \<in> N \<Rightarrow> k = Z"
    by (auto simp: cp_def)

  {
    fix k
    assume k: "k \<in> I" "cp(k) = Z"
    have "k = Z"
    proof (cases "k \<in> N")
      case True
      with k 1 cpNN show ?thesis by blast
    next
      case False
      with \<open>k \<in> I\<close> obtain n where "n \<in> N" "k = cp(n)"
        by (auto simp: I_def)
      with \<open>cp(k) = Z\<close> cpN have "n = Z" by auto
      with \<open>k = cp(n)\<close> show ?thesis by (simp add: cp_def)
    qed
  }
  with cpZ have cpisZ: "\<forall>k \<in> I: cp(k) = Z \<Leftrightarrow> k = Z" by blast

  from cpN have cpI: "\<forall>k \<in> I : cp(k) \<in> I" by (auto simp: I_def)
  hence 6: "?cp \<in> [I \<rightarrow> I]" by (rule functionInFuncSet)

  have 7: "I = N \<union> {?cp[n] : n \<in> N}" by (force simp: I_def)

  from cpZ 1 have 8: "?cp[Z] = Z" by (simp add: I_def)

  from cpNN have 9: "\<forall>n \<in> N : ?cp[n] \<in> N \<Rightarrow> n = Z" by (simp add: I_def)

  {
    fix k l
    assume dom: "k \<in> I" "l \<in> I" and eq: "cp(k) = cp(l)" and kl: "k \<noteq> l"
    have "FALSE"
    proof (cases "k \<in> N")
      case True
      have "k \<noteq> Z"
      proof
        assume "k = Z"
        with eq cpZ dom kl cpisZ show "FALSE" by auto
      qed
      with \<open>k \<in> N\<close> e have cpk: "e \<notin> k" "cp(k) = k \<union> {e}" by (auto simp: cp_def)
      have "l \<in> N"
      proof (rule contradiction)
        assume "l \<notin> N"
        with \<open>l \<in> I\<close> obtain n where "n \<in> N" "l = cp(n)"
          by (auto simp: I_def)
        with cpk eq cpN \<open>n \<in> N\<close> e show "FALSE" by force
      qed
      have "l \<noteq> Z"
      proof
        assume "l = Z"
        with eq cpZ dom kl cpisZ show "FALSE" by auto
      qed
      with \<open>l \<in> N\<close> e have "e \<notin> l" "cp(l) = l \<union> {e}" by (auto simp: cp_def)
      with cpk eq have "k \<subseteq> l" "l \<subseteq> k" by force+
      with kl show ?thesis by (auto dest: setEqual)
    next
      case False
      with dom obtain nk where nk: "nk \<in> N" "k = cp(nk)"
        by (auto simp: I_def)
      with cpN eq have cpl: "cp(l) \<in> N" by auto
      have "l \<notin> N"
      proof
        assume "l \<in> N"
        with cpl cpNN have "l = Z" by auto
        with eq dom cpZ cpisZ False 1 show "FALSE" by auto
      qed
      with dom obtain nl where "nl \<in> N" "l = cp(nl)"
        by (auto simp: I_def)
      with nk eq have "cp(cp(nk)) = cp(cp(nl))" by simp
      moreover
      from \<open>nk \<in> N\<close> cpN have "cp(cp(nk)) = nk" by auto
      moreover
      from \<open>nl \<in> N\<close> cpN have "cp(cp(nl)) = nl" by auto
      ultimately have "k = l"
        using \<open>k = cp(nk)\<close> \<open>l = cp(nl)\<close> by simp
      with kl show ?thesis ..
    qed
  }
  hence 10: "\<forall>k,l \<in> I : ?cp[k] = ?cp[l] \<Rightarrow> k = l" by auto

  have 11: "\<forall>k \<in> I : ?cp[?cp[k]] = k"
  proof
    fix k
    assume "k \<in> I"
    with cpI have "?cp[?cp[k]] = cp(cp(k))"
      by force
    moreover have "cp(cp(k)) = k"
    proof (cases "k \<in> N")
      case True
      with cpN show ?thesis by auto
    next
      case False
      with \<open>k \<in> I\<close> obtain nk where "nk \<in> N" "k = cp(nk)"
        by (auto simp: I_def)
      with cpN show ?thesis by auto
    qed
    ultimately show "?cp[?cp[k]] = k" by simp
  qed

  from 1 2 3 4 5 6 7 8 9 10 11 have "ExtendedPeano(I,N,Z,Sc,?cp)"
    unfolding ExtendedPeano_def by blast
  thus ?thesis by blast
qed

subsection \<open>The structure of integer numbers\<close>

text \<open>
  The integer numbers are now defined as some structure
  satisfying the extended Peano axioms.
\<close>

definition Succ :: "c"  where
  "Succ \<equiv> CHOOSE sc : \<exists>cp,I,N,Z : ExtendedPeano(I,N,Z,sc,cp)"

definition Nat :: "c"   where 
  "Nat \<equiv> DOMAIN Succ"

definition zero :: "c" ("0")  where
  "zero \<equiv> CHOOSE Z : \<exists>cp,I : ExtendedPeano(I,Nat,Z,Succ,cp)"

definition intCplt :: "c" where
  "intCplt \<equiv> CHOOSE cp : \<exists>I : ExtendedPeano(I,Nat,zero,Succ,cp)"

definition Int :: "c"   where
  "Int \<equiv> DOMAIN intCplt"

definition uminus :: "c \<Rightarrow> c" ("-_" [80] 80) where
  "-z \<equiv> intCplt[z]"

lemmas
  setEqualI [where A = "Nat", intro!]
  setEqualI [where B = "Nat", intro!]
  setEqualI [where A = "Int", intro!]
  setEqualI [where B = "Int", intro!]
  setEqualE [where A = "Nat", elim]
  setEqualE [where B = "Nat", elim]
  setEqualE [where A = "Int", elim]
  setEqualE [where B = "Int", elim]

lemma intExtendedPeano: "ExtendedPeano(Int,Nat,0,Succ,intCplt)"
proof -
  have "\<exists>cp,I,N,Z : ExtendedPeano(I,N,Z,Succ,cp)"
  proof (unfold Succ_def, rule chooseI_ex)
    from extendedPeanoExists 
    show "\<exists>Sc,cp,I,N,Z : ExtendedPeano(I,N,Z,Sc,cp)" by blast
  qed
  then obtain N Z where PNZ: "\<exists>cp,I : ExtendedPeano(I,N,Z,Succ,cp)" by blast
  hence "Succ \<in> [N \<rightarrow> N]"
    by (simp add: ExtendedPeano_def)
  hence "N = Nat"
    by (simp add: Nat_def)
  with PNZ have "\<exists>cp,I : ExtendedPeano(I,Nat,Z,Succ,cp)" by simp
  hence "\<exists>cp,I : ExtendedPeano(I,Nat,0,Succ,cp)"
    unfolding zero_def by (rule chooseI)
  hence "\<exists>I : ExtendedPeano(I,Nat,0,Succ,intCplt)"
    unfolding intCplt_def by (rule chooseI_ex)
  then obtain I where IEP: "ExtendedPeano(I,Nat,0,Succ,intCplt)"
    by blast
  hence "intCplt \<in> [I \<rightarrow> I]"
    by (auto simp: ExtendedPeano_def)
  hence "I = Int"
    by (simp add: Int_def)
  with IEP show ?thesis by simp
qed

lemma natIsInt [simp,intro]: "n \<in> Nat \<Longrightarrow> n \<in> Int"
  using intExtendedPeano by (auto simp: ExtendedPeano_def)

lemma uminusIsInt [simp,intro!]: "n \<in> Int \<Longrightarrow> -n \<in> Int"
  using intExtendedPeano by (auto simp: ExtendedPeano_def uminus_def)

text \<open>
  Fundamental lemmas about zero, successor, and complement.
\<close>

lemma zeroIsNat [intro!,simp]: "0 \<in> Nat"
  using intExtendedPeano by (simp add: ExtendedPeano_def)

(* redundant, but will become relevant later *)
lemma zeroIsInt [intro!,simp]: "0 \<in> Int"
  by simp

lemma SuccInNatNat [intro!,simp]: "Succ \<in> [Nat \<rightarrow> Nat]"
  using intExtendedPeano by (simp add: ExtendedPeano_def)

lemma SuccIsAFcn [intro!,simp]: "isAFcn(Succ)"
  using SuccInNatNat by blast

\<comment> \<open>@{text "DOMAIN Succ = Nat"}\<close>
lemmas domainSucc [intro!,simp] = funcSetDomain[OF SuccInNatNat]
\<comment> \<open>@{text "n \<in> Nat \<Longrightarrow> Succ[n] \<in> Nat"}\<close>
lemmas SuccIsNat [intro!,simp] = funcSetValue[OF SuccInNatNat]

lemma [simp]:
  assumes "n \<in> Nat"
  shows "(Succ[n] = 0) = FALSE"
  using assms intExtendedPeano by (auto simp: ExtendedPeano_def)

lemma [simp]:
  assumes n: "n \<in> Nat"
  shows "(0 = Succ[n]) = FALSE"
  using assms by (auto dest: sym)

lemma SuccNotZero (*[elim] \<comment> don't: produces "ignoring weak elimination rule"*):
  "\<lbrakk>Succ[n] = 0; n \<in> Nat\<rbrakk> \<Longrightarrow> P"
  "\<lbrakk>0 = Succ[n]; n \<in> Nat\<rbrakk> \<Longrightarrow> P"
by (simp+)

lemma SuccInj [dest]:
  assumes "Succ[m] = Succ[n]" and "m \<in> Nat" and "n \<in> Nat"
  shows "m=n"
  using assms intExtendedPeano by (auto simp: ExtendedPeano_def)

lemma SuccInjIff [simp]:
  assumes "m \<in> Nat" and "n \<in> Nat"
  shows "(Succ[m] = Succ[n]) = (m = n)"
using assms by auto

\<comment> \<open>The primitive induction rule for natural numbers, will be superseded below.\<close>
lemma pr_natInduct:
  assumes z: "P(0)"
  and sc: "\<And>n. \<lbrakk>n \<in> Nat; P(n)\<rbrakk> \<Longrightarrow> P(Succ[n])"
  shows "\<forall>n\<in>Nat : P(n)"
proof -
  let ?P = "{n \<in> Nat : P(n)}"
  have "?P \<in> SUBSET Nat" by auto
  moreover
  from z have "0 \<in> ?P" by simp
  moreover
  from sc have "\<forall>n \<in> ?P : Succ[n] \<in> ?P" by simp
  moreover
  have "\<forall>S \<in> SUBSET Nat : 0 \<in> S \<and> (\<forall>n \<in> S : Succ[n] \<in> S) \<Rightarrow> Nat \<subseteq> S"
    using intExtendedPeano by (simp add: ExtendedPeano_def)
  ultimately have "Nat \<subseteq> ?P"
    by blast
  thus ?thesis by auto
qed

lemma pr_natCases:
  assumes n: "n \<in> Nat"
      and 0: "n = 0 \<Longrightarrow> P"
      and suc: "\<And>m. \<lbrakk>m \<in> Nat; n = Succ[m]\<rbrakk> \<Longrightarrow> P"
  shows "P"
proof -
  have "\<forall>n \<in> Nat : n = 0 \<or> (\<exists>m \<in> Nat : n = Succ[m])"
    by (rule pr_natInduct) auto
  with assms show ?thesis by blast
qed

lemma [simp]: "-0 = 0"
  using intExtendedPeano by (simp add: ExtendedPeano_def uminus_def)

lemma uminusNat [simp]:
  assumes "n \<in> Nat"
  shows "(-n \<in> Nat) = (n = 0)"
proof -
  {
    assume "-n \<in> Nat"
    with assms intExtendedPeano have "n = 0"
      by (auto simp: ExtendedPeano_def uminus_def)
  }
  thus ?thesis by auto
qed

lemma uminusInj [dest]:
  assumes "-a = -b" and "a \<in> Int" and "b \<in> Int"
  shows "a = b"
  using assms intExtendedPeano 
  unfolding ExtendedPeano_def uminus_def by blast

lemma uminusInjIff [simp]:
  "\<lbrakk>a \<in> Int; b \<in> Int\<rbrakk> \<Longrightarrow> (-a = -b) = (a = b)"
  by auto

lemma uminusUminus [simp]:
  assumes "a \<in> Int"
  shows "--a = a"
proof -
  from intExtendedPeano have "\<forall>k \<in> Int : intCplt[intCplt[k]] = k"
    by (simp add: ExtendedPeano_def)
  with assms show ?thesis
    by (auto simp add: uminus_def)
qed

lemma uminusSwap:
  assumes "a \<in> Int" and "b \<in> Int"
  shows "(-a = b) = (a = -b)"
proof -
  from assms have "(-a = b) = (--a = -b)" by auto
  with assms show ?thesis by simp
qed

lemma intElim:
  assumes n: "n \<in> Int"
  and pos: "n \<in> Nat \<Longrightarrow> P" and neg: "\<And>m. \<lbrakk>m \<in> Nat; n = -m\<rbrakk> \<Longrightarrow> P"
  shows "P"
  using assms intExtendedPeano by (auto simp: ExtendedPeano_def uminus_def)

lemma uminusZero [simp]:
  assumes "a \<in> Int"
  shows "(-a = 0) = (a = 0)"
  using assms by (simp add: uminusSwap)

lemma uminusZero' [simp]:
  assumes "a \<in> Int"
  shows "(0 = -a) = (a = 0)"
using assms by (auto dest: sym)

lemma uminusReflZero:
  assumes "a \<in> Int" "-a = a"
  shows "a = 0"
proof -
  {
    fix k
    assume "k \<in> Nat" "-k = k"
    hence "-k \<in> Nat" by simp
    with \<open>k \<in> Nat\<close> have "k = 0" by simp
  }
  from assms this show ?thesis 
    by (elim intElim) (force+)
qed

lemma [simp]:
  "a \<in> Int \<Longrightarrow> (-a = a) = (a = 0)"
  "a \<in> Int \<Longrightarrow> (a = -a) = (a = 0)"
  by (auto dest: uminusReflZero)

lemma pr_intCases:
  assumes a: "a \<in> Int"
      and 0: "a = 0 \<Longrightarrow> P"
      and pos: "\<And>n. \<lbrakk> n \<in> Nat; a = Succ[n] \<rbrakk> \<Longrightarrow> P"
      and neg: "\<And>n. \<lbrakk> n \<in> Nat; a = -Succ[n] \<rbrakk> \<Longrightarrow> P"
  shows "P"
using a proof (rule intElim)
  assume "a \<in> Nat" 
  with 0 pos show ?thesis by (auto elim: pr_natCases)
next
  fix m
  assume "m \<in> Nat" "a = -m"
  with 0 neg show ?thesis by (auto elim: pr_natCases)
qed


subsection \<open>Successor and predecessor on integer numbers.\<close>

text \<open>
  We extend the successor function for the set of integer numbers
  and define the predecessor function as its inverse. These
  functions are denoted @{text "succ"} and @{text "pred"} and will
  replace the primitive function @{text "Succ"} for reasoning
  about integers.
\<close>

definition succ where
  "succ \<equiv> [a \<in> Int \<mapsto> IF a \<in> Nat THEN Succ[a] 
                      ELSE -(CHOOSE m \<in> Nat : a = -Succ[m])]"

abbreviation "one \<equiv> succ[0]"
notation "one" ("1")
(*
abbreviation "two \<equiv> succ[1]"
notation "two"                        ("2")
abbreviation "three \<equiv> succ[2]"
notation "three"                      ("3")
abbreviation "four \<equiv> succ[3]"
notation "four"                       ("4")
abbreviation "five \<equiv> succ[4]"
notation "five"                       ("5")
abbreviation "six \<equiv> succ[5]"
notation "six"                        ("6")
abbreviation "seven \<equiv> succ[6]"
notation "seven"                      ("7")
abbreviation "eight \<equiv> succ[7]"
notation "eight"                      ("8")
abbreviation "nine \<equiv> succ[8]"
notation "nine"                       ("9")
abbreviation "ten \<equiv> succ[9]"
notation "ten"                       ("10")
abbreviation "eleven \<equiv> succ[10]"
notation "eleven"                    ("11")
abbreviation "twelve \<equiv> succ[11]"
notation "twelve"                    ("12")
abbreviation "thirteen \<equiv> succ[12]"
notation "thirteen"                  ("13")
abbreviation "fourteen \<equiv> succ[13]"
notation "fourteen"                  ("14")
abbreviation "fifteen \<equiv> succ[14]"
notation "fifteen"                   ("15")
*)

definition two :: "c" ("2")
    where "2 \<equiv> succ[1]"
definition three :: "c" ("3")
    where "3 \<equiv> succ[2]"
definition four :: "c" ("4")
    where "4 \<equiv> succ[3]"
definition five :: "c" ("5")
    where "five \<equiv> succ[4]"
definition six :: "c" ("6")
    where "six \<equiv> succ[5]"
definition seven :: "c" ("7")
    where "seven \<equiv> succ[6]"
definition eight :: "c" ("8")
    where "eight \<equiv> succ[7]"
definition nine :: "c" ("9")
    where "nine \<equiv> succ[8]"
definition ten :: "c" ("10")
    where "ten \<equiv> succ[9]"
definition eleven :: "c" ("11")
    where "eleven \<equiv> succ[10]"
definition twelve :: "c" ("12")
    where "twelve \<equiv> succ[11]"
definition thirteen :: "c" ("13")
    where "thirteen \<equiv> succ[12]"
definition fourteen :: "c" ("14")
    where "fourteen \<equiv> succ[13]"
definition fifteen :: "c" ("15")
    where "fifteen \<equiv> succ[14]"

lemma succType: "succ \<in> [Int \<rightarrow> Int]"
proof -
  {
    fix a
    assume "a \<in> Int"
    hence "succ[a] \<in> Int"
      by (rule pr_intCases) (auto simp: succ_def intro: bChooseI2)
  }
  thus ?thesis by (auto simp: succ_def)
qed

lemma succIsAFcn [intro!,simp]: "isAFcn(succ)"
  using succType by blast

\<comment> \<open>@{text "DOMAIN succ = Int"}\<close>
lemmas [intro!,simp] = funcSetDomain[OF succType]
\<comment> \<open>@{text "a \<in> Int \<Longrightarrow> succ[a] \<in> Int"}\<close>
lemmas [intro!,simp] = funcSetValue[OF succType]

lemma succIsSucc: "n \<in> Nat \<Longrightarrow> succ[n] = Succ[n]"
  by (simp add: succ_def)

lemma succUminusSuccNat: "n \<in> Nat \<Longrightarrow> succ[-succ[n]] = -n"
  by (auto simp: succ_def intro: bChooseI2)

lemma succUminusSucc [simp]:
  assumes "a \<in> Int"
  shows "succ[-succ[a]] = -a"
using assms proof (rule pr_intCases)
  fix n
  assume n: "n \<in> Nat" "a = -Succ[n]"
  hence "succ[a] = -n"
    by (simp add: sym[OF succIsSucc] succUminusSuccNat)
  with n show ?thesis
    by (simp add: succIsSucc)
qed (simp add: succUminusSuccNat)+

lemma succInNat [simp]:
  assumes "a \<in> Int"
  shows "(succ[a] \<in> Nat) = (a \<in> Nat \<union> {-1})"
proof -
  {
    assume "a \<in> Nat" hence "succ[a] \<in> Nat"
      by (simp add: succIsSucc)
  }
  moreover
  {
    assume "a = -1" hence "succ[a] \<in> Nat"
      by simp
  }
  moreover
  {
    assume s: "succ[a] \<in> Nat"
    from assms have "a \<in> Nat \<union> {-1}"
    proof (rule pr_intCases)
      fix n
      assume "n \<in> Nat" "a = -Succ[n]"
      with s show ?thesis by (simp add: sym[OF succIsSucc])
    qed (simp+)
  }
  ultimately show ?thesis by blast
qed

lemma succIsUminus [simp]:
  assumes a: "a \<in> Int" and b: "b \<in> Int"
  shows "(succ[a] = -b) = (a = -succ[b])"
proof -
  {
    assume "succ[a] = -b"
    with b have "succ[b] = succ[-succ[a]]" by simp
    also from a have "\<dots> = -a" by simp
    finally have "a = -succ[b]" using a by simp
  }
  with assms show ?thesis by auto
qed

lemma uminusIsSucc [simp]:
  assumes a: "a \<in> Int" and b: "b \<in> Int"
  shows "(-a = succ[b]) = (b = -succ[a])"
  using assms by (auto simp: uminusSwap)

lemma succIs0:  (* better not add to simp *)
  assumes "a \<in> Int"
  shows "(succ[a] = 0) = (a = -1)"
proof -
  from assms have "(succ[a] = -0) = (a = -1)"
    by (rule succIsUminus) simp
  thus ?thesis by simp
qed

lemma zeroIsSucc:
  assumes "a \<in> Int"
  shows "(0 = succ[a]) = (a = -1)"
  by (auto simp: sym[OF succIs0[OF assms]])

lemma succNatNotZero (*[elim] -- "ignoring weak elimination rule" *):
  "\<lbrakk>succ[n] = 0; n \<in> Nat\<rbrakk> \<Longrightarrow> P"
  "\<lbrakk>0 = succ[n]; n \<in> Nat\<rbrakk> \<Longrightarrow> P"
  by (auto simp: succIsSucc)

lemma succNatZeroIff [simp]:
  "n \<in> Nat \<Longrightarrow> (succ[n] = 0) = FALSE"
  "n \<in> Nat \<Longrightarrow> (0 = succ[n]) = FALSE"
  by (auto simp: succIsSucc)

lemma succInj [dest]:
  assumes eq: "succ[a] = succ[b]" and a: "a \<in> Int" and b: "b \<in> Int"
  shows "a = b"
using a proof (rule pr_intCases)
  assume a0: "a = 0"
  from b show ?thesis
  proof (rule pr_intCases)
    assume "b = 0" with a0 show ?thesis by simp
  next
    fix n
    assume "n \<in> Nat" "b = Succ[n]"
    with a0 eq show ?thesis by (simp add: succIsSucc)
  next
    fix n
    assume "n \<in> Nat" "b = -Succ[n]"
    with a0 eq show ?thesis by (simp add: sym[OF succIsSucc])
  qed
next
  fix n
  assume n: "n \<in> Nat" "a = Succ[n]"
  from b show ?thesis
  proof (rule pr_intCases)
    assume "b = 0"
    with n eq show ?thesis by (simp add: succIsSucc)
  next
    fix m
    assume "m \<in> Nat" "b = Succ[m]"
    with n eq show ?thesis by (simp add: succIsSucc)
  next
    fix m
    assume "m \<in> Nat" "b = -Succ[m]"
    with n eq show ?thesis by (simp add: sym[OF succIsSucc])
  qed
next
  fix n
  assume n: "n \<in> Nat" "a = -Succ[n]"
  from b show ?thesis
  proof (rule pr_intCases)
    assume "b = 0"
    with n eq show ?thesis by (simp add: sym[OF succIsSucc])
  next
    fix m
    assume "m \<in> Nat" "b = Succ[m]"
    with n eq show ?thesis by (simp add: sym[OF succIsSucc])
  next
    fix m
    assume "m \<in> Nat" "b = -Succ[m]"
    with n eq show ?thesis by (simp add: sym[OF succIsSucc])
  qed
qed

lemma succInjIff [simp]:
  assumes "a \<in> Int" and "b \<in> Int"
  shows "(succ[a] = succ[b]) = (a = b)"
  using assms by auto

lemma intIsSucc:
  assumes "a \<in> Int"
  shows "\<exists>b \<in> Int : a = succ[b]"
using assms proof (rule pr_intCases)
  assume "a = 0"
  hence "a = succ[-1]" by simp
  moreover have "-1 \<in> Int" by simp
  ultimately show ?thesis by blast
next
  fix n
  assume n: "n \<in> Nat" "a = Succ[n]"
  hence "a = succ[n]" by (simp add: succIsSucc)
  with n show ?thesis by blast
next
  fix n
  assume n: "n \<in> Nat" "a = -Succ[n]"
  hence "a = succ[-succ[Succ[n]]]" by simp
  with n show ?thesis by auto
qed

definition pred where
  "pred = [a \<in> Int \<mapsto> CHOOSE b \<in> Int : a = succ[b]]"

lemma predType: "pred \<in> [Int \<rightarrow> Int]"
  unfolding pred_def by (auto intro: intIsSucc[THEN bChooseI2])

lemma predIsAFcn [intro!,simp]: "isAFcn(pred)"
  using predType by blast

\<comment> \<open>@{text "DOMAIN pred = Int"}\<close>
lemmas [intro!,simp] = funcSetDomain[OF predType]
\<comment> \<open>@{text "a \<in> Int \<Longrightarrow> pred[a] \<in> Int"}\<close>
lemmas [intro!,simp] = funcSetValue[OF predType]

lemma predValue:
  assumes "b \<in> Int" and "a = succ[b]"
  shows "b = pred[a]"
  using assms unfolding pred_def by (auto intro: bChooseI)

lemma pred0: "pred[0] = -1"
  by (rule sym[OF predValue]) auto

lemma predSucc [simp]: 
  assumes "a \<in> Int"
  shows "pred[succ[a]] = a"
  by (rule predValue[OF assms, THEN sym, OF refl])

lemma succPred [simp]:
  assumes "a \<in> Int"
  shows "succ[pred[a]] = a"
  using assms unfolding pred_def by (auto intro: intIsSucc[THEN bChooseI2])

lemma predInj [dest]:
  assumes eq: "pred[a] = pred[b]" and ab: "a \<in> Int" "b \<in> Int"
  shows "a = b"
proof -
  from eq have "succ[pred[a]] = succ[pred[b]]"
    by simp
  with ab show ?thesis by simp
qed

lemma predInjIff [simp]:
  assumes "a \<in> Int" and "b \<in> Int"
  shows "(pred[a] = pred[b]) = (a = b)"
  using assms by auto

lemma uminusSucc (*[simp]*):
  assumes "a \<in> Int"
  shows "-succ[a] = pred[-a]"
proof -
  from assms have "succ[-succ[a]] = succ[pred[-a]]"
    by simp
  with assms show ?thesis
    by blast
qed

lemma uminusPred (*[simp]*):
  assumes "a \<in> Int"
  shows "-pred[a] = succ[-a]"
  using assms by auto

text \<open>
  We restate the induction and case splitting theorems for
  natural numbers and integers in terms of @{text "succ"} and
  @{text "pred"}.
\<close>
lemma natInduct:
  assumes "P(0)" and "\<And>n. \<lbrakk> n \<in> Nat; P(n) \<rbrakk> \<Longrightarrow> P(succ[n])"
  shows "\<forall>n \<in> Nat : P(n)"
  using assms by (intro pr_natInduct) (auto simp: succIsSucc)

\<comment> \<open>version of above suitable for the inductive reasoning package\<close>
lemma natInductE [case_names 0 Succ, induct set: Nat]:
  assumes "n \<in> Nat" and "P(0)" and "\<And>n. \<lbrakk>n \<in> Nat; P(n)\<rbrakk> \<Longrightarrow> P(succ[n])"
  shows "P(n)"
using bspec[OF natInduct, where P=P] assms by blast

(*** EXAMPLE INDUCTION PROOFS ***

lemma "\<forall>n\<in>Nat : n=0 \<or> (\<exists>m \<in> Nat : n = succ[m])"
by (rule natInduct, auto)

lemma
  assumes 1: "n \<in> Nat"
  shows "n=0 \<or> (\<exists>m \<in> Nat : n = succ[m])"
using 1 by (induct, auto)

*** END EXAMPLE ***)

lemma natCases [case_names 0 succ, cases set: Nat]:
  assumes n: "n \<in> Nat"
  and z: "n=0 \<Longrightarrow> P" and sc: "\<And>m. \<lbrakk>m \<in> Nat; n = succ[m]\<rbrakk> \<Longrightarrow> P"
  shows "P"
proof -
  from n have "n=0 \<or> (\<exists>m \<in> Nat : n = succ[m])"
    by (induct, auto)
  thus ?thesis
  proof
    assume "n=0" thus "P" by (rule z)
  next
    assume "\<exists>m\<in>Nat : n = succ[m]"
    then obtain m where "m \<in> Nat" and "n = succ[m]" ..
    thus "P" by (rule sc)
  qed
qed

lemma not0_implies_Suc:
  "\<lbrakk>n \<in> Nat; n \<noteq> 0\<rbrakk> \<Longrightarrow> \<exists>m \<in> Nat: n = succ[m]"
  by (rule natCases) auto

text \<open>Induction over two parameters along the ``diagonal''.\<close>
lemma diffInduction:
  assumes b1: "\<forall>m\<in>Nat : P(m,0)" and b2: "\<forall>n\<in>Nat : P(0, succ[n])"
  and step: "\<forall>m,n\<in>Nat : P(m,n) \<Rightarrow> P(succ[m], succ[n])"
  shows "\<forall>m,n\<in>Nat : P(m,n)"
proof (rule natInduct)
  show "\<forall>n\<in>Nat : P(0,n)"
    using b1 b2 by (intro natInduct) auto
next
  fix m
  assume m: "m \<in> Nat" and ih: "\<forall>n\<in>Nat : P(m,n)"
  show "\<forall>n\<in>Nat : P(succ[m],n)"
  proof (rule bAllI)
    fix n
    assume "n \<in> Nat" thus "P(succ[m],n)"
    proof (cases)
      case 0 with b1 m show ?thesis by force
    next
      case succ with step ih m show ?thesis by auto
    qed
  qed
qed

lemma diffInduct:
  assumes n: "n \<in> Nat" and m: "m \<in> Nat"
  and b1: "\<And>m. m\<in>Nat \<Longrightarrow> P(m,0)" and b2: "\<And>n. n\<in>Nat \<Longrightarrow> P(0, succ[n])"
  and step: "\<And>m n. \<lbrakk>m \<in> Nat; n\<in>Nat; P(m,n) \<rbrakk> \<Longrightarrow> P(succ[m], succ[n])"
  shows "P(m,n)"
proof -
  have "\<forall>m,n\<in>Nat : P(m,n)"
    by (rule diffInduction, auto intro: b1 b2 step)
  with n m show ?thesis by blast
qed

lemma intInduct:
  assumes z: "P(0)"
  and pos: "\<And>n. \<lbrakk>n \<in> Nat; P(n); P(-n)\<rbrakk> \<Longrightarrow> P(succ[n])"
  and neg: "\<And>n. \<lbrakk>n \<in> Nat; P(n); P(-n)\<rbrakk> \<Longrightarrow> P(-succ[n])"
  shows "\<forall>a\<in>Int : P(a)"
proof -
  from assms have 1: "\<forall>n \<in> Nat : P(n) \<and> P(-n)"
    by (intro natInduct) auto
  show ?thesis
  proof
    fix a
    assume "a \<in> Int"
    from this 1 show "P(a)"
      by (elim intElim) auto
  qed
qed

\<comment> \<open>turn the above lemma into an induction method\<close>
lemma intInductE [case_names 0 pos neg, induct set: Int]:
  assumes "a \<in> Int" and "P(0)"
    and "\<And>n. \<lbrakk>n \<in> Nat; P(n); P(-n)\<rbrakk> \<Longrightarrow> P(succ[n])"
    and "\<And>n. \<lbrakk>n \<in> Nat; P(n); P(-n)\<rbrakk> \<Longrightarrow> P(-succ[n])"
  shows "P(a)"
  using bspec[OF intInduct, where P=P] assms by blast

lemma intZeroPosNeg:
  assumes "a \<in> Int"
  shows "a = 0 \<or> (\<exists>n \<in> Nat : a = succ[n]) \<or> (\<exists>n \<in> Nat : a = -succ[n])"
using assms by (induct a) auto

lemma intCases [case_names 0 pos neg, cases set: Int]:
  assumes "a \<in> Int"
    and "a = 0 \<Longrightarrow> P"
    and "\<And>n. \<lbrakk>n \<in> Nat; a = succ[n]\<rbrakk> \<Longrightarrow> P" 
    and "\<And>n. \<lbrakk>n \<in> Nat; a = -succ[n]\<rbrakk> \<Longrightarrow> P"
  shows "P"
  using assms by (blast dest: intZeroPosNeg)

lemma succIrrefl:
  assumes "a \<in> Int"
  shows "succ[a] \<noteq> a"
  using assms by induct auto

lemma succIrreflE (*[elim] -- don't: "ignoring weak elimination rule" *):
  "\<lbrakk>succ[a] = a; a \<in> Int\<rbrakk> \<Longrightarrow> P"
  "\<lbrakk>a = succ[a]; a \<in> Int\<rbrakk> \<Longrightarrow> P"
by (auto dest: succIrrefl)

lemma succIrrefl_iff [simp]:
  "a \<in> Int \<Longrightarrow> (succ[a] = a) = FALSE"
  "a \<in> Int \<Longrightarrow> (a = succ[a]) = FALSE"
by (auto dest: succIrrefl)

lemma predIrrefl:
  assumes "a \<in> Int"
  shows "pred[a] \<noteq> a"
proof
  assume "pred[a] = a"
  hence "succ[pred[a]] = succ[a]" by simp
  with assms show "FALSE" by simp
qed

lemma predIrreflE (*[elim]*):
  "\<lbrakk>pred[a] = a; a \<in> Int\<rbrakk> \<Longrightarrow> P"
  "\<lbrakk>a = pred[a]; a \<in> Int\<rbrakk> \<Longrightarrow> P"
by (auto dest: predIrrefl)

lemma predIrrefl_iff [simp]:
  "a \<in> Int \<Longrightarrow> (pred[a] = a) = FALSE"
  "a \<in> Int \<Longrightarrow> (a = pred[a]) = FALSE"
by (auto dest: predIrrefl)

lemma predInNat [simp]:
  assumes "a \<in> Int"
  shows "(pred[a] \<in> Nat) = (a \<in> Nat \<setminus> {0})"
  using assms by cases (auto simp: pred0 sym[OF uminusSucc])

lemma succNatNotNeg [simp]:
  assumes "m \<in> Nat" and "n \<in> Nat"
  shows "(succ[m] = -n) = FALSE" "(n = -succ[m]) = FALSE"
        "(-n = succ[m]) = FALSE" "(-succ[m] = n) = FALSE"
  using assms by auto


subsection \<open> Initial intervals of natural numbers \<close>

text \<open>
  The set of natural numbers up to (and including) a given $n$ is
  inductively defined as the smallest set of natural numbers that
  contains $n$ and all numbers whose successor is in the set.

  NB: ``less than'' is not first-order definable from the Peano axioms,
  a set-theoretic definition such as the following seems to be unavoidable.
\<close>

definition upto :: "c \<Rightarrow> c"
where "upto(n) \<equiv> lfp(Nat, \<lambda>S. {n} \<union> { k \<in> Nat : succ[k] \<in> S })"

lemmas
  setEqualI [where A = "upto(n)" for n, intro!]
  setEqualI [where B = "upto(n)" for n, intro!]
  setEqualE [where A = "upto(n)" for n, elim]
  setEqualE [where B = "upto(n)" for n, elim]

lemma uptoNat: "upto(n) \<subseteq> Nat"
  unfolding upto_def by (rule lfpSubsetDomain)

lemma uptoPred:
  assumes suc: "succ[m] \<in> upto(n)" and m: "m \<in> Nat" and n: "n \<in> Nat"
  shows "m \<in> upto(n)"
proof -
  let ?f = "\<lambda>S. {n} \<union> {k\<in>Nat : succ[k] \<in> S}"
  from n have mono: "Monotonic(Nat, ?f)"
    unfolding Monotonic_def by blast
  from m suc have 1: "m \<in> ?f(upto(n))" by auto
  from mono have 2: "?f(upto(n)) \<subseteq> upto(n)"
    unfolding upto_def by (rule lfpPreFP)
  from 1 2 show ?thesis by blast
qed

lemma uptoZero: "upto(0) = {0}"
proof (rule setEqual)
  have "{0} \<union> { k \<in> Nat : succ[k] \<in> {0} } \<subseteq> {0}" by auto
  thus "upto(0) \<subseteq> {0}"
    unfolding upto_def by (rule lfpLB, auto)
next
  show "{0} \<subseteq> upto(0)"
    unfolding upto_def by (rule lfpGLB, auto)
qed

lemma uptoSucc:
  assumes n: "n \<in> Nat"
  shows "upto(succ[n]) = upto(n) \<union> {succ[n]}" (is "?lhs = ?rhs")
proof -
  let ?preds = "\<lambda>S. {k \<in> Nat : succ[k] \<in> S}"
  let ?f = "\<lambda>S k. {k} \<union> ?preds(S)"
  have mono: "\<And>k. k \<in> Nat \<Longrightarrow> Monotonic(Nat, \<lambda>S. ?f(S,k))"
    by (auto simp: Monotonic_def)
  \<comment> \<open>``$\subseteq$''\<close>
  from n have "?preds(?rhs) \<subseteq> ?f(upto(n), n)" by auto
  also have "\<dots> \<subseteq> upto(n)"
    by (unfold upto_def, rule lfpPreFP, rule mono, rule n)
  finally have "?f(?rhs, succ[n]) \<subseteq> ?rhs" by auto
  moreover from n have "?rhs \<subseteq> Nat"
    by (intro unionLUB, auto elim: uptoNat[THEN subsetD])
  ultimately have 1: "?lhs \<subseteq> ?rhs"
    by (unfold upto_def[where n="succ[n]"], rule lfpLB)
  \<comment> \<open>``$\supseteq$''\<close>
  from n mono have 2: "?f(?lhs, succ[n]) \<subseteq> ?lhs"
    unfolding upto_def by (intro lfpPreFP) auto
  with n have "?f(?lhs, n) \<subseteq> ?lhs" by auto
  moreover have "?lhs \<subseteq> Nat" by (rule uptoNat)
  ultimately have 3: "upto(n) \<subseteq> ?lhs"
    unfolding upto_def[where n=n] by (rule lfpLB)
  from 2 have 4: "succ[n] \<in> ?lhs" by auto
  from 3 4 have "?rhs \<subseteq> ?lhs" by auto
  with 1 show ?thesis by (rule setEqual)
qed

lemma uptoRefl:
  assumes n: "n \<in> Nat"
  shows "n \<in> upto(n)"
using n proof (cases)
  case 0 thus ?thesis by (simp add: uptoZero)
next
  case (succ m) thus ?thesis by (auto simp: uptoSucc)
qed

lemma zeroInUpto:
  assumes n: "n \<in> Nat"
  shows "0 \<in> upto(n)"
using n by (induct, auto simp: uptoZero uptoSucc)

lemma SuccNotUptoZero:
  assumes "n \<in> Nat" and "succ[n] \<in> upto(0)"
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
  shows "succ[n] \<notin> upto(n)"
using n proof (induct)
  show "1 \<notin> upto(0)" by (auto simp: uptoZero)
next
  fix n
  assume n: "n \<in> Nat" and ih: "succ[n] \<notin> upto(n)"
  show "succ[succ[n]] \<notin> upto(succ[n])"
  proof (auto simp: uptoSucc n)
    assume "succ[succ[n]] \<in> upto(n)"
    with n have "succ[n] \<in> upto(n)"
      by (auto elim: uptoPred)
    with ih show "FALSE" ..
  qed
qed

lemma uptoLimit:
  assumes m: "m \<in> upto(n)" and suc: "succ[m] \<notin> upto(n)" and n: "n \<in> Nat"
  shows "m=n"
proof -
  from m uptoNat have mNat: "m \<in> Nat" by blast
  from n have "\<forall>m\<in>Nat: m \<in> upto(n) \<and> succ[m] \<notin> upto(n) \<Rightarrow> m=n" (is "?P(n)")
    by (induct, (force simp add: uptoZero uptoSucc)+)
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
    show "\<forall>n\<in>Nat : ?P(succ[m],n)"
    proof (auto simp: uptoSucc m)
      fix n
      assume "succ[m] \<in> upto(n)" and "n \<in> upto(m)"
      from this m have "succ[m] \<in> upto(m)" by (rule uptoTrans)
      with m show "succ[m] = n" \<comment> \<open>contradiction\<close>
        by (blast dest: succNotinUpto)
    qed
  qed
  with m n mn nm show ?thesis by blast
qed

lemma uptoInj:
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
  from k show "?P(succ[k],n)"
  proof (auto simp: uptoSucc)
    assume kn: "(succ[k] \<in> upto(n)) = FALSE"
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

lemma uptoInduct:
  assumes n: "n \<in> Nat"
      and base: "P(0)"
      and step: "\<And>m. \<lbrakk>m \<in> Nat; m \<in> upto(n) \<Rightarrow> P(m); succ[m] \<in> upto(n)\<rbrakk> \<Longrightarrow> P(succ[m])"
  shows "\<forall>m \<in> upto(n) : P(m)"
proof -
  have "\<forall>m \<in> Nat: m \<in> upto(n) \<Rightarrow> P(m)"
    by (rule natInduct) (auto simp: base dest: step)
  with uptoNat show ?thesis by auto
qed


subsection \<open> Primitive recursive functions over natural numbers \<close>

text \<open>
  We justify the definition of function over natural numbers by
  primitive recursion. The idea is to construct a sequence of
  approximations, and then obtain the function by diagonalization.
\<close>

definition primrec_nat_upto where
  "primrec_nat_upto(base, step, f, n) \<equiv>
     isAFcn(f) \<and> DOMAIN f = Nat
   \<and> f[0] = base
   \<and> (\<forall>m \<in> Nat : succ[m] \<in> upto(n) \<Rightarrow> f[succ[m]] = step(m, f[m]))"

lemma primrec_nat_upto_deterministic:
  assumes n: "n \<in> Nat" and m: "m \<in> upto(n)"
      and f: "primrec_nat_upto(base, step, f, n)"
      and g: "primrec_nat_upto(base, step, g, m)"
      and k: "k \<in> upto(m)"
  shows "f[k] = g[k]"
proof -
  from m uptoNat have mNat: "m \<in> Nat" by auto
  hence "\<forall>k \<in> upto(m): f[k] = g[k]"
  proof (rule uptoInduct)
    from f g show "f[0] = g[0]" unfolding primrec_nat_upto_def by simp
  next
    fix k
    assume kNat: "k \<in> Nat" and ih: "k \<in> upto(m) \<Rightarrow> f[k] = g[k]"
       and sk: "succ[k] \<in> upto(m)"
    from sk kNat g have "g[succ[k]] = step(k, g[k])"
      unfolding primrec_nat_upto_def by auto
    moreover
    from sk m n have "succ[k] \<in> upto(n)"
      by (rule uptoTrans)
    with kNat f have "f[succ[k]] = step(k, f[k])"
      unfolding primrec_nat_upto_def by auto
    moreover
    from sk kNat mNat have "k \<in> upto(m)" 
      by (rule uptoPred)
    ultimately show "f[succ[k]] = g[succ[k]]"
      using ih by simp
  qed
  with k show ?thesis by blast
qed

lemma primrec_nat_upto_exists:
  "\<forall>n \<in> Nat : \<exists>f : primrec_nat_upto(base, step, f, n)"
proof (rule natInduct)
  have "primrec_nat_upto(base, step, [n \<in> Nat \<mapsto> base], 0)"
    unfolding primrec_nat_upto_def by (auto simp: uptoZero)
  thus "\<exists>f : primrec_nat_upto(base, step, f, 0)" ..
next
  fix n
  assume n: "n \<in> Nat"
     and ih: "\<exists>f : primrec_nat_upto(base, step, f, n)"
  from n have ssn: "succ[succ[n]] \<noteq> n"
    by induct (simp+)
  from ih obtain f where f: "primrec_nat_upto(base, step, f, n)" ..
  define g where "g \<equiv> [f EXCEPT ![succ[n]] = step(n, f[n])]"
  from f n have "isAFcn(g) \<and> DOMAIN g = Nat \<and> g[0] = base"
    by (simp add: primrec_nat_upto_def g_def)
  moreover
  {
    fix m
    assume 1: "m \<in> Nat" and 2: "succ[m] \<in> upto(n)"
    have "m \<noteq> succ[n]"
    proof
      assume 3: "m = succ[n]"
      from n have "n \<in> upto(succ[succ[n]])"
        by (simp add: uptoSucc uptoRefl)
      with 2 3 have "succ[succ[n]] = n"
        by (auto dest: uptoAntisym)
      with ssn show "FALSE" ..
    qed
    with f n 1 2 have "g[succ[m]] = step(m, g[m])"
      by (auto simp: primrec_nat_upto_def g_def)
  }
  moreover
  from f n have "g[succ[n]] = step(n, g[n])"
    by (simp add: primrec_nat_upto_def g_def)
  ultimately have "primrec_nat_upto(base, step, g, succ[n])"
    using n by (auto simp: primrec_nat_upto_def uptoSucc)
  thus "\<exists>f : primrec_nat_upto(base, step, f, succ[n])" ..
qed

lemma primrec_nat: 
  "\<exists>f : isAFcn(f) \<and> DOMAIN f = Nat
      \<and> f[0] = base \<and> (\<forall>n \<in> Nat : f[succ[n]] = step(n,f[n]))"
proof -
  from primrec_nat_upto_exists[THEN fcnConstruct] obtain F where
   F: "isAFcn(F) \<and> DOMAIN F = Nat 
       \<and> (\<forall>n\<in>Nat : primrec_nat_upto(base, step, F[n], n))"
    by blast
  define g where "g \<equiv> [n \<in> Nat \<mapsto> F[n][n]]"
  have "isAFcn(g)" "DOMAIN g = Nat"
    unfolding g_def by (simp+)
  moreover
  from F have "g[0] = base" 
    by (auto simp: primrec_nat_upto_def g_def)
  moreover
  have "\<forall>n \<in> Nat : g[succ[n]] = step(n, g[n])"
  proof
    fix n
    assume n: "n \<in> Nat"
    hence 1: "n \<in> upto(n)" "n \<in> upto(succ[n])" "succ[n] \<in> upto(succ[n])"
      by (simp add: uptoSucc uptoRefl)+
    moreover
    from F n have 2: "primrec_nat_upto(base, step, F[n], n)"
              and 3: "primrec_nat_upto(base, step, F[succ[n]], succ[n])"
      by auto
    ultimately have 4: "F[succ[n]][n] = F[n][n]"
      using n by (auto intro: primrec_nat_upto_deterministic[where n="succ[n]"])
    with n 1 3 show "g[succ[n]] = step(n, g[n])"
      by (auto simp: g_def primrec_nat_upto_def)
  qed
  ultimately
  show ?thesis by blast
qed

lemma bprimrec_nat:
  assumes base: "base \<in> S" and step: "\<forall>n \<in> Nat : \<forall>x \<in> S : step(n,x) \<in> S"
  shows "\<exists>f \<in> [Nat \<rightarrow> S] : f[0] = base \<and> (\<forall>n \<in> Nat: f[succ[n]] = step(n,f[n]))"
proof -
  from primrec_nat[of base step] obtain f where
    1: "isAFcn(f)" and 2: "DOMAIN f = Nat"
    and 3: "f[0] = base" and 4: "\<forall>n\<in>Nat : f[succ[n]] = step(n,f[n])"
    by blast
  have "\<forall>n\<in>Nat : f[n] \<in> S"
  proof (rule natInduct)
    from 3 base show "f[0] \<in> S" by simp
  next
    fix n
    assume "n \<in> Nat" and "f[n] \<in> S"
    with step 4 show "f[succ[n]] \<in> S" by force
  qed
  with 1 2 3 4 show ?thesis
    by blast
qed

definition nat_primrec where
  "nat_primrec(S, base, step) \<equiv>
   CHOOSE f \<in> [Nat \<rightarrow> S] : f[0] = base
                         \<and> (\<forall>n \<in> Nat : f[succ[n]] = step(n, f[n]))"

lemma nat_primrecE:
  assumes f: "f = nat_primrec(S, base, step)" (is "f = ?g")
  and base: "base \<in> S"
  and step: "\<forall>n \<in> Nat : \<forall>x \<in> S : step(n,x) \<in> S"
  and maj: "\<lbrakk> f \<in> [Nat \<rightarrow> S]; f[0] = base; \<forall>n \<in> Nat : f[succ[n]] = step(n, f[n]) \<rbrakk> \<Longrightarrow> P"
  shows "P"
proof -
  from base step have "\<exists> g \<in> [Nat \<rightarrow> S] : g[0] = base \<and> (\<forall>n \<in> Nat: g[succ[n]] = step(n,g[n]))"
    by (rule bprimrec_nat)
  hence "?g \<in> [Nat \<rightarrow> S] \<and> ?g[0] = base \<and> (\<forall>n \<in> Nat: ?g[succ[n]] = step(n,?g[n]))"
    unfolding nat_primrec_def by (rule bChooseI2, auto)
  with f maj show ?thesis by blast
qed

lemma nat_primrecType:
  assumes "base \<in> S" and "\<forall>n \<in> Nat : \<forall>x \<in> S : step(n,x) \<in> S"
  shows "nat_primrec(S, base, step) \<in> [Nat \<rightarrow> S]"
proof -
  define f where "f \<equiv> nat_primrec(S, base, step)"
  from f_def[THEN meta_to_obj_eq] assms show ?thesis
    by (rule nat_primrecE) (simp add: f_def)
qed


subsection \<open> Primitive recursive functions over the integers \<close>

text \<open>
  We introduce a similar construction for functions defined
  over the integers. We have two step functions for positive and
  negative integers and allow both of them to refer to the value
  of the function at the predecessor and its conjugate.
\<close>

definition primrec_int_upto where
  "primrec_int_upto(base, pstep, nstep, f, n) \<equiv>
     isAFcn(f) \<and> DOMAIN f = Int
   \<and> f[0] = base
   \<and> (\<forall>m \<in> Nat : succ[m] \<in> upto(n) \<Rightarrow> 
         f[succ[m]] = pstep(m, f[m], f[-m])
       \<and> f[-succ[m]] = nstep(m, f[m], f[-m]))"

lemma primrec_int_upto_deterministic:
  assumes n: "n \<in> Nat" and m: "m \<in> upto(n)"
      and f: "primrec_int_upto(base, pstep, nstep, f, n)"
      and g: "primrec_int_upto(base, pstep, nstep, g, m)"
      and k: "k \<in> upto(m)"
  shows "f[k] = g[k]" "f[-k] = g[-k]"
proof -
  from m uptoNat have mNat: "m \<in> Nat" by auto
  hence "\<forall>k \<in> upto(m): f[k] = g[k] \<and> f[-k] = g[-k]"
  proof (rule uptoInduct)
    from f g show "f[0] = g[0] \<and> f[-0] = g[-0]" 
      unfolding primrec_int_upto_def by simp
  next
    fix k
    assume kNat: "k \<in> Nat"
       and ih: "k \<in> upto(m) \<Rightarrow> f[k] = g[k] \<and> f[-k] = g[-k]"
       and sk: "succ[k] \<in> upto(m)"
    from sk kNat g 
    have "g[succ[k]] = pstep(k, g[k], g[-k])
        \<and> g[-succ[k]] = nstep(k, g[k], g[-k])"
      unfolding primrec_int_upto_def by auto
    moreover
    from sk m n have "succ[k] \<in> upto(n)"
      by (rule uptoTrans)
    with kNat f
    have "f[succ[k]] = pstep(k, f[k], f[-k])
        \<and> f[-succ[k]] = nstep(k, f[k], f[-k])"
      unfolding primrec_int_upto_def by auto
    moreover
    from sk kNat mNat have "k \<in> upto(m)" 
      by (rule uptoPred)
    ultimately 
    show "f[succ[k]] = g[succ[k]] \<and> f[-succ[k]] = g[-succ[k]]"
      using ih by simp
  qed
  with k show "f[k] = g[k]" "f[-k] = g[-k]" by (blast+)
qed

lemma primrec_int_upto_exists:
  "\<forall>n \<in> Nat : \<exists>f : primrec_int_upto(base, pstep, nstep, f, n)"
proof (rule natInduct)
  have "primrec_int_upto(base, pstep, nstep, [n \<in> Int \<mapsto> base], 0)"
    unfolding primrec_int_upto_def by (auto simp: uptoZero)
  thus "\<exists>f : primrec_int_upto(base, pstep, nstep, f, 0)" ..
next
  fix n
  assume n: "n \<in> Nat"
     and ih: "\<exists>f : primrec_int_upto(base, pstep, nstep, f, n)"
  from n have ssn: "succ[succ[n]] \<noteq> n"
    by induct (simp+)
  from ih obtain f where f: "primrec_int_upto(base, pstep, nstep, f, n)" ..
  define g where "g \<equiv> [m \<in> Int \<mapsto> 
                       IF m = succ[n] THEN pstep(n, f[n], f[-n])
                       ELSE IF m = -succ[n] THEN nstep(n, f[n], f[-n])
                       ELSE f[m]]"
  have "isAFcn(g) \<and> DOMAIN g = Int"
    by (simp add: g_def)
  moreover
  from f n have "g[0] = base"
    by (simp add: primrec_int_upto_def g_def)
  moreover
  {
    fix m
    assume 1: "m \<in> Nat" and 2: "succ[m] \<in> upto(n)"
    have m1: "m \<noteq> succ[n]"
    proof
      assume 3: "m = succ[n]"
      from n have "n \<in> upto(succ[succ[n]])"
        by (simp add: uptoSucc uptoRefl)
      with 2 3 have "succ[succ[n]] = n"
        by (auto dest: uptoAntisym)
      with ssn show "FALSE" ..
    qed
    from 1 n have m2: "m \<noteq> -succ[n]" by auto
    from m1 m2 f n 1 2 
    have "g[succ[m]] = pstep(m, g[m], g[-m])
        \<and> g[-succ[m]] = nstep(m, g[m], g[-m])"
      by (auto simp: primrec_int_upto_def g_def)
  }
  moreover
  from f n have "g[succ[n]] = pstep(n, g[n], g[-n])"
    by (simp add: g_def)
  moreover
  from f n have "g[-succ[n]] = nstep(n, g[n], g[-n])"
    by (simp add: g_def)
  ultimately have "primrec_int_upto(base, pstep, nstep, g, succ[n])"
    using n by (auto simp: primrec_int_upto_def uptoSucc)
  thus "\<exists>f : primrec_int_upto(base, pstep, nstep, f, succ[n])" ..
qed

lemma primrec_int: 
  "\<exists>f : isAFcn(f) \<and> DOMAIN f = Int
      \<and> f[0] = base 
      \<and> (\<forall>n \<in> Nat : f[succ[n]] = pstep(n, f[n], f[-n]))
      \<and> (\<forall>n \<in> Nat : f[-succ[n]] = nstep(n, f[n], f[-n]))"
proof -
  from primrec_int_upto_exists[THEN fcnConstruct] obtain F where
   F: "isAFcn(F) \<and> DOMAIN F = Nat 
       \<and> (\<forall>n\<in>Nat : primrec_int_upto(base, pstep, nstep, F[n], n))"
    by blast
  define g where "g \<equiv> [i \<in> Int \<mapsto> IF i \<in> Nat THEN F[i][i] ELSE F[-i][i]]"
  have "isAFcn(g)" "DOMAIN g = Int"
    unfolding g_def by (simp+)
  moreover
  from F have "g[0] = base" 
    by (auto simp: primrec_int_upto_def g_def)
  moreover
  have "\<forall>n \<in> Nat : g[succ[n]] = pstep(n, g[n], g[-n])
                 \<and> g[-succ[n]] = nstep(n, g[n], g[-n])"
    (is "\<forall>n \<in> Nat : ?P(n)")
  proof
    fix n
    assume n: "n \<in> Nat"
    hence 1: "n \<in> upto(n)" "n \<in> upto(succ[n])" "succ[n] \<in> upto(succ[n])"
      by (simp add: uptoSucc uptoRefl)+
    moreover
    from F n have 2: "primrec_int_upto(base, pstep, nstep, F[n], n)"
              and 3: "primrec_int_upto(base, pstep, nstep, F[succ[n]], succ[n])"
      by auto
    with 1 have 4: "F[succ[n]][n] = F[n][n]" "F[succ[n]][-n] = F[n][-n]"
      using n by (auto intro: primrec_int_upto_deterministic[where n = "succ[n]"])
    moreover
    from n have "g[-n] = F[n][-n]"
      by (auto simp add: g_def)
    ultimately show "?P(n)"
      using 3 n by (auto simp: g_def primrec_int_upto_def)
  qed
  ultimately
  show ?thesis by blast
qed

lemma bprimrec_int:
  assumes base: "base \<in> S" 
      and pstep: "\<forall>n \<in> Nat : \<forall>x,y \<in> S : pstep(n,x,y) \<in> S"
      and nstep: "\<forall>n \<in> Nat : \<forall>x,y \<in> S : nstep(n,x,y) \<in> S"
    shows "\<exists>f \<in> [Int \<rightarrow> S] : 
              f[0] = base 
            \<and> (\<forall>n \<in> Nat: f[succ[n]] = pstep(n, f[n], f[-n]))
            \<and> (\<forall>n \<in> Nat: f[-succ[n]] = nstep(n, f[n], f[-n]))"
proof -
  from primrec_int[of base pstep nstep] obtain f where
    1: "isAFcn(f)" and 2: "DOMAIN f = Int"
    and 3: "f[0] = base" 
    and 4: "\<forall>n\<in>Nat : f[succ[n]] = pstep(n, f[n], f[-n])"
    and 5: "\<forall>n\<in>Nat : f[-succ[n]] = nstep(n, f[n], f[-n])"
    by blast
  from 3 4 5 base pstep nstep have "\<forall>n\<in>Int : f[n] \<in> S"
    by (intro intInduct) force+
  with 1 2 3 4 5 show ?thesis
    by blast
qed

definition int_primrec where
  "int_primrec(S, base, pstep, nstep) \<equiv>
   CHOOSE f \<in> [Int \<rightarrow> S] : f[0] = base
                         \<and> (\<forall>n \<in> Nat : f[succ[n]] = pstep(n, f[n], f[-n]))
                         \<and> (\<forall>n \<in> Nat : f[-succ[n]] = nstep(n, f[n], f[-n]))"

lemma int_primrecE:
  assumes f: "f = int_primrec(S, base, pstep, nstep)" (is "f = ?g")
  and base: "base \<in> S" 
  and pstep: "\<forall>n \<in> Nat : \<forall>x,y \<in> S : pstep(n,x,y) \<in> S"
  and nstep: "\<forall>n \<in> Nat : \<forall>x,y \<in> S : nstep(n,x,y) \<in> S"
  and maj: "\<lbrakk> f \<in> [Int \<rightarrow> S]; f[0] = base; 
              \<forall>n \<in> Nat : f[succ[n]] = pstep(n, f[n], f[-n]);
              \<forall>n \<in> Nat : f[-succ[n]] = nstep(n, f[n], f[-n]) \<rbrakk> \<Longrightarrow> P"
  shows "P"
proof -
  from base pstep nstep 
  have "\<exists>g \<in> [Int \<rightarrow> S] : g[0] = base 
                         \<and> (\<forall>n \<in> Nat: g[succ[n]] = pstep(n, g[n], g[-n]))
                         \<and> (\<forall>n \<in> Nat: g[-succ[n]] = nstep(n, g[n], g[-n]))"
    by (rule bprimrec_int)
  hence "?g \<in> [Int \<rightarrow> S] \<and> ?g[0] = base 
       \<and> (\<forall>n \<in> Nat: ?g[succ[n]] = pstep(n, ?g[n], ?g[-n]))
       \<and> (\<forall>n \<in> Nat: ?g[-succ[n]] = nstep(n, ?g[n], ?g[-n]))"
    unfolding int_primrec_def by (rule bChooseI2) auto
  with f maj show ?thesis by blast
qed

lemma int_primrecType:
  assumes "base \<in> S" 
  and "\<forall>n \<in> Nat : \<forall>x,y \<in> S : pstep(n,x,y) \<in> S"
  and "\<forall>n \<in> Nat : \<forall>x,y \<in> S : nstep(n,x,y) \<in> S"
  shows "int_primrec(S, base, pstep, nstep) \<in> [Int \<rightarrow> S]"
proof -
  define f where "f \<equiv> int_primrec(S, base, pstep, nstep)"
  from f_def[THEN meta_to_obj_eq] assms show ?thesis
    by (rule int_primrecE) (simp add: f_def)
qed

end
