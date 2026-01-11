section \<open>Axioms used by the new SMT backend\<close>

theory NewSMT
  imports Constant
begin

subsection \<open>Set Theory\<close>

lemma ChooseDef: "P(x) \<Longrightarrow> P(Choice(P))"
  by (rule chooseI)

lemma SetExtensionality: "(\<forall>z : z \<in> a \<Leftrightarrow> z \<in> b) \<Rightarrow> a = b"
  by (simp add: extension)

lemma SubseteqIntro: "(\<forall>z : z \<in> a \<Rightarrow> z \<in> b) \<Rightarrow> a \<subseteq> b"
  by blast

lemma SubseteqElim: "a \<subseteq> b \<and> x \<in> a \<Rightarrow> x \<in> b"
  by blast

text \<open>
  The two following axioms are stated for $n$-ary enumerations,
  we prove their instances for $n=2$.
\<close>
lemma EnumIntro: "a \<in> {a,b} \<and> b \<in> {a,b}"
  by blast

lemma EnumElim: "x \<in> {a,b} \<Rightarrow> x=a \<or> x=b"
  by blast

lemma SubsetDef: "x \<in> SUBSET a \<Leftrightarrow> x \<subseteq> a"
  by blast

lemma UnionIntro: "x \<in> y \<and> y \<in> a \<Rightarrow> x \<in> UNION a"
  by blast

lemma UnionElim: "x \<in> UNION a \<Rightarrow> (\<exists>y : x \<in> y \<and> y \<in> a)"
  by blast

lemma SetstDef: "x \<in> subsetOf(a,P) \<Leftrightarrow> x \<in> a \<and> P(x)"
  by (rule subsetOf)

text \<open>
  The two following axioms are stated for an $n$-ary
  operator $f$ but Isabelle only provides the construct
  for unary operators.
\<close>
lemma SetofIntro: "y \<in> a \<Rightarrow> f(y) \<in> setOfAll(a,f)"
  by blast

lemma SetofElim: "x \<in> setOfAll(a,f) \<Rightarrow> (\<exists>y : y \<in> a \<and> x = f(y))"
  by blast

lemma CupDef: "x \<in> a \<union> b \<Leftrightarrow> x \<in> a \<or> x \<in> b"
  by blast

lemma CapDef: "x \<in> a \<inter> b \<Leftrightarrow> x \<in> a \<and> x \<in> b"
  by blast

lemma SetminusDef: "x \<in> a \<setminus> b \<Leftrightarrow> x \<in> a \<and> x \<notin> b"
  by blast


subsection \<open>Functions\<close>

lemma FcnExtensionality:
  assumes "isAFcn(f)" "isAFcn(g)" "DOMAIN f = DOMAIN g"
          "\<forall>x \<in> DOMAIN f : f[x] = g[x]"
        shows   "f = g"
  using assms by auto

lemma FcnIsafcn: "isAFcn(Fcn(a,F))"
  by (rule fcnIsAFcn)

lemma FcnDom: "DOMAIN Fcn(a,F) = a"
  by (rule DOMAIN)

lemma FcnApp: "x \<in> a \<Rightarrow> Fcn(a,F)[x] = F(x)"
  by auto

lemma ArrowIntro:
  assumes "isAFcn(f)" "DOMAIN f = a" "\<forall>x \<in> a : f[x] \<in> b"
  shows   "f \<in> [a \<rightarrow> b]"
  using assms by (rule inFuncSet)

lemma ArrowElim1: "f \<in> [a \<rightarrow> b] \<Rightarrow> isAFcn(f) \<and> DOMAIN f = a"
  by blast

lemma ArrowElim2: "f \<in> [a \<rightarrow> b] \<and> x \<in> a \<Rightarrow> f[x] \<in> b"
  by blast

lemma ExceptIsafcn: "isAFcn(except(f,x,y))"
  by blast

lemma ExceptDom: "DOMAIN except(f,x,y) = DOMAIN f"
  by (rule domainExcept)

lemma ExceptApp1: "x \<in> DOMAIN f \<Rightarrow> except(f,x,y)[x] = y"
  by auto

lemma ExceptApp2: "z \<in> DOMAIN f \<and> z \<noteq> x \<Rightarrow> except(f,x,y)[z] = f[z]"
  by auto


subsection \<open>Integers\<close>

lemma PlusTyping: "x \<in> Int \<and> y \<in> Int \<Rightarrow> x+y \<in> Int"
  by simp

lemma UminusTyping: "x \<in> Int \<Rightarrow> -x \<in> Int"
  by simp

lemma MinusTyping: "x \<in> Int \<and> y \<in> Int \<Rightarrow> x-y \<in> Int"
  by simp

lemma TimesTyping: "x \<in> Int \<and> y \<in> Int \<Rightarrow> x*y \<in> Int"
  by simp

lemma DivTyping: "x \<in> Int \<and> y \<in> Int \<and> y > 0 \<Rightarrow> x div y \<in> Int"
  by simp

lemma NatDef: "x \<in> Nat \<Leftrightarrow> x \<in> Int \<and> 0 \<le> x"
  by simp

lemma RangeDef: "x \<in> a .. b \<Leftrightarrow> x \<in> Int \<and> a \<le> x \<and> x \<le> b"
  by simp


subsection \<open>Booleans\<close>

text \<open>
  The following lemmas do not exactly correspond to the SMT
  axioms because Isabelle/TLA+ is untyped and does not have
  cast operators.
\<close>

lemma BooleanIntro: "TRUE \<in> BOOLEAN \<and> FALSE \<in> BOOLEAN"
  by blast

lemma BooleanElim: "x \<in> BOOLEAN \<Rightarrow> x = TRUE \<or> x = FALSE"
  by blast


subsection \<open>Tuples and Records\<close>

text \<open>
  The following SMT axioms are for tuples or records
  of arbitrary length, we prove instances for pairs.
\<close>

lemma TupIsafcn: "isAFcn(\<langle>x,y\<rangle>)"
  by blast

lemma TupDom: "DOMAIN \<langle>x,y\<rangle> = {1,2}"
  by (auto simp: two_def)

lemma TupApp: "\<langle>x,y\<rangle>[1] = x \<and> \<langle>x,y\<rangle>[2] = y"
  by (auto simp: two_def)

lemma ProductIntro: "x \<in> a \<and> y \<in> b \<Rightarrow> \<langle>x,y\<rangle> \<in> a \<times> b"
  by auto

lemma ProductElim: "x \<in> a \<times> b \<Longrightarrow> x = \<langle>x[1], x[2]\<rangle>"
  by (rule prodProj)

lemma RecordIsafcn: "isAFcn(''foo'' :> x @@ ''bar'' :> y)"
  by auto

lemma RecordDom: "DOMAIN (''foo'' :> x @@ ''bar'' :> y) = {''foo'', ''bar''}"
  by auto

lemma RecordApp: 
  "(''foo'' :> x @@ ''bar'' :> y)[''foo''] = x"
  "(''foo'' :> x @@ ''bar'' :> y)[''bar''] = y"
  by auto

lemma RectIntro:
  assumes "x \<in> a" "y \<in> b"
  shows   "(''foo'' :> x @@ ''bar'' :> y) \<in> [''foo'' : a, ''bar'' : b]"
  using assms by auto

lemma RectElim:
  assumes "x \<in> [''foo'' : a, ''bar'' : b]"
  shows   "x = (''foo'' :> x[''foo''] @@ ''bar'' :> x[''bar''])"
  using assms by force


subsection \<open>Sequences\<close>

text \<open>
  Somewhat rewritten, in particular the original hypothesis
  @{text "\<forall>i: i \<in> DOMAIN s \<Leftrightarrow> 1 \<le> i \<and> i \<le> Len(s)"}
  doesn't imply that @{text "DOMAIN s \<subseteq> Nat"}.
  Could instead assume
  @{text "DOMAIN s = 1 .. Len(s)"} and
  @{text "\<forall>i \<in> DOMAIN s : s[i] \<in> a"}.
\<close>
lemma SeqIntro:
  assumes "isAFcn(s)" "Len(s) \<in> Nat"
     "\<forall>i : i \<in> DOMAIN s \<Leftrightarrow> i \<in> Nat \<and> 1 \<le> i \<and> i \<le> Len(s)"
     "\<forall>i \<in> Nat : 1 \<le> i \<and> i \<le> Len(s) \<Rightarrow> s[i] \<in> a"
   shows  "s \<in> Seq(a)"
proof
  from assms show "isASeq(s)" by auto
next
  fix k
  assume "k \<in> 1 .. Len(s)"
  hence k: "k \<in> Int" "1 \<le> k" "k \<le> Len(s)" by auto
  with \<open>Len(s) \<in> Nat\<close> have "k \<in> Nat" by auto
  with \<open>\<forall>i \<in> Nat : 1 \<le> i \<and> i \<le> Len(s) \<Rightarrow> s[i] \<in> a\<close> k
  show "s[k] \<in> a" by blast
qed

lemma SeqElim1:
  "s \<in> Seq(a) \<Rightarrow> isAFcn(s) \<and> Len(s) \<in> Nat \<and> DOMAIN s = 1 .. Len(s)"
  by auto

text \<open>
  Similarly rewritten as theorem @{text SeqIntro} above.
\<close>
lemma SeqElim2:
  "s \<in> Seq(a) \<and> i \<in> Nat \<and> 1 \<le> i \<and> i \<le> Len(s) \<Rightarrow> s[i] \<in> a"
  by auto

lemma LenDef:
  "x \<in> Nat \<and> DOMAIN s = 1 .. x \<Rightarrow> Len(s) = x"
  by auto

text \<open>
  Isabelle/TLA+ currently doesn't know about concatenation of sequences,
  so we cannot prove lemmas corresponding to the SMT axioms about concatenation.
\<close>

lemma AppendTyping: "s \<in> Seq(a) \<and> x \<in> a \<Rightarrow> Append(s,x) \<in> Seq(a)"
  by auto

lemma AppendLen: 
  assumes "Len(s) \<in> Nat"
  shows   "Len(Append(s,x)) = Len(s)+1"
proof
  from assms show "DOMAIN Append(s,x) = 1 .. (Len(s)+1)" by auto
next
  from assms show "Len(s)+1 \<in> Nat" by auto
qed

text \<open>
  Some changes w.r.t. the original formulations of the axioms about @{text Append}.
\<close>
lemma AppendApp1:
  assumes "Len(s) \<in> Nat" (* missing from original formulation *)
          "i \<in> Int"
          "1 \<le> i" "i \<le> Len(s)"
  shows   "Append(s,x)[i] = s[i]"
  using assms unfolding Append_def by auto

lemma AppendApp2:
  assumes "Len(s) \<in> Nat"
  shows "Append(s,x)[Len(s)+1] = x"
proof -
  from assms have "Len(s)+1 = succ[Len(s)]"
    by simp
  moreover
  from assms have "Len(s)+1 \<in> DOMAIN Append(s,x)"
    by (auto simp: Append_def)
  ultimately
  show ?thesis
    using assms by (auto simp: Append_def)
qed

text \<open>
  Isabelle/TLA+ doesn't know about the remaining operations on sequences.
\<close>

lemma TupSeqTyping: "x \<in> a \<and> y \<in> a \<Rightarrow> \<langle>x,y\<rangle> \<in> Seq(a)"
  by auto

lemma TupSeqLen: "Len(\<langle>x,y\<rangle>) = 2"
  by (auto simp: two_def)


end
