(* This material is now obsolete but included because it may still become relevant. *)

header {* Normalization rules used in the SMT backend  *}

theory SMT
imports NatDivision CaseExpressions Strings Integers
begin

text {* We can declare the rewriting rules used for normalization
   with the attribute "norm". *}

ML {*
structure NormalizeRules = Named_Thms
  (val name = "norm"
   val description = "Theorems for normalization")
*}

setup {* NormalizeRules.setup *}

text {* Trivial rules *}

theorem [norm]: "isBool(e) \<Longrightarrow> e = TRUE \<equiv> e" by (simp add:isBool_def)
theorem [norm]: "isBool(e) \<Longrightarrow> e = FALSE \<equiv> ~e" by (simp add:isBool_def)
theorem [norm]: "isBool(e) \<Longrightarrow> e \<in> BOOLEAN" by (auto simp add:isBool_def)

theorem [norm]: "isBool(e) \<Longrightarrow> e \<and> TRUE \<equiv> e" by (simp add:isBool_def)
theorem [norm]: "isBool(e) \<Longrightarrow> e \<or> FALSE \<equiv> e" by (simp add:isBool_def)
theorem [norm]: "isBool(e) \<Longrightarrow> TRUE \<Rightarrow> e \<equiv> e" by (simp add:isBool_def)
theorem [norm]: "isBool(e) \<Longrightarrow> e \<Rightarrow> TRUE \<equiv> TRUE" by (simp add:isBool_def)
theorem [norm]: "isBool(e) \<Longrightarrow> FALSE \<Rightarrow> e \<equiv> TRUE" by (simp add:isBool_def)
theorem [norm]: "isBool(e) \<Longrightarrow> (\<not>\<not>e) \<equiv> e" by (simp add:isBool_def)

theorem [norm]: "\<forall> x : TRUE \<equiv> TRUE" by simp
theorem [norm]: "\<forall> x : FALSE \<equiv> FALSE" by simp
theorem [norm]: "\<exists> x : TRUE \<equiv> TRUE" by simp
theorem [norm]: "\<exists> x : FALSE \<equiv> FALSE" by simp
theorem [norm]: "\<forall> x \<in> S : TRUE \<equiv> TRUE" by simp
theorem [norm]: "\<exists> x \<in> S : FALSE \<equiv> FALSE" by simp

theorem [norm]: "S \<union> {} = S" by simp
theorem [norm]: "{} \<union> S = S" by simp
theorem [norm]: "S \\ {} = S" by auto
theorem [norm]: "{} \\ S = {}" by simp

theorem [norm]: "{a1,a2} \<union> {b1,b2} = {a1,a2,b1,b2}" by simp
theorem [norm]: "{a,b} \<subseteq> S \<equiv> a \<in> S \<and> b \<in> S" by simp

theorem [norm]: "(\<And>x. isBool(P(x))) \<Longrightarrow> (\<forall>x \<in> {a,b} : P(x)) \<equiv> P(a) \<and> P(b)"
  by (simp add:isBool_def)
theorem [norm]: "(\<And>x. isBool(P(x))) \<Longrightarrow> (\<exists>x \<in> {a,b} : P(x)) \<equiv> P(a) \<or> P(b)"
  by (simp add:isBool_def)

theorem [norm]: "\<lbrakk>\<And>x. isBool(P(x)) ; \<forall>x \<in> S \\ T : P(x)\<rbrakk> \<Longrightarrow> \<forall>x \<in> S : x \<notin> T \<Rightarrow> P(x)"
  by (simp add: bAll_def)
theorem [norm]: "(\<And>x. isBool(P(x))) \<Longrightarrow> (\<forall>x \<in> {a,b} \\ S : P(x)) \<Longrightarrow> \<forall>x \<in> {a,b} : x \<notin> S \<Rightarrow> P(x)"
  by (auto simp only: bAll_def)

text {* Sets *}

theorem [norm]: "S \<in> SUBSET T \<equiv> S \<subseteq> T" by simp
theorem [norm]: "x \<in> S \<union> T \<equiv> x \<in> S \<or> x \<in> T" by simp
theorem [norm]: "x \<in> S \<inter> T \<equiv> x \<in> S \<and> x \<in> T" by simp
theorem [norm]: "x \<in> S \\ T \<equiv> x \<in> S \<and> x \<notin> T" by simp
theorem [norm]: "x \<in> {} \<equiv> FALSE" by simp
theorem [norm]: "x \<in> {y} \<equiv> x = y" by simp
theorem [norm]: "x \<in> {y,z} \<equiv> x = y \<or> x = z" by simp
theorem [norm]: "x \<in> UNION {e1,e2} \<equiv> x \<in> e1 \<or> x \<in> e2" by simp
theorem [norm]: "x \<in> UNION {e(y) : y \<in> S} \<equiv> \<exists> y \<in> S : x \<in> e(y)" by simp
theorem [norm]: "x \<in> UNION {y \<in> S : P(y)} \<equiv> \<exists> T \<in> S : P(T) \<and> x \<in> T" by simp
theorem [norm]: "x \<in> UNION S \<equiv> \<exists> T \<in> S : x \<in> T" by simp
theorem [norm]: "x \<in> {e(y) : y \<in> S} \<equiv> \<exists> y \<in> S : x = e(y)" by simp
theorem [norm]: "x \<in> {y \<in> S : P(y)} \<equiv> x \<in> S \<and> P(x)" by simp

theorem [norm]: "S \<subseteq> T \<Longrightarrow> \<forall> x \<in> S : x \<in> T" by auto
theorem [norm]: "S = {} = (\<forall>x \<in> S : FALSE)" by auto

text {* Of the following two rules, the first is applied when S \<noteq> {}
  is a hypothesis ; the second, when it is a conclusion. *}
theorem [norm]: "S \<noteq> {} \<equiv> (\<exists> x \<in> S : TRUE)" by simp
theorem [norm]: "S \<noteq> {} \<equiv> (S = {} \<Rightarrow> FALSE)" by simp

text {* For the moment, the interval of numbers ".." is defined only for naturals. *}
theorem [norm]: "x \<in> a..b \<equiv> x \<in> Nat \<and> a \<le> x \<and> x \<le> b" by (simp add: natInterval_def)

text {* \<lbrakk>b \<in> Nat; a \<in> Nat; c \<in> Nat\<rbrakk> \<Longrightarrow> a .. b = a .. c = (b < a \<and> c < a \<or> b = c) *}
theorems
  natIntervalEqual_iff [of a b a c, simplified, standard, norm]
  natIntervalEqual_iff [of a b c b, simplified, standard, norm]

text {* Functions *}

theorem [norm]: "isAFcn([x \<in> S \<mapsto> e])" by simp
theorem [norm]: "isAFcn([f EXCEPT ![a] = b])" by simp

theorem [norm]: "f = [x \<in> S \<mapsto> e(x)] \<Leftrightarrow> isAFcn(f) \<and> DOMAIN f = S \<and> (\<forall> x \<in> S : f[x] = e(x))" by auto
theorem [norm]: "f \<in> [S \<rightarrow> T] \<Leftrightarrow> isAFcn(f) \<and> DOMAIN f = S \<and> (\<forall> x \<in> S : f[x] \<in> T)" by auto
theorem [norm]: "a \<in> S \<Longrightarrow> [x \<in> S \<mapsto> e(x)][a] = e(a)" by simp
theorem [norm]:
  assumes "a \<in> DOMAIN f"
      and "g = [f EXCEPT ![a] = b]"
  shows "isAFcn(g)"
    and "DOMAIN g = DOMAIN f"
    and "g[a] = b \<and> (\<forall> x \<in> DOMAIN f \\ {a} : g[x] = f[x])"
  using assms by auto

theorem [norm]:
  "a \<in> DOMAIN f \<Longrightarrow> [f EXCEPT ![x] = y][a] = (IF x = a THEN y ELSE f[a])"
  by (auto simp: except_def)
theorem [norm]:
  "DOMAIN [x \<in> S \<mapsto> e(x)] = S" by simp
theorem [norm]:
  "DOMAIN [f EXCEPT ![a] = b] = DOMAIN f" by simp
theorem [norm]:
  assumes "a \<in> DOMAIN f"
      and "b \<in> T"
      and "[f EXCEPT ![a] = b] \<in> [S \<rightarrow> T]"
  shows "DOMAIN f = S" and "a \<in> S" and "b \<in> T"
    and "\<forall> x \<in> S \\ {a} : f[x] \<in> T"
  using assms by (simp_all only:FuncSet except_def, auto)

theorem [norm]:
  "[x \<in> S \<mapsto> e(x)] = [x \<in> T \<mapsto> d(x)] = (S = T \<and> (\<forall>x \<in> S : e(x) = d(x)))"
  by (force simp add: fcnEqualIff)

theorem [norm]:
  "[f EXCEPT ![a] = b] = [g EXCEPT ![c] = d] =
  (DOMAIN f = DOMAIN g \<and>
  (\<forall>x \<in> DOMAIN g : (IF x = a THEN b ELSE f[x]) = (IF x = c THEN d ELSE g[x])))"
  by (force simp add: fcnEqualIff)

text {* IFs *}

theorem [norm]:
  "isBool(P) \<Longrightarrow> Q(IF P THEN t ELSE e) \<Longrightarrow> IF P THEN Q(t) ELSE Q(e)"
  by (auto simp add:isBool_def)
theorem [norm]:
  "isBool(P) \<Longrightarrow> Q(x, IF P THEN t ELSE e) \<Longrightarrow> IF P THEN Q(x,t) ELSE Q(x,e)"
  "isBool(P) \<Longrightarrow> Q(IF P THEN t ELSE e, x) \<Longrightarrow> IF P THEN Q(t,x) ELSE Q(e,x)"
  by (auto simp add:isBool_def)
(* SM: should the above rather be the following? *)
theorem [norm]:
  "isBool(P) \<Longrightarrow> Q(x, IF P THEN t ELSE e) = (IF P THEN Q(x,t) ELSE Q(x,e))"
  "isBool(P) \<Longrightarrow> Q(IF P THEN t ELSE e, x) = (IF P THEN Q(t,x) ELSE Q(e,x))"
  by (auto simp add:isBool_def)

theorem [norm]:
  "isBool(P) \<Longrightarrow> (IF P THEN t ELSE e)[x] = (IF P THEN t[x] ELSE e[x])"
  by (auto simp add:isBool_def)
theorem [norm]:
  "isBool(P) \<Longrightarrow> [(IF P THEN t ELSE e) EXCEPT ![x] = y] =
    (IF P THEN [t EXCEPT ![x] = y] ELSE [e EXCEPT ![x] = y])"
  by (auto simp add:isBool_def)
theorem [norm]:
  "x = (IF P THEN t ELSE e) \<Longrightarrow> IF P THEN x = t ELSE x = e"
  "(IF P THEN t ELSE e) = x \<Longrightarrow> IF P THEN t = x ELSE e = x"
  by auto
(* SM: should the above rather be the following? *)
theorem [norm]:
  "(x = (IF P THEN t ELSE e)) = (IF P THEN x = t ELSE x = e)"
  "((IF P THEN t ELSE e) = x) = (IF P THEN t = x ELSE e = x)"
  by auto
theorem [norm]:
  "x \<in> (IF P THEN t ELSE e) \<Longrightarrow> IF P THEN x \<in> t ELSE x \<in> e"
  "(IF P THEN t ELSE e) \<in> S \<Longrightarrow> IF P THEN t \<in> S ELSE e \<in> S"
  by auto
(* SM: similar *)
theorem [norm]:
  "x \<in> (IF P THEN t ELSE e) = (IF P THEN x \<in> t ELSE x \<in> e)"
  "(IF P THEN t ELSE e) \<in> S = (IF P THEN t \<in> S ELSE e \<in> S)"
  by auto
theorem [norm]:
  "isBool(P) \<Longrightarrow> x \<le> (IF P THEN t ELSE e) \<Longrightarrow> IF P THEN x \<le> t ELSE x \<le> e"
  "isBool(P) \<Longrightarrow> (IF P THEN t ELSE e) \<le> x \<Longrightarrow> IF P THEN t \<le> x ELSE e \<le> x"
  by (auto simp add:isBool_def)
(* SM: similar *)
theorem [norm]:
  "isBool(P) \<Longrightarrow> x \<le> (IF P THEN t ELSE e) = (IF P THEN x \<le> t ELSE x \<le> e)"
  "isBool(P) \<Longrightarrow> (IF P THEN t ELSE e) \<le> x = (IF P THEN t \<le> x ELSE e \<le> x)"
  by (auto simp add:isBool_def)
theorem [norm]:
  "\<lbrakk>isBool(P); P = Q\<rbrakk> \<Longrightarrow> (IF P THEN t ELSE e) \<le> (IF Q THEN u ELSE v) \<Longrightarrow> IF P THEN t \<le> u ELSE e \<le> v"
  by (auto simp add:isBool_def)
(* SM: similar *)
theorem [norm]:
  "\<lbrakk>isBool(P); P = Q\<rbrakk> \<Longrightarrow> (IF P THEN t ELSE e) \<le> (IF Q THEN u ELSE v) = (IF P THEN t \<le> u ELSE e \<le> v)"
  by (auto simp add:isBool_def)

theorem [norm]:
  "isBool(P) \<Longrightarrow> isAFcn(IF P THEN t ELSE e) \<Longrightarrow> IF P THEN isAFcn(t) ELSE isAFcn(e)"
  by (auto simp add:isBool_def)
(* SM: similar *)
theorem [norm]:
  "isBool(P) \<Longrightarrow> isAFcn(IF P THEN t ELSE e) = (IF P THEN isAFcn(t) ELSE isAFcn(e))"
  by (auto simp add:isBool_def)

text {* Tuples/Sequences *}

theorem [norm]: "isAFcn(<<>>)" by simp
theorem [norm]: "isAFcn(Append(s,e))" by (simp add: Append_def)
theorem [norm]: "isAFcn(<<e1,e2>>)" by simp

theorem [norm]: "[x \<in> S \<mapsto> e] = <<>> \<Longrightarrow> S = {}" by simp
theorem [norm]: "DOMAIN <<>> = {}" by simp

theorem [norm]: "<<e1,e2>>[1] = e1" by simp
theorem [norm]: "<<e1,e2>>[2] = e2" by simp
theorem [norm]: "t = <<e1,e2>> \<Leftrightarrow> isASeq(t) \<and> DOMAIN t = 1..2 \<and> t[1] = e1 \<and> t[2] = e2"
  by (intro iffI, simp, rule seqEqualI, simp_all, intro LenI, simp_all)
theorem [norm]: "t \<in> S \<times> T \<Leftrightarrow> isASeq(t) \<and> DOMAIN t = 1..2 \<and> t[1] \<in> S \<and> t[2] \<in> T"
  by (intro iffI, force, auto simp: prod_def Product_def)

theorem [norm]: "<<a1,a2>> = <<b1,b2>> \<Longrightarrow> a1 = b1 \<and> a2 = b2" by simp
theorem [norm]:
  assumes "[i \<in> 1..2 \<mapsto> e(i)] = <<e1,e2>>"
  shows "\<forall>i \<in> 1..2 : e(i) = <<e1,e2>>[i]"
proof -
  def tup \<equiv> "[i \<in> 1..2 \<mapsto> e(i)]"
  have "tup[1] = e(1) \<and> tup[2] = e(2)" by (auto simp: tup_def)
  moreover
  from assms have "tup[1] = e1 \<and> tup[2] = e2" by (auto simp: tup_def)
  ultimately show ?thesis by auto
qed

text {* Records *}

(* FIX: predicate isFieldOf(h,r) *)

theorem [norm]: "r = (''h1'' :> e1 @@ ''h2'' :> e2) \<Longrightarrow> r[''h1''] = e1 \<and> r[''h2''] = e2" by simp
theorem [norm]: "r \<in> [''h1'' : e1, ''h2'' : e2] \<Longrightarrow> r[''h1''] \<in> e1 \<and> r[''h2''] \<in> e2" by auto
theorem [norm]:
  assumes "h \<in> DOMAIN r" and "s = [r EXCEPT ![h] = e]"
  shows "\<forall>f \<in> DOMAIN r : IF f = h THEN s[f] = e ELSE s[f] = r[f]"
  using assms by auto

text {* Arithmetic *}

theorem "n \<in> Int \<Longrightarrow> -.-.n = n" by simp

theorem "x \<in> Int \<Longrightarrow> x + 0 = x" by simp
theorem "x \<in> Int \<Longrightarrow> 0 + x = x" by simp
theorem "x \<in> Int \<Longrightarrow> x - 0 = x" by simp
theorem "x \<in> Int \<Longrightarrow> 0 - x = -.x" by simp

theorem "x \<in> Int \<Longrightarrow> x - x = 0" by simp

theorem "x \<in> Int \<Longrightarrow> x \<ge> x" by simp
theorem "x \<in> Int \<Longrightarrow> x \<le> x" by simp

theorem "\<lbrakk>x \<in> Int; y \<in> Int; z \<in> Int\<rbrakk> \<Longrightarrow> (x + y \<le> x + z) = (y \<le> z)"
  apply (rule intCases3[of x y z],simp+) sorry
theorem "\<lbrakk>x \<in> Int; y \<in> Int; z \<in> Int\<rbrakk> \<Longrightarrow> (x + y \<le> z + x) = (y \<le> z)" sorry
theorem "\<lbrakk>x \<in> Int; y \<in> Int; z \<in> Int\<rbrakk> \<Longrightarrow> (y + x \<le> x + z) = (y \<le> z)" sorry
theorem "\<lbrakk>x \<in> Int; y \<in> Int; z \<in> Int\<rbrakk> \<Longrightarrow> (y + x \<le> z + x) = (y \<le> z)" sorry

theorem "\<lbrakk>x \<in> Int; y \<in> Int; z \<in> Int\<rbrakk> \<Longrightarrow> (x \<le> y - z) = (x + z \<le> y)"
  apply (rule intCases3[of x y z],simp+)
  apply (simp add: int_diff_def)
  thm nat_add_right_cancel_leq
  thm leq_adiff_right_add_left
  sorry
theorem "\<lbrakk>x \<in> Int; y \<in> Int; z \<in> Int\<rbrakk> \<Longrightarrow> (x \<le> y - z) = (x + z \<le> y)"
  proof -
    assume x:"x \<in> Int" and y:"y \<in> Int" and z:"z \<in> Int"
    have 1:"(x \<le> y - z) = (x + z \<le> (y - z) + z)" sorry
    have 2:"(y - z) + z = y" sorry
    from x y z 1 2 show ?thesis by simp
  qed
theorem "\<lbrakk>x \<in> Int; y \<in> Int; z \<in> Int\<rbrakk> \<Longrightarrow> (x - y \<le> z) = (x \<le> z + y)" sorry

theorem "\<lbrakk>x \<in> Int; y \<in> Int\<rbrakk> \<Longrightarrow> (x + y) - x = y" sorry
theorem "\<lbrakk>x \<in> Int; y \<in> Int\<rbrakk> \<Longrightarrow> (y + x) - x = y" sorry
theorem "\<lbrakk>x \<in> Int; y \<in> Int\<rbrakk> \<Longrightarrow> (x - y) + y = x" sorry
theorem "\<lbrakk>x \<in> Int; y \<in> Int\<rbrakk> \<Longrightarrow> x + (y - x) = y" sorry

theorem "\<lbrakk>x \<in> Int; y \<in> Int; z \<in> Int\<rbrakk> \<Longrightarrow> x + (y - z) = (x + y) - z"
  by (auto simp: int_diff_def add_assoc_int)
theorem "\<lbrakk>x \<in> Int; y \<in> Int; z \<in> Int\<rbrakk> \<Longrightarrow> (x - z) + y = (x + y) - z" sorry
theorem "\<lbrakk>x \<in> Int; y \<in> Int; z \<in> Int\<rbrakk> \<Longrightarrow> x - (y + z) = (x - y) - z" sorry
theorem "\<lbrakk>x \<in> Int; y \<in> Int; z \<in> Int\<rbrakk> \<Longrightarrow> x - (y - z) = (x + z) - y" sorry

theorem "\<lbrakk>x \<in> Int; n \<in> Nat\<rbrakk> \<Longrightarrow> x + -.n = x - n" sorry
theorem "\<lbrakk>x \<in> Int; n \<in> Nat\<rbrakk> \<Longrightarrow> -.n + x = x - n" sorry
theorem "\<lbrakk>x \<in> Int; n \<in> Nat\<rbrakk> \<Longrightarrow> x - -.n = x + n" sorry


text {* Before sequences, some lemmas about intervals *}
lemma (*[simp]:*) "n \<in> Int \<and> n \<le> 0 \<Longrightarrow> 1 .. n = {}" sorry
lemma (*[simp]:*) "n \<in> Nat \<and> 1..n = {} \<Longrightarrow> n = 0" sorry
lemma (*[simp]:*) "n \<in> Nat \<and> {} = 1..n \<Longrightarrow> n = 0" sorry
lemma OneToNegative (*[simp]*): "n \<in> Int \<and> n \<le> 0 \<Longrightarrow> 1..n = 1..0" sorry
(*
theorem range_empty [simp]: "b < a \<Longrightarrow> a..b = {}"
  sorry
SM: shouldn't this rather be the following
*)
theorem range_empty (*[simp]*): "\<lbrakk>a \<in> Int; b \<in> Int\<rbrakk> \<Longrightarrow> (a .. b = {}) = (b < a)"
  sorry

lemma (*[simp]:*) "\<lbrakk>n \<in> Int; {1} = 1..n\<rbrakk> \<Longrightarrow> n = 1" sorry
lemma (*[simp]:*) "\<lbrakk>n \<in> Int; {1,2} = 1..n\<rbrakk> \<Longrightarrow> n = 2" sorry
lemma (*[simp]:*) "\<lbrakk>n \<in> Int; {1,2,3} = 1..n\<rbrakk> \<Longrightarrow> n = 3" sorry

(* Seq(S) is defined over intervals of naturals but it should work
    as well for intervals of integers. *)
lemma SeqInt: "UNION {[1 .. n \<rightarrow> S] : n \<in> Int} = Seq(S)"
proof -
  have "(UNION {[1 .. n \<rightarrow> S] : n \<in> Int}) = (UNION {[1 .. n \<rightarrow> S] : n \<in> Nat})"
    (is "?uint = ?unat")
  proof
    fix x
    assume x: "x \<in> ?uint"
    then obtain n where n: "n \<in> Int" "x \<in> [1..n \<rightarrow> S]" by auto
    show "x \<in> ?unat"
    proof (cases "n \<in> Nat")
      case True
      with n show ?thesis by auto
    next
      case False
      with n have "n < 1" sorry (* reasoning about integers *)
      with n have "1..n = {}" by (simp add: range_empty)
      with n show ?thesis by force (* contradiction with "x \<in> [1..n \<rightarrow> S]" *)
    qed
  qed (auto simp: Int_def)  (* the other inclusion is trivial since Nat \<subseteq> Int *)
  thus ?thesis by (simp only: Seq_def)
qed

text {* Sequences *}

(* NB: "\\circ" is already -- mistakenly -- used for relation composition in Tuples.thy !!*)
definition "Concat" :: "[c, c] \<Rightarrow> c" (infixl "\\o" 50)
  where "Concat(s,t) \<equiv> [i \<in> 1 .. (Len(s) + Len(t)) \<mapsto>
           IF i \<le> Len(s) THEN s[i] ELSE t[i - Len(s)]]"

(* SM: changed definition of Tail to use "--" instead of "-", which shouldn't change the semantics *)
definition "Tail"
  where "Tail(s) \<equiv> [i \<in> 1..(Len(s) - 1) \<mapsto> s[i + 1]]"

definition "SubSeq"
  where "SubSeq(s,m,n) \<equiv> [i \<in> 1..(1 + n - m) \<mapsto> s[i + m - 1]]"

theorem [norm]: "isAFcn(<<>>)" by simp
theorem [norm,simp]: "isAFcn(Append(s,e))" by (simp add: Append_def)
theorem [norm,simp]: "isAFcn(Tail(s))" by (simp add: Tail_def)
theorem [norm,simp]: "isAFcn(s \\o t)" by (simp add: Concat_def)
theorem [norm,simp]: "isAFcn(SubSeq(s,m,n))" by (auto simp add: SubSeq_def)
(*theorem [norm,simp]: "isAFcn(SelectSeq(s,P))" by (simp add: SelectSeq_def)*)

text {* These theorems are added as axioms to the translation. *}
theorem axiom_emptyseq: "s = <<>> \<Leftrightarrow> isASeq(s) \<and> DOMAIN s = {} \<and> Len(s) = 0" by auto
theorem axiom_isASeq: "isASeq(s) \<Longrightarrow> isAFcn(s) \<and> DOMAIN s = 1..Len(s) \<and> Len(s) \<in> Nat" by auto
theorem axiom_inSeq:  "s \<in> Seq(S) \<Longrightarrow> isASeq(s) \<and> (\<forall>i \<in> 1..Len(s): s[i] \<in> S)" by auto
theorem axiom_inSeq': "s \<in> Seq(S) \<Longrightarrow>
  isAFcn(s) \<and> DOMAIN s = 1..Len(s) \<and> Len(s) \<in> Nat
  \<and> (\<forall>i \<in> 1..Len(s): s[i] \<in> S)" by auto

theorem [norm,simp]: "DOMAIN (s \\o t) = 1..(Len(s)+Len(t))"by (simp add: Concat_def)
theorem [norm,simp]: "DOMAIN (Tail(s)) = 1..(Len(s) - 1)" by (simp add: Tail_def)
theorem [norm,simp]: "DOMAIN (SubSeq(s,m,n)) = 1..(1 + n - m)"  by (simp add: SubSeq_def)

(* Rules about <<>> *)
theorem [norm,simp]: "isAFcn(f) \<Longrightarrow> (DOMAIN f = {}) = (f = \<langle>\<rangle>)" by auto

theorem [norm,simp]: "isASeq(s) \<Longrightarrow> \<langle>\<rangle> \\o s = s" by (auto simp add: Concat_def)
theorem [norm,simp]: "isASeq(s) \<Longrightarrow> s \\o \<langle>\<rangle> = s" by (auto simp add: Concat_def)
theorem [norm]: "Append(\<langle>\<rangle>,e) = \<langle>e\<rangle>" ..
theorem [norm]: "Len(\<langle>\<rangle>) = 0" by simp
theorem [norm,simp]: "Tail(\<langle>\<rangle>) = \<langle>\<rangle>" by (auto simp: Tail_def OneToNegative)
theorem [norm]: "SubSeq(s,m,n) = \<langle>\<rangle> \<Longrightarrow> s = \<langle>\<rangle> \<or> 1..(1 + n - m) = {}"
  by (simp add: SubSeq_def)

(* Rules about Len *)
theorem [norm]: "Len(\<langle>e1\<rangle>) = 1" by simp
theorem [norm]: "Len(\<langle>e1,e2\<rangle>) = 2" by simp

theorem SeqLenGeqZero [norm]: "isASeq(s) \<Longrightarrow> 0 \<le> Len(s)" by simp

theorem [simp]:
  assumes 1: "isASeq(s)" and 2: "s \<noteq> \<langle>\<rangle>"
  shows "0 < Len(s)"
proof -
  from 1 have "0 \<le> Len(s)" by (rule SeqLenGeqZero)
  hence "0 < Len(s) \<or> Len(s) = 0" by (auto simp: nat_leq_less LenInNat[OF 1])
  with 2 show ?thesis by (auto simp: seqLenZeroIsEmpty[OF 1])
qed

(* SM: follows from above, but reasoning about integer arithmetic is tedious at best *)
theorem LenNonEmptySeq (*[simp]*):
  assumes "isASeq(s)" and "s \<noteq> \<langle>\<rangle>"
  shows "Len(s) - 1 \<in> Nat"
sorry

theorem [norm,simp]: "n \<in> Nat \<Longrightarrow> Len([x \<in> 1..n \<mapsto> e]) = n"
  by (intro LenI, auto)
theorem [norm,simp]: "n \<in> Int \<and> n \<le> 0 \<Longrightarrow> Len([x \<in> 1..n \<mapsto> e]) = 0"
  by (intro LenI, simp_all add: OneToNegative)

theorem [norm]: "\<lbrakk>isASeq(s); s \<noteq> \<langle>\<rangle>\<rbrakk> \<Longrightarrow> Len(Tail(s)) = Len(s) - 1"
  by (force simp: Tail_def LenNonEmptySeq)
theorem [norm]: "\<lbrakk>isASeq(s); isASeq(t)\<rbrakk> \<Longrightarrow> Len(s \\o t) = Len(s) + Len(t)"
  by (force simp: Concat_def)
theorem [norm]: "isASeq(s) \<Longrightarrow> Len(Append(s,e)) = Len(s) + 1"
  by (force simp: Append_def)
theorem [norm]: "isASeq(s) \<Longrightarrow> Len([s EXCEPT ![x] = y]) = Len(s)"
  by force

theorem [simp]:
  assumes 1: "isASeq(s)" and 2: "isASeq(t)" and 3: "s \\o t = \<langle>\<rangle>"
  shows "s = \<langle>\<rangle> \<and> t = \<langle>\<rangle>"
proof -
  from assms have "Len(s) = 0 \<and> Len(t) = 0" by (simp add: Concat_def natIntervalEmpty_iff)
  with 1 2 show ?thesis by auto
qed

(* theorem "isASeq(s) \<and> n \<le> Len(s) \<Longrightarrow> \<exists>m \<in> Nat: n \<le> m \<and> DOMAIN s = 1..m" *)
theorem "isASeq(s) \<and> 0 < Len(s) \<Longrightarrow> Len(s) \<noteq> 0" by auto

(* Rules of the form isASeq(seq) *)
theorem [norm]: "isASeq(\<langle>\<rangle>)" by simp
theorem [norm]: "isASeq(s) \<Longrightarrow> isASeq(Append(s,e))" by simp
theorem FcnIsASeq [norm,simp]: "n \<in> Nat \<Longrightarrow> isASeq([x \<in> 1..n \<mapsto> e(x)])" by (simp add: isASeq_def)
theorem FcnIsASeq2 [norm,simp]: "isASeq(s) \<Longrightarrow> isASeq([x \<in> 1..Len(s) \<mapsto> e(x)])" by simp
theorem [norm,simp]: "\<lbrakk>isASeq(s); isASeq(t)\<rbrakk> \<Longrightarrow> isASeq(s \\o t)" by (simp add: Concat_def)

theorem TailIsASeq [norm]:
  assumes s: "isASeq(s)"
  shows "isASeq(Tail(s))"
proof (cases "s = \<langle>\<rangle>")
  case True thus ?thesis by simp
next
  case False
  with s have "Len(s) - 1 \<in> Nat" by (rule LenNonEmptySeq)
  thus ?thesis by (auto simp: Tail_def)
qed

theorem SubSeqIsASeq [norm]:
  assumes s: "isASeq(s)" and m: "m \<in> Int" and n: "n \<in> Int"
  shows "isASeq(SubSeq(s,m,n))"
proof -
  let ?S = "{s[i + m - 1] : i \<in> 1 .. (1+n-m)}"
  have "SubSeq(s,m,n) \<in> [1..(1+n-m) \<rightarrow> ?S]" by (auto simp: SubSeq_def)
  moreover
  from m n have "1 + n - m \<in> Int" by simp
  ultimately
  have "SubSeq(s,m,n) \<in> UNION {[1..z \<rightarrow> ?S] : z \<in> Int}" by auto
  hence "SubSeq(s,m,n) \<in> Seq(?S)" by (simp add: SeqInt)
  thus ?thesis by auto
qed

theorem [norm]: "\<lbrakk>isASeq(s)\<rbrakk> \<Longrightarrow> isASeq([s EXCEPT ![a] = b])" by (simp add: except_def)

(* Rules of the form seq[i] *)
theorem [norm]: "\<lbrakk>isASeq(s); i \<in> 1..Len(s)\<rbrakk> \<Longrightarrow> Append(s,e)[i] = s[i]"
  by (auto simp: inNatInterval_iff)
theorem [norm]: "isASeq(s) \<Longrightarrow> Append(s,e)[Len(s) + 1] = e" by auto
theorem TailElt [norm]: "\<lbrakk>isASeq(s); i \<in> 1..(Len(s) - 1)\<rbrakk> \<Longrightarrow> Tail(s)[i] = s[i + 1]" by (simp add: Tail_def)
theorem [norm]: "i \<in> 1..(1 + n - m) \<Longrightarrow> SubSeq(s,m,n)[i] = s[i + m - 1]" by (simp add: SubSeq_def)
theorem ConcatEltFirst [norm]:
  assumes s: "isASeq(s)" and t: "isASeq(t)" and i: "i \<in> 1..Len(s)"
  shows "(s \\o t)[i] = s[i]"
proof -
  from assms have "i \<in> 1 .. (Len(s) + Len(t))" by (auto intro: nat_leq_trans)
  moreover
  from assms have "i \<le> Len(s)" by auto
  ultimately show ?thesis by (simp add: Concat_def)
qed

theorem ConcatEltSecond [norm]:
  assumes s: "isASeq(s)" and t: "isASeq(t)" and i: "i \<in> (Len(s)+1) .. (Len(s)+Len(t))"
  shows "(s \\o t)[i] = t[i - Len(s)]"
proof -
  from s i have "1 \<le> Succ[Len(s)]" "Succ[Len(s)] \<le> i" "1 \<in> Nat" "Succ[Len(s)] \<in> Nat" "i \<in> Nat" by auto
  hence "1 \<le> i" by (rule nat_leq_trans)
  moreover
  from i have "i \<in> Nat" "i \<le> Len(s) + Len(t)" by auto
  ultimately have "i \<in> 1 .. (Len(s) + Len(t))" by simp
  moreover
  have "\<not>(i \<le> Len(s))"
  proof
    assume 1: "i \<le> Len(s)"
    from s i have "Succ[Len(s)] \<le> i" "i \<in> Nat" "Len(s) \<in> Nat" by auto
    with 1 have "Succ[Len(s)] \<le> Len(s)" by (blast dest: nat_leq_trans)
    with s show "FALSE" by simp
  qed
  ultimately show ?thesis by (simp add: Concat_def)
qed

(* Rules of the form seq \<in> Seq(S) *)
theorem [norm]: "\<langle>\<rangle> \<in> Seq(S)" by auto
theorem [norm]: "e1 \<in> S \<and> e2 \<in> S \<Longrightarrow> \<langle>e1,e2\<rangle> \<in> Seq(S)" by auto
theorem [norm]: "\<langle>e1,e2\<rangle> \<in> Seq(S) \<Longrightarrow> e1 \<in> S \<and> e2 \<in> S" by force
theorem [norm]: "n \<in> Nat \<Longrightarrow> [i \<in> 1 .. n \<mapsto> e(i)] \<in> Seq(S) = (\<forall>i \<in> 1..n : e(i) \<in> S)"
  by (simp add:Seq_def FuncSet)
theorem [norm]:
  assumes n: "n \<in> Int" shows "[i \<in> 1 .. n \<mapsto> e(i)] \<in> Seq(S) = (\<forall>i \<in> 1..n : e(i) \<in> S)"
  apply (simp add: Seq_def FuncSet)
  using n apply (rule intCases, simp_all)
  by force
theorem AppendInSeq [norm]:
  assumes s: "isASeq(s)"
  shows "(Append(s,e) \<in> Seq(S)) \<Leftrightarrow> (e \<in> S \<and> s \<in> Seq(S))"
proof
  assume "Append(s,e) \<in> Seq(S)"
  hence 1: "\<forall>k \<in> 1 .. Len(Append(s,e)) : Append(s,e)[k] \<in> S" by auto
  have "\<forall>k \<in> 1 .. Len(s) : s[k] \<in> S"
  proof
    fix k
    assume k: "k \<in> 1 .. Len(s)"
    with s have "k \<in> 1 .. Len(Append(s,e))" by auto
    with 1 have "Append(s,e)[k] \<in> S" ..
    with s k show "s[k] \<in> S" by force
  qed
  moreover
  from 1 s have "e \<in> S" by simp
  moreover note s
  ultimately show "e \<in> S \<and> s \<in> Seq(S)" by auto
next
  assume "e \<in> S \<and> s \<in> Seq(S)"
  thus "Append(s,e) \<in> Seq(S)"
    by simp
qed

theorem [norm]: "\<lbrakk>e \<in> S; s \<in> Seq(S)\<rbrakk> \<Longrightarrow> Append(s,e) \<in> Seq(S)" by auto

theorem [norm]:
  assumes s: "s \<in> Seq(S)"
  shows "Tail(s) \<in> Seq(S)"
proof (cases "s = \<langle>\<rangle>")
  case True thus ?thesis by (simp add: emptySeqInSeq)
next
  case False
  with s have "Len(s) \<in> Nat" "Len(s) \<noteq> 0" by auto
  then obtain k where k: "k \<in> Nat" "Len(s) = Succ[k]" by (blast dest: natCases)
  hence k1: "Succ[k] - 1 = k" sorry (* integer arithmetic *)
  with k s have len: "Len(Tail(s)) = k" by (force simp: Tail_def)
  show ?thesis
  proof
    from s show "isASeq(Tail(s))" by (simp add: SeqIsASeq TailIsASeq)
  next
    fix i
    assume "i \<in> 1 .. Len(Tail(s))"
    with len have i: "i \<in> 1 .. k" by simp
    with k have "Succ[i] \<in> 1 .. Len(s)" by force
    moreover
    from i k k1 s have "Tail(s)[i] = s[Succ[i]]" by (auto simp: Tail_def)
    moreover
    note s i
    ultimately show "Tail(s)[i] \<in> S" by auto
  qed
qed

theorem [norm]:
  assumes s: "s \<in> Seq(S)" and t: "t \<in> Seq(S)"
  shows "s \\o t \<in> Seq(S)"
proof
  from s t show "isASeq(s \\o t)" by (auto simp: Concat_def)
next
  fix k
  assume k: "k \<in> 1 .. Len(s \\o t)"
  show "(s \\o t)[k] \<in> S"
  proof (cases "k \<in> 1 .. Len(s)")
    case True
    with s t show ?thesis by (auto simp: ConcatEltFirst SeqIsASeq)
  next
    case False
    with k have "k \<in> (Len(s)+1) .. (Len(s) + Len(t))" "k - Len(s) \<in> 1 .. Len(t)"
      sorry  (* SM: currently impossible to prove due to insufficient support for difference *)
    with s t show ?thesis by (auto simp: ConcatEltSecond SeqIsASeq)
  qed
qed

theorem [norm]:
  assumes s: "s \<in> Seq(S)" and m: "m \<in> Int" and n: "n \<in> Int"
     and mn: "(n < m) \<or> (m \<in> 1 .. Len(s) \<and> n \<in> m .. Len(s))"
  shows "SubSeq(s,m,n) \<in> Seq(S)"
proof
  from s m n show "isASeq(SubSeq(s,m,n))" by (auto intro: SubSeqIsASeq)
next
  fix k
  assume k: "k \<in> 1 .. Len(SubSeq(s,m,n))"
  with assms have "k \<in> 1 .. (1 + n - m)" "k + m - 1 \<in> 1 .. Len(s)" sorry (* missing integer arithmetic *)
  with s show "SubSeq(s,m,n)[k] \<in> S" by (auto simp: SubSeq_def)
qed

theorem [norm]:
  assumes s: "s \<in> Seq(S)" and e: "e \<in> S"
  shows "[s EXCEPT ![i] = e] \<in> Seq(S)"
proof -
  from s have "s \<in> [1 .. Len(s) \<rightarrow> S]" by auto
  with e have "[s EXCEPT ![i] = e] \<in> [1 .. Len(s) \<rightarrow> S]" by auto
  moreover
  from s have "Len(s) \<in> Nat" by auto
  ultimately show ?thesis by (auto simp: Seq_def)
qed

(* Rules of the form x = seq *)

theorem [norm]:
  assumes m: "m \<in> Int" and n: "n \<in> Int" and t: "t = SubSeq(s,m,n)" and i: "i \<in> m .. n"
  shows "t[1 + i - m] = s[i]"
proof -
  from m n i have "1 + i - m \<in> 1 .. (1 + n - m)" "(1 + i - m) + m - 1 = i"
    sorry (* integer arithmetic *)
  with t show ?thesis by (simp add: SubSeq_def)
qed

theorem [norm]:
  assumes n: "n \<in> 1..Len(s)"
  shows "SubSeq(s,n,n) = \<langle>s[n]\<rangle>"
proof -
  from n have "1 + n - n = 1" "1 + n - 1 = n" "n \<in> Nat"
    sorry (* integer arithmetic *)
  thus ?thesis by (auto simp: SubSeq_def)
qed

theorem [norm]: "x = Len(s) \<Longrightarrow> isASeq(s) \<Rightarrow> x \<in> Nat \<and> DOMAIN s = 1..x" by simp

theorem [norm]:
  assumes "isASeq(s)"
      and "x = Append(s,e)"
  shows "isASeq(x)"
    and "DOMAIN x = 1 .. (Len(s) + 1)"
    and "\<forall>i \<in> 1 .. Len(s): x[i] = s[i]"
    and "x[Len(s) + 1] = e"
  using assms by (simp_all, auto simp: Append_def)

theorem [norm]:
  assumes "isASeq(s)"
      and "isASeq(t)"
      and "x = (s \\o t)"
  shows "isASeq(x)"
    and "DOMAIN x = 1 .. (Len(s) + Len(t))"
    and "\<forall>i \<in> 1 .. Len(s): x[i] = s[i]"
    and "\<forall>i \<in> (Len(s) + 1) .. (Len(s) + Len(t)): x[i] = t[i - Len(s)]"
using assms by (auto simp: ConcatEltFirst ConcatEltSecond)

theorem [norm]:
  assumes "isASeq(s)"
      and "s \<noteq> \<langle>\<rangle>"
      and "x = Tail(s)"
  shows "isASeq(x)"
    and "DOMAIN x = 1 .. (Len(s) - 1)"
    and "\<forall>i \<in> 1 .. (Len(s) - 1): x[i] = s[i + 1]"
using assms by (simp_all add: TailIsASeq TailElt)

text {* Setting up the smt tactic. *}

thm norm

ML {*
fun smt_tac ctxt =
(*  let
    val my_ctxt =
      ctxt |> Simplifier.map_simpset
        (fold Splitter.add_split @{thms prod.splits} #>
          Simplifier.add_simp @{thm split_def})
  in ALLGOALS (clarsimp_tac my_ctxt) end *)
  ALLGOALS (clarsimp_tac ctxt)
*}

method_setup smt = {*
  (* concrete syntax like "clarsimp", "auto" etc. *)
  Method.sections Clasimp.clasimp_modifiers >>
  (* Isar method boilerplate *)
  (fn _ => fn ctxt => SIMPLE_METHOD (CHANGED (smt_tac ctxt)))
*}

end
