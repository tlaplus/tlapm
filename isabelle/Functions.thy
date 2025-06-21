(*  Title:      TLA+/Functions.thy
    Author:     Stephan Merz, Inria Nancy
    Copyright (C) 2008-2025  INRIA and Microsoft Corporation
    License:    BSD
    Version:    Isabelle2025
*)

section \<open> \tlaplus{} Functions \<close>

theory Functions
imports SetTheory
begin

subsection \<open> Syntax and axioms for functions \<close>

text \<open>
  Functions in \tlaplus{} are not defined (e.g., as sets of pairs),
  but axiomatized, and in fact, pairs and tuples will be defined as special
  functions. Incidentally, this approach helps us to identify functional
  values, and to automate the reasoning about them. This theory considers
  only unary functions; functions with multiple arguments are defined
  as functions over products. We follow the development of functions given
  in Section 16.1 of ``Specifying Systems''.
\<close>

consts
  Fcn      :: "[c, c \<Rightarrow> c] \<Rightarrow> c"                       \<comment> \<open> function constructor \<close>
  DOMAIN   :: "c \<Rightarrow> c"         ("(DOMAIN _)" [100]90)  \<comment> \<open> domain of a function \<close>
  fapply   :: "[c, c] \<Rightarrow> c"    ("(_[_])" [89,0]90)     \<comment> \<open> function application \<close>

syntax
  "@Fcn"   :: "[idt,c,c] \<Rightarrow> c" ("(1[_ \<in> _ \<mapsto> _])" 900)
syntax (ASCII)
  "@Fcn"   :: "[idt,c,c] \<Rightarrow> c" ("(1[_ \\in _ |-> _])" 900)
translations
  "[x \<in> S \<mapsto> e]"  \<rightleftharpoons>  "CONST Fcn(S, \<lambda>x. e)"

axiomatization where
  DOMAIN [simp]:  "DOMAIN Fcn(S,e) = S" and
  fapply [simp]:  "v \<in> S \<Longrightarrow> Fcn(S,e)[v] = e(v)"

text \<open>The predicate @{text isAFcn} characterizes functional values.\<close>
definition isAFcn :: "c \<Rightarrow> c"
  where "isAFcn(f) \<equiv> f = Fcn(DOMAIN f, \<lambda>x. f[x])"

axiomatization where
  fcnIsAFcn [intro!, simp]: "isAFcn(Fcn(S,e))"

text \<open>
  Two functions are equal if they have the same domain and agree on all
  arguments within the domain.
\<close>
axiomatization where fcnEqual[elim!]:
  "\<lbrakk>isAFcn(f); isAFcn(g); DOMAIN f = DOMAIN g; \<forall>x \<in> DOMAIN g : f[x]=g[x]\<rbrakk>
   \<Longrightarrow> f = g"

text \<open>
  @{text "FuncSet(S,T)"} represents the set of functions with domain @{text S}
  and co-domain @{text T}. It cannot be defined as a set comprehension because
  we do not have a bounding set for its elements.
\<close>
consts
  FuncSet  :: "[c,c] \<Rightarrow> c"     ("([_ \<rightarrow> _])" 900)      \<comment> \<open> function space \<close>
syntax (ASCII)
  FuncSet  :: "[c,c] \<Rightarrow> c"     ("([_ -> _])" 900)

axiomatization where
  FuncSet: "f \<in> [S \<rightarrow> T] \<Leftrightarrow> isAFcn(f) \<and> DOMAIN f = S \<and> (\<forall>x\<in>S : f[x] \<in> T)"

lemmas \<comment> \<open> establish set equality for domains and function spaces \<close>
  setEqualI [where A = "DOMAIN f" for f, intro!]
  setEqualI [where B = "DOMAIN f" for f, intro!]
  setEqualI [where A = "[S \<rightarrow> T]" for S T, intro!]
  setEqualI [where B = "[S \<rightarrow> T]" for S T, intro!]


definition except   :: "[c,c,c] \<Rightarrow> c"    \<comment> \<open> function override \<close>
where "except(f,v,e) \<equiv> [x \<in> DOMAIN f \<mapsto> (IF x=v THEN e ELSE f[x])]"

nonterminal
  xcpt
syntax
  "_xcpt"    :: "[c,c] \<Rightarrow> xcpt"          ("(![_] =/ _)")
  "_xcpts"   :: "[c,c,xcpt] \<Rightarrow> xcpt"     ("(![_] =/ _,/ _)")
  "_except"  :: "[c,xcpt] \<Rightarrow> c"          ("[_ EXCEPT/ _]" [900,0] 900)
translations
  "_except(f, _xcpts(v,e, xcs))"  \<rightleftharpoons>  "_except(CONST except(f,v,e), xcs)"
  "[f EXCEPT ![v] = e]"           \<rightleftharpoons>  "CONST except(f,v,e)"

text \<open>
  The following operators are useful for representing functions with
  finite domains by enumeration. They are not part of basic \tlaplus{},
  but they are defined in the TLC module of the standard library.
\<close>

definition oneArg :: "[c,c] \<Rightarrow> c"        (infixl ":>" 75)
where "d :> e  \<equiv>  [x \<in> {d} \<mapsto> e]"

definition extend :: "[c,c] \<Rightarrow> c"        (infixl "@@" 70)
where "f @@ g  \<equiv>  [x \<in> (DOMAIN f) \<union> (DOMAIN g) \<mapsto>
                   IF x \<in> DOMAIN f THEN f[x] ELSE g[x]]"


subsection \<open> @{text isAFcn}: identifying functional values \<close>

lemma boolifyIsAFcn [simp]: "boolify(isAFcn(f)) = isAFcn(f)"
by (simp add: isAFcn_def)

lemma isBoolIsAFcn [intro!,simp]: "isBool(isAFcn(f))"
by (unfold isBool_def, rule boolifyIsAFcn)

(***
lemma [intro!]:
  "\<lbrakk>isBool(P); isAFcn(f) \<Leftrightarrow> P\<rbrakk> \<Longrightarrow> isAFcn(f) = P"
  "\<lbrakk>isBool(P); P \<Leftrightarrow> isAFcn(f)\<rbrakk> \<Longrightarrow> P = isAFcn(f)"
by auto
***)

lemma [intro!,simp]: "isAFcn([f EXCEPT ![c] = e])"
by (simp add: except_def)

text \<open>
  We derive instances of axiom @{text fcnEqual} that help in automating
  proofs about equality of functions.
\<close>

lemma fcnEqual2[elim!]:
   "\<lbrakk>isAFcn(g); isAFcn(f); DOMAIN f = DOMAIN g; \<forall>x \<in> DOMAIN g : f[x]=g[x]\<rbrakk>
    \<Longrightarrow> f = g"
by (rule fcnEqual)

text \<open> possibly useful as a simplification rule, but cannot be active by default \<close>
lemma fcnEqualIff:
  assumes "isAFcn(f)" and "isAFcn(g)"
  shows "(f = g) = (DOMAIN f = DOMAIN g \<and> (\<forall>x \<in> DOMAIN g : f[x] = g[x]))"
using assms by auto

lemma [intro!]:
  "\<lbrakk>isAFcn(f); DOMAIN f = S; \<forall>x \<in> S : f[x] = e(x)\<rbrakk> \<Longrightarrow> [x \<in> S \<mapsto> e(x)] = f"
  "\<lbrakk>isAFcn(f); DOMAIN f = S; \<forall>x \<in> S : f[x] = e(x)\<rbrakk> \<Longrightarrow> f = [x \<in> S \<mapsto> e(x)]"
by auto

lemma [intro!]:
  "\<lbrakk>isAFcn(f); DOMAIN f = DOMAIN g; v \<in> DOMAIN g \<Longrightarrow> f[v] = w;
    \<forall>y \<in> DOMAIN g : y \<noteq> v \<Rightarrow> f[y] = g[y]\<rbrakk>
   \<Longrightarrow> [g EXCEPT ![v] = w] = f"
  "\<lbrakk>isAFcn(f); DOMAIN f = DOMAIN g; v \<in> DOMAIN g \<Longrightarrow> f[v] = w;
    \<forall>y \<in> DOMAIN g : y \<noteq> v \<Rightarrow> f[y] = g[y]\<rbrakk>
   \<Longrightarrow> f = [g EXCEPT ![v] = w]"
by (auto simp: except_def)


subsection \<open> Theorems about functions \<close>

lemma fcnCong (*[cong] -- not active by default (??) *):
  assumes "S = T" and "\<And>x. x \<in> T \<Longrightarrow> e(x) = f(x)"
  shows "[x \<in> S \<mapsto> e(x)] = [x \<in> T \<mapsto> f(x)]"
using assms by auto

lemma domainExcept [simp]: "DOMAIN [f EXCEPT ![v] = e] = DOMAIN f"
by (simp add: except_def)

lemma applyExcept [simp]:
  assumes "w \<in> DOMAIN f"
  shows "[f EXCEPT ![v] = e][w] = (IF w=v THEN e ELSE f[w])"
using assms by (auto simp: except_def)

lemma exceptI:
  assumes "w \<in> DOMAIN f" and "v=w \<Longrightarrow> P(e)" and "v \<noteq> w \<Longrightarrow> P(f[w])"
  shows "P([f EXCEPT ![v]=e][w])"
using assms by (auto simp: except_def intro: condI)

lemma exceptTrivial:
  assumes "v \<notin> DOMAIN f" and "isAFcn(f)"
  shows "[f EXCEPT ![v]=e] = f"
using assms by auto

lemma exceptEqual [simp]:
  assumes "isAFcn(f)"
  shows "([f EXCEPT ![v] = e] = f) = (v \<notin> DOMAIN f \<or> f[v] = e)"
using assms by (auto simp: fcnEqualIff)

text \<open>
  A function can be defined from a predicate. Using the @{text CHOOSE}
  operator, the definition does not require the predicate to be
  functional.
\<close>

lemma fcnConstruct:
  assumes hyp: "\<forall>x \<in> S : \<exists>y : P(x,y)"
  shows "\<exists>f : isAFcn(f) \<and> DOMAIN f = S \<and> (\<forall>x\<in>S : P(x, f[x]))"
    (is "\<exists>f : ?F(f)")
proof -
  let ?fn = "[x \<in> S \<mapsto> CHOOSE y : P(x,y)]"
  have "?F(?fn)"
  proof auto
    fix x
    assume "x \<in> S"
    with hyp have "\<exists>y : P(x,y)" by auto
    thus "P(x, CHOOSE y : P(x,y))" by (rule chooseI_ex)
  qed
  thus ?thesis ..
qed


subsection \<open> Function spaces \<close>

lemma inFuncSetIff:
  "(f \<in> [S \<rightarrow> T]) = (isAFcn(f) \<and> DOMAIN f = S \<and> (\<forall>x\<in>S : f[x] \<in> T))"
proof (rule boolEqual)
  show "f \<in> [S \<rightarrow> T] \<Leftrightarrow> isAFcn(f) \<and> DOMAIN f = S \<and> (\<forall>x\<in>S : f[x] \<in> T)"
    by (rule FuncSet)
qed (auto)

lemma funcSetIsAFcn [simp]:
  assumes "f \<in> [S \<rightarrow> T]"
  shows "isAFcn(f)"
using assms unfolding inFuncSetIff by blast

lemma funcSetDomain [simp]:
  assumes "f \<in> [S \<rightarrow> T]"
  shows "DOMAIN f = S"
using assms unfolding inFuncSetIff by blast

lemma funcSetValue [simp]:
  assumes "f \<in> [S \<rightarrow> T]" and "x \<in> S"
  shows "f[x] \<in> T"
using assms unfolding inFuncSetIff by blast

lemma funcSetE (*[elim]*):
  assumes "f \<in> [S \<rightarrow> T]" and "x \<in> S" and "\<lbrakk>isAFcn(f); DOMAIN f = S; f[x] \<in> T\<rbrakk> \<Longrightarrow> P"
  shows P
using assms unfolding inFuncSetIff by blast

lemma funcSetE' [elim]:
  assumes "f \<in> [S \<rightarrow> T]" and "\<lbrakk>isAFcn(f); DOMAIN f = S; \<forall>x \<in> S : f[x] \<in> T\<rbrakk> \<Longrightarrow> P"
  shows P
using assms unfolding inFuncSetIff by blast

lemma funcSetFcnEqual [elim!]:
  assumes "f \<in> [S \<rightarrow> T]" and "isAFcn(g)" and "DOMAIN g = S"
      and "\<forall>x \<in> S: f[x] = g[x]"
  shows "f = g"
using assms by auto

declare funcSetFcnEqual[symmetric, elim]

lemma inFuncSet [intro!]:
  assumes "isAFcn(f)" and "DOMAIN f = S" and "\<forall>x \<in> S : f[x] \<in> T"
  shows "f \<in> [S \<rightarrow> T]"
using assms unfolding inFuncSetIff by blast

lemma funcSetSubRange:
  assumes "f \<in> [S \<rightarrow> T]" and "T \<subseteq> U"
  shows "f \<in> [S \<rightarrow> U]"
using assms by auto

lemma funcSetEmpty [simp]:
  "([S \<rightarrow> T] = {}) = ((S \<noteq> {}) \<and> (T = {}))"
  "({} = [S \<rightarrow> T]) = ((S \<noteq> {}) \<and> (T = {}))"
by auto

lemma isAFcnFuncSet:
  assumes hyp: "isAFcn(f)"
  shows "\<exists>S, T : f \<in> [S \<rightarrow> T]"
using assms by blast

lemma functionInFuncSet:
  assumes "\<forall>x \<in> S : e(x) \<in> T"
  shows "[x\<in>S \<mapsto> e(x)] \<in> [S \<rightarrow> T]"
using assms by auto

lemma exceptInFuncSet[elim!]:
  assumes 1: "f \<in> [S \<rightarrow> U]" and 2: "U \<subseteq> T"
      and 3: "\<lbrakk>v \<in> S; isAFcn(f); DOMAIN f = S; \<forall>x \<in> S : f[x] \<in> U\<rbrakk> \<Longrightarrow> e \<in> T"
  shows "[f EXCEPT ![v]=e] \<in> [S \<rightarrow> T]" (is "?exc \<in> [S \<rightarrow> T]")
proof
  from 1 show "DOMAIN ?exc = S" by auto
next
  from assms show "\<forall>x \<in> S : ?exc[x] \<in> T" by auto
qed (simp)

text \<open>
  The following special case is useful for invariant proofs where one
  proves type correctness. The additional hypotheses make the type of $f$
  available and are useful, for example, when the expression $e$ is of the
  form $f[u]$ for some $u \in S$.
\<close>

lemma exceptInFuncSetSame:
  assumes "f \<in> [S \<rightarrow> T]"
  and "\<lbrakk>v \<in> S; isAFcn(f); DOMAIN f = S; \<forall>x \<in> S : f[x] \<in> T\<rbrakk> \<Longrightarrow> e \<in> T"
  shows "[f EXCEPT ![v]=e] \<in> [S \<rightarrow> T]"
using assms by auto


subsection \<open> Finite functions and extension \<close>

lemma oneArgIsAFcn [simp, intro!]: "isAFcn(d :> e)"
by (simp add: oneArg_def)

lemma oneArgDomain [simp]: "DOMAIN (d :> e) = {d}"
by (simp add: oneArg_def)

lemma oneArgVal [simp]: "(d:>e)[d] = e"
by (simp add: oneArg_def)

lemma oneArgFuncSet: "(d :> e) \<in> [{d} \<rightarrow> {e}]"
by auto

lemma extendIsAFcn [simp, intro!]: "isAFcn (f @@ g)"
by (simp add: extend_def)

lemma extendDomain [simp]: "DOMAIN (f @@ g) = (DOMAIN f) \<union> (DOMAIN g)"
by (simp add: extend_def)

lemma extendVal [simp]:
  assumes "x \<in> (DOMAIN f) \<union> (DOMAIN g)"
  shows "(f @@ g)[x] = (IF x \<in> DOMAIN f THEN f[x] ELSE g[x])"
using assms by (simp add: extend_def)

lemma extendFuncSet:
  assumes "f \<in> [S \<rightarrow> U]" and "g \<in> [T \<rightarrow> V]"
  shows "f @@ g \<in> [S \<union> T \<rightarrow> U \<union> V]"
using assms by auto

lemma oneArgEqual [intro!]:
  "\<lbrakk>isAFcn(f); DOMAIN f = {d}; f[d] = e\<rbrakk> \<Longrightarrow> (d :> e) = f"
  "\<lbrakk>isAFcn(f); DOMAIN f = {d}; f[d] = e\<rbrakk> \<Longrightarrow> f = (d :> e)"
by force+

lemma oneArgEqualIff [simp]:
  "isAFcn(f) \<Longrightarrow> (f = (d :> e)) = ((DOMAIN f = {d}) \<and> f[d] = e)"
  "isAFcn(f) \<Longrightarrow> ((d :> e) = f) = ((DOMAIN f = {d}) \<and> f[d] = e)"
by auto

text \<open> infer equations @{text "f = g @@ h"} \<close>
lemmas
  fcnEqual[where f = "f @@ h" for f h, intro!]
  fcnEqual[where g = "g @@ h" for g h, intro!]

lemma extendEqualIff [simp]:
  "isAFcn(f) \<Longrightarrow> (f = g @@ h) =
                (DOMAIN f = (DOMAIN g) \<union> (DOMAIN h) \<and>
                (\<forall>x \<in> DOMAIN g : f[x] = g[x]) \<and>
                (\<forall>x \<in> DOMAIN h \\ DOMAIN g : f[x] = h[x]))"
  "isAFcn(f) \<Longrightarrow> (g @@ h = f) =
                (DOMAIN f = (DOMAIN g) \<union> (DOMAIN h) \<and>
                (\<forall>x \<in> DOMAIN g : g[x] = f[x]) \<and>
                (\<forall>x \<in> DOMAIN h \\ DOMAIN g : h[x] = f[x]))"
by auto

(** Examples **
lemma "(a :> {} @@ b :> {}) = (b :> {} @@ a :> {})"
by auto

lemma "({} :> {}) \<noteq> ({a} :> {})"
by simp

lemma "({} :> {} @@ b :> {}) \<noteq> ({b} :> {})"
by simp

lemma "({} :> {} @@ {b} :> {}) \<noteq> ({b} :> {} @@ {} :> {a})"
by auto

**)

subsection \<open> Notions about functions \<close>

subsubsection \<open> Image and Range \<close>

text \<open>
  Image of a set under a function, and range of a function.
  Because the application of a function to an argument outside of its domain
  usually leads to silliness, we restrict to the domain when defining
  the image.
\<close>

definition Image
where "Image(f,A) \<equiv> { f[x] : x \<in> A \<inter> DOMAIN f }"

text \<open>
  The range of a function, introduced as an abbreviation.
  To reason about the range, apply the theorems about @{text Image},
  or simply rewrite with @{text Image_def}.
\<close>

abbreviation Range
where "Range(f) \<equiv> Image(f, DOMAIN f)"

lemma imageI [intro]:
  assumes "x \<in> A" and "x \<in> DOMAIN f"
  shows "f[x] \<in> Image(f,A)"
using assms by (auto simp: Image_def)

lemma imageI_eq:
  assumes "x \<in> A" and "x \<in> DOMAIN f" and "y = f[x]"
  shows "y \<in> Image(f,A)"
using assms by (auto simp: Image_def)

lemma imageI_exEq [intro]:
  assumes "\<exists>x \<in> A \<inter> DOMAIN f : y = f[x]"
  shows "y \<in> Image(f,A)"
using assms by (auto intro: imageI_eq)

lemma rangeI:  \<comment> \<open> useful special case \<close>
  assumes "\<exists>x \<in> DOMAIN f: y = f[x]"
  shows "y \<in> Range(f)"
using assms by auto

lemma imageE [elim]:
  assumes "y \<in> Image(f,A)" and "\<And>x. \<lbrakk>x \<in> A; x \<in> DOMAIN f; y = f[x]\<rbrakk> \<Longrightarrow> P"
  shows "P"
using assms by (auto simp: Image_def)

lemma imageEqualI [intro!]:
  assumes "\<And>y. y \<in> B \<Leftrightarrow> (\<exists>x \<in> A \<inter> DOMAIN f : y = f[x])"
  shows "Image(f,A) = B"
using assms by (intro setEqualI, auto simp: Image_def)

declare imageEqualI [symmetric,intro!]

lemma inImageiff [simp]:
  "(y \<in> Image(f,A)) = (\<exists>x \<in> A \<inter> DOMAIN f : y = f[x])"
by blast

lemma imageEmpty [simp]:
  "(Image(f,A) = {}) = (A \<inter> DOMAIN f = {})"
  "({} = Image(f,A)) = (A \<inter> DOMAIN f = {})"
by auto

subsubsection \<open> Injective functions \<close>

definition InjectiveOn
where "InjectiveOn(f,A) \<equiv> \<forall>x,y \<in> A \<inter> DOMAIN f : f[x] = f[y] \<Rightarrow> x = y"

abbreviation Injective   \<comment> \<open> special case: injective function \<close>
where "Injective(f) \<equiv> InjectiveOn(f, DOMAIN f)"

definition Injections
where "Injections(S,T) \<equiv> { f \<in> [S \<rightarrow> T] : Injective(f) }"

lemmas
  setEqualI [where A = "Injections(S,T)" for S T, intro!]
  setEqualI [where B = "Injections(S,T)" for S T, intro!]

lemma injectiveOnIsBool [intro!,simp]:
  "isBool(InjectiveOn(f,A))"
by (simp add: InjectiveOn_def)

lemma boolifyInjectiveOn [simp]:
  "boolify(InjectiveOn(f,A)) = InjectiveOn(f,A)"
by auto

text \<open> For the moment, no support by default for automatic reasoning. \<close>

lemma injectiveOnI:
  assumes "\<And>x y. \<lbrakk> x \<in> A; x \<in> DOMAIN f; y \<in> A; y \<in> DOMAIN f; f[x] = f[y] \<rbrakk> \<Longrightarrow> x = y"
  shows "InjectiveOn(f,A)"
using assms by (auto simp: InjectiveOn_def)

lemma injectiveOnD:
  assumes "f[x] = f[y]" and "InjectiveOn(f,A)"
  and "x \<in> A" and "x \<in> DOMAIN f" and "y \<in> A" and "y \<in> DOMAIN f"
  shows "x = y"
using assms by (auto simp: InjectiveOn_def)

lemma injectiveOnE:
  assumes "InjectiveOn(f,A)"
  and "(\<And>x y. \<lbrakk> x \<in> A; x \<in> DOMAIN f; y \<in> A; y \<in> DOMAIN f; f[x] = f[y] \<rbrakk> \<Longrightarrow> x=y) \<Longrightarrow> P"
  shows "P"
using assms by (auto simp: InjectiveOn_def)

lemma injectiveOnIff:  \<comment> \<open> useful for simplification \<close>
  assumes "InjectiveOn(f,A)" and "x \<in> A \<inter> DOMAIN f" and "y \<in> A \<inter> DOMAIN f"
  shows "(f[x] = f[y]) = (x = y)"
using assms injectiveOnD by auto

lemma injectiveOnSubset:
  assumes "InjectiveOn(f,A)" and "B \<subseteq> A"
  shows "InjectiveOn(f,B)"
using assms by (auto simp: InjectiveOn_def)

lemma injectiveOnSetminus:
  assumes "InjectiveOn(f,A)"
  shows "InjectiveOn(f, A \<setminus> B)"
using assms by (auto simp: InjectiveOn_def)

text \<open>The existence of an inverse function implies injectivity.\<close>

lemma inverseThenInjective:
  assumes inv: "\<And>x. \<lbrakk> x \<in> A; x \<in> DOMAIN f \<rbrakk> \<Longrightarrow> g[f[x]] = x"
  shows "InjectiveOn(f,A)"
proof (rule injectiveOnI)
  fix x y
  assume x: "x \<in> A" "x \<in> DOMAIN f"
     and y: "y \<in> A" "y \<in> DOMAIN f"
     and eq: "f[x] = f[y]"
  from x have x1: "x = g[f[x]]" by (rule sym[OF inv])
  from y have y1: "g[f[y]] = y" by (rule inv)
  from x1 y1 eq show "x = y" by simp
qed

text \<open> Trivial cases. \<close>

lemma injectiveOnEmpty [intro!,simp]:
  "InjectiveOn(f, {})"
by (blast intro: injectiveOnI)

lemma injectiveOnSingleton [intro!,simp]:
  "InjectiveOn(f, {x})"
by (blast intro: injectiveOnI)

(** in particular: **
lemma "Injective(d :> e)"
by simp
**)

text \<open> Injectivity and EXCEPT. \<close>

lemma injectiveOnExcept:
  assumes 1: "InjectiveOn(f, A \\ {v})" and 2: "isAFcn(f)"
  and 3: "v \<in> DOMAIN f \<Rightarrow> (\<forall>x \<in> (DOMAIN f \<inter> A) \\ {v} : f[x] \<noteq> e)"
  shows "InjectiveOn([f EXCEPT ![v] = e], A)" (is "InjectiveOn(?exc, A)")
proof (rule injectiveOnI)
  fix x y
  assume x1: "x \<in> A" and x2: "x \<in> DOMAIN ?exc"
     and y1: "y \<in> A" and y2: "y \<in> DOMAIN ?exc"
     and eq: "?exc[x] = ?exc[y]"
  show "x = y"
  proof (cases "v \<in> DOMAIN f")
    case False
    from False 2 have "?exc = f" by (rule exceptTrivial)
    with eq have eq': "f[x] = f[y]" by simp
    from False x1 x2 have x3: "x \<in> (A \\ {v})" "x \<in> DOMAIN f" by auto
    from False y1 y2 have y3: "y \<in> (A \\ {v})" "y \<in> DOMAIN f" by auto
    from eq' 1 x3 y3 show "x = y" by (rule injectiveOnD)
  next
    case True
    with 3 have 4: "\<forall>x \<in> (DOMAIN f \<inter> A) \\ {v} : f[x] \<noteq> e" by (rule mp)
    show "x = y"
    proof (rule classical)
      assume neq: "x \<noteq> y"
      have "x \<noteq> v"
      proof
	assume contr: "x = v"
	with True have fx: "?exc[x] = e" by auto
	from y2 contr neq have "?exc[y] = f[y]" by auto
	with contr neq y1 y2 4 have "?exc[y] \<noteq> e" by auto
	with fx eq show "FALSE" by simp
      qed
      with x1 x2 have x3: "x \<in> (A \\ {v})" "x \<in> DOMAIN f" by auto
      have "y \<noteq> v"  \<comment> \<open>symmetrical reasoning\<close>
      proof
	assume contr: "y = v"
	with True have fy: "?exc[y] = e" by auto
	from x2 contr neq have "?exc[x] = f[x]" by auto
	with contr neq x1 x2 4 have "?exc[x] \<noteq> e" by auto
	with fy eq show "FALSE" by simp
      qed
      with y1 y2 have y3: "y \<in> (A \\ {v})" "y \<in> DOMAIN f" by auto
      from eq x3 y3 have "f[x] = f[y]" by auto
      from this 1 x3 y3 show "x = y" by (rule injectiveOnD)
    qed
  qed
qed

lemma injectiveOnExtend:
  assumes f: "InjectiveOn(f,A)" and g: "InjectiveOn(g, A \\ DOMAIN f)"
  and disj: "Image(f, A) \<inter> Image(g, A \\ DOMAIN f) = {}"
  shows "InjectiveOn(f @@ g, A)"
proof (rule injectiveOnI)
  fix x y
  assume 1: "x \<in> A" "y \<in> A" "x \<in> DOMAIN (f @@ g)" "y \<in> DOMAIN (f @@ g)"
     and 2: "(f @@ g)[x] = (f @@ g)[y]"
  show "x = y"
  proof (cases "x \<in> DOMAIN f")
    case True
    have "y \<in> DOMAIN f"
    proof (rule contradiction)
      assume y: "y \<notin> DOMAIN f"
      from 1 True have "(f @@ g)[x] \<in> Image(f,A)" by auto
      moreover
      from 1 y have "(f @@ g)[y] \<in> Image(g, A \\ DOMAIN f)" by auto
      moreover
      note 2
      ultimately have "(f @@ g)[y] \<in> Image(f,A) \<inter> Image(g, A \\ DOMAIN f)" by auto
      with disj show FALSE by blast
    qed
    with True f 1 2 show "x = y" by (auto elim: injectiveOnD)
  next
    case False
    have "y \<notin> DOMAIN f"
    proof
      assume y: "y \<in> DOMAIN f"
      with 1 have "(f @@ g)[y] \<in> Image(f,A)" by auto
      moreover
      from False 1 have "(f @@ g)[x] \<in> Image(g, A \\ DOMAIN f)" by auto
      moreover
      note 2
      ultimately have "(f @@ g)[y] \<in> Image(f,A) \<inter> Image(g, A \\ DOMAIN f)" by auto
      with disj show FALSE by blast
    qed
    with False g 1 2 show "x = y" by (auto elim: injectiveOnD)
  qed
qed

lemma injectiveExtend: \<comment> \<open> special case \<close>
  assumes 1: "Injective(f)" and 2: "InjectiveOn(g, DOMAIN g \<setminus> DOMAIN f)"
  and 3: "Range(f) \<inter> Image(g, DOMAIN g \<setminus> DOMAIN f) = {}"
  shows "Injective(f @@ g)"
proof (rule injectiveOnExtend)
  from 1 show "InjectiveOn(f, DOMAIN (f @@ g))"
    by (auto simp: InjectiveOn_def)
next
  from 2 show "InjectiveOn(g, DOMAIN (f @@ g) \<setminus> DOMAIN f)"
    by (auto simp: InjectiveOn_def)
next
  show "Image(f, DOMAIN (f @@ g)) \<inter> Image(g, DOMAIN (f @@ g) \<setminus> DOMAIN f) = {}"
  proof (clarify)
    fix x
    assume xf: "x \<in> Image(f, DOMAIN (f @@ g))"
       and xg: "x \<in> Image(g, DOMAIN (f @@ g) \<setminus> DOMAIN f)"
    from xf have "x \<in> Range(f)" by auto
    moreover
    from xg have "x \<in> Image(g, DOMAIN g \<setminus> DOMAIN f)" by auto
    moreover
    note 3
    ultimately show FALSE by blast
  qed
qed

lemma injectiveOnImageInter:
  assumes "InjectiveOn(f,A)" and "B \<subseteq> A" and "C \<subseteq> A"
  shows "Image(f, B \<inter> C) = Image(f,B) \<inter> Image(f,C)"
using assms by (auto simp: InjectiveOn_def Image_def)

lemma injectiveOnImageSetminus:
  assumes "InjectiveOn(f,A)" and "B \<subseteq> A" and "C \<subseteq> A"
  shows "Image(f, B \<setminus> C) = Image(f,B) \<setminus> Image(f,C)"
using assms by (auto simp: InjectiveOn_def Image_def)

lemma injectiveImageMember:
  assumes "Injective(f)" and "a \<in> DOMAIN f"
  shows "(f[a] \<in> Image(f,A)) = (a \<in> A)"
using assms by (auto simp: InjectiveOn_def Image_def)

lemma injectiveImageSubset:
  assumes f: "Injective(f)"
  shows "(Image(f,A) \<subseteq> Image(f,B)) = (A \<inter> DOMAIN f \<subseteq> B \<inter> DOMAIN f)"
proof -
  {
    fix x
    assume ab: "Image(f,A) \<subseteq> Image(f,B)" and x: "x \<in> A" "x \<in> DOMAIN f"
    from x have "f[x] \<in> Image(f,A)" by (rule imageI)
    with ab have "f[x] \<in> Image(f,B)" ..
    then obtain z where z: "z \<in> B \<inter> DOMAIN f" "f[x] = f[z]" by auto
    from f z x have "x = z" by (auto elim: injectiveOnD)
    with z have "x \<in> B" by simp
  }
  thus ?thesis by blast \<comment> \<open>the reverse inclusion is proved automatically\<close>
qed

lemma injectiveImageEqual:
  assumes f: "Injective(f)"
  shows "(Image(f,A) = Image(f,B)) = (A \<inter> DOMAIN f = B \<inter> DOMAIN f)"
proof -
  have "(Image(f,A) = Image(f,B)) = (Image(f,A) \<subseteq> Image(f,B) \<and> Image(f,B) \<subseteq> Image(f,A))"
    by auto
  also from f have "\<dots> = (A \<inter> DOMAIN f \<subseteq> B \<inter> DOMAIN f \<and> B \<inter> DOMAIN f \<subseteq> A \<inter> DOMAIN f)"
    by (simp add: injectiveImageSubset)
  also have "\<dots> = (A \<inter> DOMAIN f = B \<inter> DOMAIN f)"
    by auto
  finally show ?thesis .
qed

lemma injectionsI:
  assumes "f \<in> [S \<rightarrow> T]" and "\<And>x y. \<lbrakk> x \<in> S; y \<in> S; f[x] = f[y] \<rbrakk> \<Longrightarrow> x = y"
  shows "f \<in> Injections(S,T)"
using assms funcSetDomain by (auto simp: Injections_def InjectiveOn_def)

lemma injectionsE:
  assumes 1: "f \<in> Injections(S,T)"
  and 2: "\<lbrakk> f \<in> [S \<rightarrow> T]; \<And>x y. \<lbrakk> x \<in> S; y \<in> S; f[x] = f[y] \<rbrakk> \<Longrightarrow> x = y \<rbrakk> \<Longrightarrow> P"
  shows P
using assms unfolding Injections_def InjectiveOn_def by blast


subsubsection \<open> Surjective functions \<close>

definition Surjective
where "Surjective(f,A) \<equiv> A \<subseteq> Range(f)"

definition Surjections
where "Surjections(S,T) \<equiv> { f \<in> [S \<rightarrow> T] : Surjective(f,T) }"

lemmas
  setEqualI [where A = "Surjections(S,T)" for S T, intro!]
  setEqualI [where B = "Surjections(S,T)" for S T, intro!]

lemma surjectiveIsBool [intro!,simp]:
  "isBool(Surjective(f,A))"
by (simp add: Surjective_def)

lemma boolifySurjective [simp]:
  "boolify(Surjective(f,A)) = Surjective(f,A)"
by auto

lemma surjectiveI:
  assumes "\<And>y. y \<in> A \<Longrightarrow> \<exists>x \<in> DOMAIN f : y = f[x]"
  shows "Surjective(f,A)"
unfolding Surjective_def by (blast intro: rangeI[OF assms])

lemma surjectiveD:
  assumes "Surjective(f,A)" and "y \<in> A"
  shows "\<exists>x \<in> DOMAIN f : y = f[x]"
using assms by (auto simp: Surjective_def Image_def)

text \<open>
  @{text "\<lbrakk> Surjective(f,A); y \<in> A; \<And>x. \<lbrakk> x \<in> DOMAIN f; y = f[x] \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"}
\<close>
lemmas surjectiveE = surjectiveD[THEN bExE]

lemma surjectiveRange:
  shows "Surjective(f, Range(f))"
by (simp add: Surjective_def)

lemma surjectiveSubset:
  assumes "Surjective(f,A)" and "B \<subseteq> A"
  shows "Surjective(f,B)"
using assms by (auto simp: Surjective_def)

lemma surjectionsI:
  assumes "f \<in> [S \<rightarrow> T]" and "\<And>y. y \<in> T \<Longrightarrow> \<exists>x \<in> S : y = f[x]"
  shows "f \<in> Surjections(S,T)"
using assms by (unfold Surjections_def, auto intro!: surjectiveI)

lemma surjectionsFuncSet:
  assumes "f \<in> Surjections(S,T)"
  shows "f \<in> [S \<rightarrow> T]"
using assms by (simp add: Surjections_def)

lemma surjectionsSurjective:
  assumes 1: "f \<in> Surjections(S,T)" and 2: "y \<in> T"
  shows "\<exists>x \<in> S : y = f[x]"
proof -
  from 1 have "Surjective(f,T)" by (simp add: Surjections_def)
  from this 2 have "\<exists>x \<in> DOMAIN f : y = f[x]" by (rule surjectiveD)
  with 1 funcSetDomain show ?thesis by (auto simp: Surjections_def)
qed

lemma surjectionsE:
  assumes 1: "f \<in> Surjections(S,T)"
  and 2: "\<lbrakk> f \<in> [S \<rightarrow> T]; \<forall>y\<in>T : \<exists>x \<in> S : y = f[x] \<rbrakk> \<Longrightarrow> P"
  shows "P"
using 1 surjectionsFuncSet surjectionsSurjective by (intro 2, auto)

lemma surjectionsRange:
  assumes "f \<in> Surjections(S,T)"
  shows "Range(f) = T"
using assms by (rule surjectionsE, auto)


subsubsection \<open> Bijective functions \<close>

text \<open>
  Here we do not define a predicate @{text Bijective} because it
  would require a set parameter for the codomain and would therefore be
  curiously asymmetrical.
\<close>

definition Bijections
where "Bijections(S,T) \<equiv> Injections(S,T) \<inter> Surjections(S,T)"

lemmas
  setEqualI [where A = "Bijections(S,T)" for S T, intro!]
  setEqualI [where B = "Bijections(S,T)" for S T, intro!]

lemma bijectionsI [intro!]:
  assumes "f \<in> [S \<rightarrow> T]" and "Injective(f)" and "Surjective(f,T)"
  shows "f \<in> Bijections(S,T)"
using assms by (simp add: Bijections_def Injections_def Surjections_def)

lemma bijectionsInjections:
  assumes "f \<in> Bijections(S,T)"
  shows "f \<in> Injections(S,T)"
using assms by (simp add: Bijections_def)

lemma bijectionsSurjections:
  assumes "f \<in> Bijections(S,T)"
  shows "f \<in> Surjections(S,T)"
using assms by (simp add: Bijections_def)

lemma bijectionsE:
  assumes 1: "f \<in> Bijections(S,T)"
  and 2: "\<lbrakk> f \<in> [S \<rightarrow> T]; Injective(f); Surjective(f,T) \<rbrakk> \<Longrightarrow> P"
  shows "P"
using 1 by (intro 2, auto simp: Bijections_def Injections_def Surjections_def)


subsubsection \<open> Inverse of a function \<close>

definition Inverse
where "Inverse(f) \<equiv> [ y \<in> Range(f) \<mapsto> CHOOSE x \<in> DOMAIN f : f[x] = y ]"

(** TODO: add a rule for proving g = Inverse(f) ?? *)

lemma inverseIsAFcn [simp,intro!]:
  "isAFcn(Inverse(f))"
by (simp add: Inverse_def)

lemma inverseDomain [simp]:
  "DOMAIN Inverse(f) = Range(f)"
by (simp add: Inverse_def)

lemma inverseFcnSet:
  "Inverse(f) \<in> [Range(f) \<rightarrow> DOMAIN f]"
proof
  show "\<forall>x \<in> Range(f) : Inverse(f)[x] \<in> DOMAIN f"
  proof
    fix y
    assume y: "y \<in> Range(f)"
    then obtain x where "x \<in> DOMAIN f" and "f[x] = y" by auto
    hence "(CHOOSE x \<in> DOMAIN f : f[x] = y) \<in> DOMAIN f" by (rule bChooseInSet)
    with y show "Inverse(f)[y] \<in> DOMAIN f" by (simp add: Inverse_def)
  qed
qed (auto)

lemma inverseInDomain:
  assumes "y \<in> Range(f)"
  shows "Inverse(f)[y] \<in> DOMAIN f"
using inverseFcnSet assms by (rule funcSetValue)

lemma Inverse:
  assumes y: "y \<in> Range(f)"
  shows "f[ Inverse(f)[y] ] = y"
proof -
  from y obtain x where "x \<in> DOMAIN f" and "f[x] = y" by auto
  hence "f[CHOOSE x \<in> DOMAIN f: f[x]=y] = y" by (rule bChooseI)
  with y show ?thesis by (simp add: Inverse_def)
qed

lemma inverseInjective [simp,intro]:
  "Injective(Inverse(f))"
proof (intro injectiveOnI, auto)
  fix x x'
  assume x: "x \<in> DOMAIN f" and x': "x' \<in> DOMAIN f"
     and eq: "Inverse(f)[ f[x] ] = Inverse(f)[ f[x'] ]" (is "?invx = ?invx'")
  from x have "f[x] = f[?invx]" by (intro sym[OF Inverse], auto)
  moreover
  from x' have "f[?invx'] = f[x']" by (intro Inverse, auto)
  moreover
  note eq
  ultimately show "f[x] = f[x']" by simp
qed

text \<open>
  For injective functions, @{text Inverse} really inverts the function.
\<close>

lemma injectiveInverse:
  assumes f: "Injective(f)" and x: "x \<in> DOMAIN f"
  shows "Inverse(f)[ f[x] ] = x"
proof -
  from x have "f[x] \<in> Range(f)" by auto
  hence "Inverse(f)[f[x]] = (CHOOSE z \<in> DOMAIN f : f[z] = f[x])" by (simp add: Inverse_def)
  moreover
  have "\<dots> = x"
  proof (rule bChooseI2)
    from x show "\<exists>z \<in> DOMAIN f : f[z] = f[x]" by blast
  next
    fix z
    assume "z \<in> DOMAIN f" and "f[z] = f[x]"
    with f x show "z = x" by (auto elim: injectiveOnD)
  qed
  ultimately
  show ?thesis by simp
qed

lemma injectiveIffExistsInverse:
  "Injective(f) = (\<exists>g : \<forall>x \<in> DOMAIN f : g[f[x]] = x)"
by (auto intro: inverseThenInjective dest: injectiveInverse)

lemma inverseOfInjectiveSurjective:
  assumes f: "Injective(f)"
  shows "Surjective(Inverse(f), DOMAIN f)"
proof (rule surjectiveI)
  fix x
  assume x: "x \<in> DOMAIN f"
  with f have "x = Inverse(f)[f[x]]" by (rule sym[OF injectiveInverse])
  with x show "\<exists>y \<in> DOMAIN Inverse(f) : x = Inverse(f)[y]" by auto
qed

text \<open> The inverse of a bijection is a bijection. \<close>

lemma inverseBijections:
  assumes f: "f \<in> Bijections(S,T)"
  shows "Inverse(f) \<in> Bijections(T,S)"
proof
  from f have "f \<in> Surjections(S,T)" by (simp add: Bijections_def)
  hence rng: "Range(f) = T" by (rule surjectionsRange)
  from f have dom: "DOMAIN f = S" by (auto elim: bijectionsE)
  from dom rng inverseFcnSet show "Inverse(f) \<in> [T \<rightarrow> S]" by auto
next
  from f have "Injective(f)" by (auto elim: bijectionsE)
  hence "Surjective(Inverse(f), DOMAIN f)" by (rule inverseOfInjectiveSurjective)
  with f show "Surjective(Inverse(f),S)" by (auto elim: bijectionsE)
qed (rule inverseInjective)


end
