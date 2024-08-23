(*  Title:      TLA+/SetTheory.thy
    Author:     Stephan Merz, Inria Nancy
    Copyright (C) 2008-2024  INRIA and Microsoft Corporation
    License:    BSD
    Version:    Isabelle2024
*)

section \<open>\tlaplus{} Set Theory\<close>

theory SetTheory
imports PredicateLogic
begin

text \<open>
  This theory defines the version of Zermelo-Fraenkel set theory
  that underlies \tlaplus{}.
\<close>

subsection \<open>Basic syntax and axiomatic basis of set theory\<close>

text \<open>
  The following constants are at the basis of our set theory.
\<close>

consts
  "in"      ::  "[c, c] \<Rightarrow> c" (infixl "\<in>" 50)   (* set membership *)
  emptyset  ::  "c"        ("{}" 100)      (* empty set *)
  SUBSET    ::  "c \<Rightarrow> c"   ("SUBSET _" [100]90) (* power set *)
  UNION     ::  "c \<Rightarrow> c"   ("UNION _" [100]90)  (* generalized union *)
  subsetOf  ::  "[c, c \<Rightarrow> c] \<Rightarrow> c"    (* subsetOf(S,p) = {x \in S : p} *)
  setOfAll  ::  "[c, c \<Rightarrow> c] \<Rightarrow> c"    (* setOfAll(S,e) = {e : x \in S} *)
  infinity  ::  "c"                   (* infinity set *)

notation (ASCII)
  "in"         (infixl "\\in" 50)

text \<open>Negated set membership\<close>

abbreviation "notin(a, S) \<equiv> \<not>(a \<in> S)"

notation
  "notin"      (infixl "\<notin>" 50)
notation (ASCII)
  "notin"      (infixl "\\notin" 50)

text \<open>
  We introduce some more notation and operators before stating the
  axioms of set theory, in order to make them more readable.
\<close>


text \<open> Concrete syntax: set comprehension \<close>

(***
  We cannot yet allow multiple bindings as in {f(x,y) : x \<in> S, y \<in> T}
  because logical constants (such as setOfAll) must have fixed arity.
  Multiple bindings will be introduced as shorthands involving tuples
  when tuples are available -- fortunately we don't need them earlier!

  Note that the expression "{x \<in> S : y \<in> T}" is ambiguous
  (as mentioned in the TLA+ book). In such cases, use logical syntax, e.g.
  subsetOf(S, \<lambda>x. y \<in> T). See the definition cap_def below.
***)
syntax
  "@setOfAll" :: "[c, idt, c] \<Rightarrow> c"         ("(1{_ : _ \<in> _})")
  "@subsetOf" :: "[idt, c, c] \<Rightarrow> c"         ("(1{_ \<in> _ : _})")
syntax (ASCII)
  "@setOfAll" :: "[c, idt, c] \<Rightarrow> c"         ("(1{_ : _ \\in _})")
  "@subsetOf" :: "[idt, c, c] \<Rightarrow> c"         ("(1{_ \\in _ : _})")
translations
  "{e : x \<in> S}"  \<rightleftharpoons>  "CONST setOfAll(S, \<lambda>x. e)"
  "{x \<in> S : P}"  \<rightleftharpoons>  "CONST subsetOf(S, \<lambda>x. P)"

text \<open>Unordered pairs\<close>

definition upair :: "[c, c] \<Rightarrow> c"
  where "upair(a,b)  \<equiv>  { IF x={} THEN a ELSE b : x \<in> SUBSET (SUBSET {}) }"

text \<open>Binary set union\<close>

definition union :: "[c, c] \<Rightarrow> c" (infixl "\<union>" 65)
  where "A \<union> B \<equiv> UNION upair(A,B)"

notation (ASCII)
  union      (infixl "\\union" 65)

definition addElt :: "[c, c] \<Rightarrow> c"
  where "addElt(a, A)  \<equiv>  upair(a,a) \<union> A"

text \<open> Concrete syntax: set enumerations \<close>

nonterminal cs

syntax
  ""         ::  "c \<Rightarrow> cs"          ("_")
  "@cs"      ::  "[c, cs] \<Rightarrow> cs"    ("_,/ _")
  "@enumset" ::  "cs \<Rightarrow> c"          ("{(_)}")

translations
  "{x, xs}" \<rightleftharpoons>  "CONST addElt(x, {xs})"
  "{x}"     \<rightleftharpoons>  "CONST addElt(x, {})"

abbreviation BOOLEAN :: "c" where
  "BOOLEAN \<equiv> {TRUE, FALSE}"

text \<open>Bounded quantification\<close>

definition bChoose :: "[c, c \<Rightarrow> c] \<Rightarrow> c"
  where "bChoose(A,P)  \<equiv>  CHOOSE x : x \<in> A \<and> P(x)"

definition bEx :: "[c, c \<Rightarrow> c] \<Rightarrow> c"
  where "bEx(A, P)  \<equiv>  \<exists>x : x \<in> A \<and> P(x)"

definition bAll :: "[c, c \<Rightarrow> c] \<Rightarrow> c"
  where "bAll(A, P) \<equiv>  \<forall>x : x \<in> A \<Rightarrow> P(x)"

text \<open> Concrete syntax: bounded quantification \<close>

(*** FIXME: allow multiple bindings as in "ALL x:S, y:T. P(x,y)".
  The following was a valiant attempt to define appropriate syntax
  translations, but for some reason the first translation rule below
  is not accepted -- do we need to program a parse translation?

nonterminal sbinds

syntax
  "@sbind"    ::  "[idt,c] \<Rightarrow> sbinds"         ("_ \\in _" [100, 10] 100)
  "@sbinds"   ::  "[idt,c,sbinds] \<Rightarrow> sbinds"   ("_ \\in _,/ _" [100, 10, 100] 100)
syntax (xsymbols)
  "@sbind"    ::  "[idt,c] \<Rightarrow> sbinds"         ("_ \<in> _"  [100, 10] 100)
  "@sbinds"   ::  "[idt,c, sbinds] \<Rightarrow> sbinds"  ("_ \<in> _,/ _" [100, 10, 100] 100)

syntax
  "@bChoice" ::  "[sbinds, c] \<Rightarrow> c"          ("(3CHOOSE _ :/ _)" 10)
  "@bEx"     ::  "[sbinds, c] \<Rightarrow> c"          ("(3\\E _ :/ _)" [100, 10] 10)
  "@bAll"    ::  "[sbinds, c] \<Rightarrow> c"          ("(3\\A _ :/ _)" [100, 10] 10)
syntax (xsymbols)
  "@bEx"     ::  "[sbinds, c] \<Rightarrow> c"          ("(3\<exists>_ :/ _)" [100,10] 10)
  "@bAll"    ::  "[sbinds, c] \<Rightarrow> c"          ("(3\<forall>_ :/ _)" [100,10] 10)

translations
  "\<forall>x \<in> S, bds : P"  \<rightleftharpoons>  "CONST bAll(S, \<lambda>x. \<forall>bds : P)"
  "\<forall>x \<in> S : P"       \<rightleftharpoons>  "CONST bAll(S, \<lambda>x. P)"
***)

(*** TEMPORARY FIX:
  concrete syntax for bounded quantification, only single binding allowed
  (but possibly multiple variables in input)
***)

syntax
  "@bChoice" ::  "[idt, c, c] \<Rightarrow> c"       ("(3CHOOSE _ \<in> _ :/ _)" [100,0,0]10)
  "@bEx"     ::  "[cidts, c, c] \<Rightarrow> c"     ("(3\<exists>_ \<in> _ :/ _)" [100,0,0] 10)
  "@bAll"    ::  "[cidts, c, c] \<Rightarrow> c"     ("(3\<forall>_ \<in> _ :/ _)" [100,0,0] 10)
syntax (ASCII)
  (* Again, only single variable for bounded choice. *)
  "@bChoice" ::  "[idt, c, c] \<Rightarrow> c"       ("(3CHOOSE _ in _ :/ _)" [100,0,0] 10)
  "@bEx"     ::  "[cidts, c, c] \<Rightarrow> c"     ("(3\\E _ \\in _ :/ _)" [100,0,0] 10)
  "@bAll"    ::  "[cidts, c, c] \<Rightarrow> c"     ("(3\\A _ \\in _ :/ _)" [100,0,0] 10)
translations
  "CHOOSE x \<in> S : P"      \<rightleftharpoons>  "CONST bChoose(S, \<lambda>x. P)"
  (* the following cannot be a print macro because the RHS is non-linear
     -- need a print translation for display *)
  "\<exists>x, xs \<in> S : P"        \<rightharpoonup>  "CONST bEx(S, \<lambda>x. \<exists>xs \<in> S : P)"
  "\<exists>x \<in> S : P"            \<rightharpoonup>  "CONST bEx(S, \<lambda>x. P)"
  "\<forall>x, xs \<in> S : P"        \<rightharpoonup>  "CONST bAll(S, \<lambda>x. \<forall>xs \<in> S : P)"
  "\<forall>x \<in> S : P"            \<rightharpoonup>  "CONST bAll(S, \<lambda>x. P)"

print_translation \<open>
  let
      fun bEx_tr' [S, Abs(x, T, P as (Const (@{const_syntax "bEx"},_) $ S' $ Q))] =
          (* bEx(S, bEx(S', Q)) => \\E x,y \\in S : Q if S = S' *)
          let val (y,Q') = Syntax_Trans.atomic_abs_tr' (x,T,Q)
              val (_ $ xs $ set $ Q'') = bEx_tr' [S', Q']
	  in  if S = S'
	      then Syntax.const "@bEx" $ (Syntax.const "@cidts" $ y $ xs)
				       $ set $ Q''
	      else Syntax.const "@bEx" $ y $ S $
		       (Syntax.const "@bEx" $ xs $ set $ Q'')
	  end
	| bEx_tr' [S, Abs(x, T, P)] =
	    let val (x',P') = Syntax_Trans.atomic_abs_tr' (x,T,P)
	    in  (Syntax.const "@bEx") $ x' $ S $ P'
	    end
	| bEx_tr' _ = raise Match;
      fun bAll_tr' [S, Abs(x, T, P as (Const (@{const_syntax "bAll"},_) $ S' $ Q))] =
          (* bAll(S, bAll(S', Q)) => \\A x,y \\in S : Q if S = S' *)
          let val (y,Q') = Syntax_Trans.atomic_abs_tr' (x,T,Q)
              val (_ $ xs $ set $ Q'') = bAll_tr' [S', Q']
	  in  if S = S'
	      then Syntax.const "@bAll" $ (Syntax.const "@cidts" $ y $ xs)
				        $ set $ Q''
	      else Syntax.const "@bAll" $ y $ S $
		       (Syntax.const "@bAll" $ xs $ set $ Q'')
	  end
	| bAll_tr' [S, Abs(x, T, P)] =
	    let val (x',P') = Syntax_Trans.atomic_abs_tr' (x,T,P)
	    in  (Syntax.const "@bAll") $ x' $ S $ P'
	    end
	| bAll_tr' _ = raise Match;
  in  [(@{const_syntax "bEx"}, (fn _ => bEx_tr')),
       (@{const_syntax "bAll"}, (fn _ => bAll_tr'))]
  end
\<close>

(*** TEST DATA for parse and print translations ***
lemma "\<exists>x,y,z \<in> S : x = y \<or> y = z"
oops

lemma "\<forall>x,y,z \<in> S : x = y \<Rightarrow> y = z"
oops

lemma "\<forall>x,y \<in> S : \<exists>u,v \<in> T : x=u \<or> y=v"
oops

lemma "\<exists>x,y \<in> S : \<exists>z \<in> T : x = y \<and> y = z"
oops

lemma "\<forall>x,y \<in> S : \<forall>z \<in> T : x=y \<and> y \<noteq> z"
oops
*** END TEST DATA ***)

text \<open>
  We now state the axioms of set theory: extensionality
  and the definitions of @{text UNION}, @{text SUBSET}, and @{text setOfAll}.
  Membership is also asserted to be produce Boolean values---in traditional
  presentations of ZF set theory this is ensured by distinguishing sorts of
  terms and formulas. @{term infinity} is some infinite set, but it is not
  uniquely defined. The foundation axiom rules out sets that are ``too big''.
\<close>
axiomatization where
  inIsBool [intro!,simp]: "isBool(x \<in> A)"
and
  extension:    "(A = B) \<Leftrightarrow> (\<forall>x : x \<in> A \<Leftrightarrow> x \<in> B)"
and
  UNION:        "(A \<in> UNION S) \<Leftrightarrow> (\<exists>B \<in> S : A \<in> B)"
and
  SUBSET:       "(A \<in> SUBSET S) \<Leftrightarrow> (\<forall>x \<in> A : x \<in> S)"
and
  setOfAll:     "(y \<in> setOfAll(S, e)) \<Leftrightarrow> (\<exists>x : x \<in> S \<and> y = e(x))"
and
  subsetOf:     "(y \<in> subsetOf(S, P)) \<Leftrightarrow> (y \<in> S \<and> P(y))"
and
  infinity:     "({} \<in> infinity) \<and> (\<forall>x \<in> infinity : {x} \<union> x \<in> infinity)"
and
  foundation:   "(A = {}) \<or> (\<exists>x \<in> A : \<forall>y \<in> x : y \<notin> A)"


text \<open>More set operations\<close>

definition subset :: "[c, c] \<Rightarrow> c" (infixl "\<subseteq>" 50)
  where "A \<subseteq> B \<equiv> \<forall>x \<in> A : x \<in> B"

definition inter ::  "[c, c] \<Rightarrow> c" (infixl "\<inter>" 70)  (* binary intersection *)
  where "A \<inter> B \<equiv>  subsetOf(A, \<lambda>x. x \<in> B)"

definition setminus ::  "[c, c] \<Rightarrow> c" (infixl "\<setminus>" 65)     (* set difference *)
  where "A \<setminus> B \<equiv> {x \<in> A : x \<notin> B}"

definition INTER ::  "c \<Rightarrow> c"   ("INTER _" [100]90)  (* generalized intersection *)
  where "INTER A \<equiv> { x \<in> UNION A : \<forall>B \<in> A : x \<in> B }"

text \<open>Note that @{text "INTER {}"} is @{text "{}"}.\<close>

notation (ASCII)
  "inter"      (infixl "\\inter" 70)  and
  "setminus"   (infixl "\\" 65)  and
  "subset"     (infixl "\\subseteq" 50)

abbreviation (input) "supset(S, T) \<equiv> T \<subseteq> S"
notation
  "supset"    (infixl "\<supseteq>" 50)
notation (ASCII)
  "supset"    (infixl "\\supseteq" 50)

definition "psubset" :: "[c, c] \<Rightarrow> c" (infixl "\<subset>" 50)
where "S \<subset> T \<equiv> S \<subseteq> T \<and> S \<noteq> T"

notation (ASCII)
  "psubset"   (infixl "\\subset" 50)

abbreviation (input) "psupset(S,T) \<equiv> T \<subset> S"
notation
  "psupset"  (infix "\<supset>" 50)
notation (ASCII)
  "psupset"  (infix "\\supset" 50)

lemma psubset_intro [intro!]:
  "\<lbrakk> S \<subseteq> T ; S \<noteq> T \<rbrakk> \<Longrightarrow> S \<subset> T"
unfolding psubset_def by safe

lemma psubset_elim [elim!]:
  "\<lbrakk> S \<subset> T ; \<lbrakk> S \<subseteq> T ; S \<noteq> T \<rbrakk> \<Longrightarrow> C \<rbrakk> \<Longrightarrow> C"
unfolding psubset_def by safe


subsection \<open> Boolean operators \<close>

text \<open>
  The following lemmas assert that certain operators always return
  Boolean values; these are helpful for the automated reasoning methods.
\<close>

lemma boolifyIn [simp]: "boolify(x \<in> A) = (x \<in> A)"
by (rule inIsBool[unfolded isBool_def])

lemma notIn_inFalse: "a \<notin> A \<Longrightarrow> (a \<in> A) = FALSE"
by auto

lemma boolifyBAll [simp]: "boolify(\<forall>x\<in>A : P(x)) = (\<forall>x\<in>A : P(x))"
by (simp add: bAll_def)

lemma bAllIsBool [intro!,simp]: "isBool(\<forall>x\<in>A : P(x))"
by (unfold isBool_def, rule boolifyBAll)

lemma boolifyBEx [simp]: "boolify(\<exists>x\<in>A : P(x)) = (\<exists>x\<in>A : P(x))"
by (simp add: bEx_def)

lemma bExIsBool [intro!,simp]: "isBool(\<exists>x\<in>A : P(x))"
by (unfold isBool_def, rule boolifyBEx)

lemma boolifySubset [simp]: "boolify(A \<subseteq> B) = (A \<subseteq> B)"
by (simp add: subset_def)

lemma subsetIsBool [intro!,simp]: "isBool(A \<subseteq> B)"
by (unfold isBool_def, rule boolifySubset)

lemma boolifypSubset [simp]: "boolify(A \<subset> B) = (A \<subset> B)"
by (simp add: psubset_def)

lemma psubsetIsBool [intro!,simp]: "isBool(A \<subset> B)"
by (unfold isBool_def, rule boolifypSubset)

lemma [intro!]:
  "\<lbrakk>isBool(P); x\<in>S \<Leftrightarrow> P\<rbrakk> \<Longrightarrow> (x\<in>S) = P"
  "\<lbrakk>isBool(P); P \<Leftrightarrow> x\<in>S\<rbrakk> \<Longrightarrow> P = (x\<in>S)"
  "\<lbrakk>isBool(P); bAll(S,A) \<Leftrightarrow> P\<rbrakk> \<Longrightarrow> bAll(S,A) = P"
  "\<lbrakk>isBool(P); P \<Leftrightarrow> bAll(S,A)\<rbrakk> \<Longrightarrow> P = bAll(S,A)"
  "\<lbrakk>isBool(P); bEx(S,A) \<Leftrightarrow> P\<rbrakk> \<Longrightarrow> bEx(S,A) = P"
  "\<lbrakk>isBool(P); P \<Leftrightarrow> bEx(S,A)\<rbrakk> \<Longrightarrow> P = bEx(S,A)"
  "\<lbrakk>isBool(P); S \<subseteq> T \<Leftrightarrow> P\<rbrakk> \<Longrightarrow> (S \<subseteq> T) = P"
  "\<lbrakk>isBool(P); P \<Leftrightarrow> S \<subseteq> T\<rbrakk> \<Longrightarrow> P = (S \<subseteq> T)"
by auto


subsection \<open> Substitution rules \<close>

lemma subst_elem [trans]:
  assumes "b \<in> A" and "a=b"
  shows "a \<in> A"
using assms by simp

lemma subst_elem_rev [trans]:
  assumes "a=b" and "b \<in> A"
  shows "a \<in> A"
using assms by simp

lemma subst_set [trans]:
  assumes "a \<in> B" and "A=B"
  shows "a \<in> A"
using assms by simp

lemma subst_set_rev [trans]:
  assumes "A=B" and "a \<in> B"
  shows "a \<in> A"
using assms by simp


subsection \<open> Bounded quantification \<close>

lemma bAllI [intro!]:
  assumes "\<And>x. x \<in> A \<Longrightarrow> P(x)"
  shows "\<forall>x\<in>A : P(x)"
using assms unfolding bAll_def by blast

lemma bspec:
  assumes "\<forall>x\<in>A : P(x)" and "x \<in> A"
  shows "P(x)"
using assms unfolding bAll_def by blast

setup \<open>
  map_theory_claset (fn ctxt =>
    ctxt addbefore ("bspec", fn ctxt' => dresolve_tac ctxt' @{thms bspec} THEN' assume_tac ctxt'))
\<close>

(**
text \<open>The following rule intentionally has single assumption (non-conditional),
because otherwise it interferes with how \<open>Nat\<close> is reduced to \<open>Int\<close>.\<close>
lemma bspec' [dest]:
  assumes "\<forall>x\<in>A : P(x)"
  shows "\<forall>x : (x\<in>A) \<Rightarrow> P(x)"
  using assms unfolding bAll_def by blast
**)

lemma bAll_unb [simp] : "\<And>T P. (\<forall>e : e \<in> T \<Rightarrow> P(e)) \<Longrightarrow> (\<forall>e \<in> T : P(e))"
  using bAll_def by simp

lemma bAllE [elim]:
  assumes "\<forall>x\<in>A : P(x)" and "x \<notin> A \<Longrightarrow> Q" and "P(x) \<Longrightarrow> Q"
  shows "Q"
using assms unfolding bAll_def by blast

lemma bAllTriv [simp]: "(\<forall>x\<in>A : P) = ((\<exists>x : x \<in> A) \<Rightarrow> P)"
unfolding bAll_def by blast

lemma bAllCong [cong]:
  assumes "A=B" and "\<And>x. x \<in> B \<Longrightarrow> P(x) \<Leftrightarrow> Q(x)"
  shows "(\<forall>x\<in>A : P(x)) = (\<forall>x\<in>B : Q(x))"
using assms by (auto simp: bAll_def)

lemma bExI [intro]:
  assumes "x \<in> A" and "P(x)"
  shows "\<exists>x\<in>A : P(x)"
using assms unfolding bEx_def by blast

lemma bExCI:  (* proof by contradiction *)
  assumes "(\<forall>x\<in>A : \<not>P(x)) \<Longrightarrow> P(a)" and "a \<in> A"
  shows "\<exists>x\<in>A : P(x)"
using assms by blast

lemma bExE [elim!]:
  assumes "\<exists>x\<in>A : P(x)" and "\<And>x. \<lbrakk> x \<in> A; P(x) \<rbrakk> \<Longrightarrow> Q"
  shows "Q"
using assms unfolding bEx_def by blast

lemma bExTriv [simp]: "(\<exists>x\<in>A : P) = ((\<exists>x : x \<in> A) \<and> P)"
unfolding bEx_def by simp

lemma bExCong [cong]:
  assumes "A=B" and "\<And>x. x \<in> B \<Longrightarrow> P(x) \<Leftrightarrow> Q(x)"
  shows "(\<exists>x\<in>A : P(x)) = (\<exists>x\<in>B : Q(x))"
using assms unfolding bEx_def by force

lemma bChooseI:
  assumes 1: "t \<in> A" and 2: "P(t)"
  shows "P(CHOOSE x \<in> A : P(x))"
proof -
  let ?ch = "CHOOSE x \<in> A : P(x)"
  from 1 2 have "t \<in> A \<and> P(t)" ..
  hence "?ch \<in> A \<and> P(?ch)"
    by (unfold bChoose_def, rule chooseI)
  thus ?thesis ..
qed

lemma bChooseInSet:
  assumes 1: "t \<in> A" and 2: "P(t)"
  shows "(CHOOSE x \<in> A : P(x)) \<in> A"
proof -
  let ?ch = "CHOOSE x \<in> A : P(x)"
  from 1 2 have "t \<in> A \<and> P(t)" ..
  hence "?ch \<in> A \<and> P(?ch)"
    by (unfold bChoose_def, rule chooseI)
  thus ?thesis ..
qed

lemma bChooseI_ex:
  assumes hyp: "\<exists>x\<in>A : P(x)"
  shows "P(CHOOSE x\<in>A : P(x))"
proof -
  from hyp obtain x where "x \<in> A" and "P(x)" by auto
  thus ?thesis by (rule bChooseI)
qed

lemma bChooseInSet_ex:
  assumes hyp: "\<exists>x\<in>A : P(x)"
  shows "(CHOOSE x\<in>A : P(x)) \<in> A"
proof -
  from hyp obtain x where "x \<in> A" and "P(x)" by auto
  thus ?thesis by (rule bChooseInSet)
qed

lemma bChooseI2:
  assumes 1: "\<exists>x\<in>A : P(x)" and 2: "\<And>x. \<lbrakk>x \<in> A; P(x)\<rbrakk> \<Longrightarrow> Q(x)"
  shows "Q(CHOOSE x\<in>A : P(x))"
proof (rule 2)
  from 1 show "(CHOOSE x\<in>A : P(x)) \<in> A" by (rule bChooseInSet_ex)
next
  from 1 show "P(CHOOSE x\<in>A : P(x))" by (rule bChooseI_ex)
qed

lemma bChooseCong [cong]:
  assumes "A=B" and "\<And>x. x \<in> B \<Longrightarrow> P(x) \<Leftrightarrow> Q(x)"
  shows "(CHOOSE x\<in>A : P(x)) = (CHOOSE x\<in>B : Q(x))"
unfolding bChoose_def proof (rule choose_det)
  fix x
  from assms show "x \<in> A \<and> P(x) \<Leftrightarrow> x \<in> B \<and> Q(x)" by blast
qed

(*** currently inactive -- causes several obscure warnings about renamed
     variables and seems to slow down large examples such as AtomicBakery ***
ML \<open>
  structure Simpdata =
  struct

    open Simpdata;

    val mksimps_pairs = [(@{const_name bAll}, (@{thms bspec}, false))] @ mksimps_pairs;

  end;

  open Simpdata;
\<close>

declaration \<open>
  fn _ => Simplifier.map_ss (fn ss => ss
    |> Simplifier.set_mksimps (fn ctxt =>
        Simpdata.mksimps Simpdata.mksimps_pairs ctxt))
\<close>
***)

(***
  TYPE CHECKING CURRENTLY NOT INSTALLED

  The solver installed by the type checking package breaks some proofs
  and makes the auto tactic loop for unfathomable reasons. Type checking
  itself works, but is not used anywhere.

  TODO: investigate the issue and find out what is really needed about
  type checking.

subsubsection \<open> Setting up type checking for \tlaplus{}. \<close>

text \<open>
  Type checking is intended to solve simple goals, for example showing
  that conjunctions are Boolean, and that the result of a conditional
  expression is a natural number if both branches yield naturals. Unlike
  simplification (Isabelle's rewriting machinery), type checking may
  instantiate unknowns. It is used as a ``solver'' of the simplifier,
  in particular for proving hypotheses of conditional rewrite rules,
  and due to this, proofs by simplification may actually instantiate
  unknowns.

  The code is essentially taken from Isabelle/ZF.
\<close>

use "typecheck.ML"
setup TypeCheck.setup

declare
  trueIsBool [TC]     falseIsBool [TC]    boolifyIsBool [TC]
  eqIsBool [TC]       isBoolCond [TC]     notIsBool [TC]
  andIsBool [TC]      orIsBool [TC]       impIsBool [TC]
  iffIsBool [TC]      exIsBool [TC]       allIsBool [TC]
  inIsBool [TC]       bAllIsBool [TC]     bExIsBool [TC]
  subsetIsBool [TC]

*** TEST DATA ***

lemma "isBool (A \<and> B)"
by typecheck

lemma "isBool (IF P THEN x=y ELSE g(a) \<in> UNION S)"
by typecheck

*** END TEST DATA ***

***)


subsection \<open> Simplification of conditional expressions \<close>

lemma inCond [simp]: "(a \<in> (IF P THEN S ELSE T)) = ((P \<and> a \<in> S) \<or> (\<not>P \<and> a \<in> T))"
by (force intro: condI elim: condE)

lemma condIn [simp]: "((IF P THEN a ELSE b) \<in> S) = ((P \<and> a \<in> S) \<or> (\<not>P \<and> b \<in> S))"
by (force intro: condI elim: condE)

lemma inCondI (*[TC]*):
  (* adding this as (unsafe) introduction rule cripples blast & co -- why? *)
  assumes "P \<Longrightarrow> c \<in> A" and "\<not>P \<Longrightarrow> c \<in> B"
  shows "c \<in> (IF P THEN A ELSE B)"
using assms by auto

lemma condInI (*[TC]*):
  (* too general to add as introduction rule? *)
  assumes "P \<Longrightarrow> a \<in> S" and "\<not>P \<Longrightarrow> b \<in> S"
  shows "(IF P THEN a ELSE b) \<in> S"
using assms by auto

lemma inCondE: (* too general to add as elimination rule? *)
  assumes "c \<in> (IF P THEN A ELSE B)"
  and "\<lbrakk> P; c \<in> A \<rbrakk> \<Longrightarrow> Q" and "\<lbrakk> \<not>P; c \<in> B \<rbrakk> \<Longrightarrow> Q"
  shows "Q"
using assms by auto

lemma condInE: (* too general to add as elimination rule? *)
  assumes "(IF P THEN a ELSE b) \<in> S"
  and "\<lbrakk> P; a \<in> S \<rbrakk> \<Longrightarrow> Q" and "\<lbrakk> \<not>P; b \<in> S \<rbrakk> \<Longrightarrow> Q"
  shows "Q"
using assms by auto

lemma subsetCond [simp]:
  "(A \<subseteq> (IF P THEN S ELSE T)) = ((P \<and> A \<subseteq> S) \<or> (\<not>P \<and> A \<subseteq> T))"
by (blast intro: condI elim: condE)

lemma condSubset [simp]:
  "((IF P THEN A ELSE B) \<subseteq> S) = ((P \<and> A \<subseteq> S) \<or> (\<not>P \<and> B \<subseteq> S))"
by (force intro: condI elim: condE)

(** introduction and elimination rules omitted -- should be subsumed by standard
    rules for subset plus the rules for membership and conditionals above
**)


subsection \<open> Rules for subsets and set equality \<close>

lemma subsetI [intro!]:
  assumes "\<And>x. x \<in> A \<Longrightarrow> x \<in> B"
  shows "A \<subseteq> B"
using assms by (auto simp: subset_def)

lemma subsetD [elim,trans]:
  assumes "A \<subseteq> B" and "c \<in> A"
  shows "c \<in> B"
using assms by (auto simp: subset_def)

lemma rev_subsetD [trans]:
  "\<lbrakk> c \<in> A; A \<subseteq> B \<rbrakk> \<Longrightarrow> c \<in> B"
by (rule subsetD)

lemma subsetCE [elim]:
  assumes "A \<subseteq> B" and "c \<notin> A \<Longrightarrow> P" and "c \<in> B \<Longrightarrow> P"
  shows "P"
using assms unfolding subset_def by blast

lemma subsetE:
  assumes "A \<subseteq> B" and "\<And>x. (x \<in> A \<Longrightarrow> x \<in> B) \<Longrightarrow> P"
  shows "P"
using assms by blast

lemma subsetNotIn:
  assumes "A \<subseteq> B" and "c \<notin> B"
  shows "c \<notin> A"
using assms by blast

lemma rev_subsetNotIn: "\<lbrakk> c \<notin> B; A \<subseteq> B \<rbrakk> \<Longrightarrow> c \<notin> A"
by (rule subsetNotIn)

lemma notSubset: "(\<not>(A \<subseteq> B)) = (\<exists>x \<in> A : x \<notin> B)"
by blast

lemma notSubsetI (*[intro]*):
  assumes "a \<in> A" and "a \<notin> B"
  shows "\<not>(A \<subseteq> B)"
using assms by blast

lemma notSubsetE (*[elim!]*):
  assumes "\<not>(A \<subseteq> B)" and "\<And>x. \<lbrakk> x \<in> A; x \<notin> B \<rbrakk> \<Longrightarrow> P"
  shows "P"
using assms by blast

text \<open> The subset relation is a partial order. \<close>

lemma subsetRefl [simp,intro!]: "A \<subseteq> A"
by blast

lemma subsetTrans [trans]:
  assumes "A \<subseteq> B" and "B \<subseteq> C"
  shows "A \<subseteq> C"
using assms by blast

lemma setEqual:
  assumes "A \<subseteq> B" and "B \<subseteq> A"
  shows "A = B"
using assms by (intro iffD2[OF extension], blast)

lemma setEqualI:
  assumes "\<And>x. x \<in> A \<Longrightarrow> x \<in> B" and "\<And>x. x \<in> B \<Longrightarrow> x \<in> A"
  shows "A = B"
by (rule setEqual, (blast intro: assms)+)

text \<open>
  The rule @{text setEqualI} is too general for use as a default
  introduction rule: we don't want to apply it for Booleans, for
  example. However, instances where at least one term results from
  a set constructor are useful.
\<close>

lemmas
(** the instances for the empty set are superseded by rules below
  setEqualI [where A = "{}", intro!]
  setEqualI [where B = "{}", intro!]
**)
  setEqualI [where A = "addElt(a,C)" for a C, intro!]
  setEqualI [where B = "addElt(a,C)" for a C, intro!]
  setEqualI [where A = "SUBSET C" for C, intro!]
  setEqualI [where B = "SUBSET C" for C, intro!]
  setEqualI [where A = "UNION C" for C, intro!]
  setEqualI [where B = "UNION C" for C, intro!]
  setEqualI [where A = "INTER C" for C, intro!]
  setEqualI [where B = "INTER C" for C, intro!]
  setEqualI [where A = "C \<union> D" for C D, intro!]
  setEqualI [where B = "C \<union> D" for C D, intro!]
  setEqualI [where A = "C \<inter> D" for C D, intro!]
  setEqualI [where B = "C \<inter> D" for C D, intro!]
  setEqualI [where A = "C \<setminus> D" for C D, intro!]
  setEqualI [where B = "C \<setminus> D" for C D, intro!]
  setEqualI [where A = "subsetOf(S,P)" for S P, intro!]
  setEqualI [where B = "subsetOf(S,P)" for S P, intro!]
  setEqualI [where A = "setOfAll(S,e)" for S e, intro!]
  setEqualI [where B = "setOfAll(S,e)" for S e, intro!]

lemma setEqualD1: "A = B \<Longrightarrow> A \<subseteq> B"
  by blast

lemma setEqualD2: "A = B \<Longrightarrow> B \<subseteq> A"
  by blast

lemma setEqualE:
  assumes "A = B"
  and "\<lbrakk> c \<in> A; c \<in> B \<rbrakk> \<Longrightarrow> P" and "\<lbrakk> c \<notin> A; c \<notin> B \<rbrakk> \<Longrightarrow> P"
  shows "P"
using assms by (blast dest: setEqualD1 setEqualD2)

text \<open>
  Again, we add instances of this theorem for obvious set constructors.
\<close>
lemmas
  setEqualE [where A = "{}", elim]
  setEqualE [where B = "{}", elim]
  setEqualE [where A = "addElt(a,C)" for a C, elim]
  setEqualE [where B = "addElt(a,C)" for a C, elim]
  setEqualE [where A = "SUBSET C" for C, elim]
  setEqualE [where B = "SUBSET C" for C, elim]
  setEqualE [where A = "UNION C" for C, elim]
  setEqualE [where B = "UNION C" for C, elim]
  setEqualE [where A = "INTER C" for C, elim]
  setEqualE [where B = "INTER C" for C, elim]
  setEqualE [where A = "C \<union> D" for C D, elim]
  setEqualE [where B = "C \<union> D" for C D, elim]
  setEqualE [where A = "C \<inter> D" for C D, elim]
  setEqualE [where B = "C \<inter> D" for C D, elim]
  setEqualE [where A = "C \<setminus> D" for C D, elim]
  setEqualE [where B = "C \<setminus> D" for C D, elim]
  setEqualE [where A = "subsetOf(S,P)" for S P, elim]
  setEqualE [where B = "subsetOf(S,P)" for S P, elim]
  setEqualE [where A = "setOfAll(S,e)" for S e, elim]
  setEqualE [where B = "setOfAll(S,e)" for S e, elim]

lemma setEqual_iff: "(A = B) = (\<forall>x : x \<in> A \<Leftrightarrow> x \<in> B)"
by (blast intro: setEqualI)


subsection \<open> Set comprehension: @{text setOfAll} and @{text subsetOf} \<close>

(***
lemma setOfAllI:
  assumes "a \<in> S"
  shows "e(a) \<in> { e(x) : x \<in> S }"
using assms by (blast intro: setOfAll[THEN iffD2])
***)

lemma setOfAllI (*[intro!] doesn't seem to work well*):
  assumes "\<exists>x \<in> S : a = e(x)"
  shows "a \<in> { e(x) : x \<in> S }"
using assms by (blast intro: iffD2[OF setOfAll])

lemma setOfAll_eqI [intro]:
  assumes "a = e(x)" and "x \<in> S"
  shows "a \<in> { e(x) : x \<in> S }"
using assms by (blast intro: setOfAllI)

lemma setOfAllE [elim!]:
  assumes "a \<in> { e(x) : x \<in> S }" and "\<And>x. \<lbrakk> x \<in> S; e(x) = a \<rbrakk> \<Longrightarrow> P"
  shows "P"
using assms by (blast dest: iffD1[OF setOfAll])

lemma setOfAll_iff [simp]:
  "(a \<in> { e(x) : x \<in> S }) = (\<exists>x\<in>S : a = e(x))"
by blast

lemma setOfAll_triv [simp]: "{ x : x \<in> S } = S"
by blast

lemma setOfAll_cong (*[cong]*):
  assumes "S = T" and "\<And>x. x \<in> T \<Longrightarrow> e(x) = f(x)"
  shows "{ e(x) : x \<in> S } = { f(y) : y \<in> T }"
using assms by auto

text \<open>
  The following rule for showing equality of sets defined by comprehension
  is probably too general to use by default with the automatic proof methods.
\<close>

lemma setOfAllEqual:
  assumes "\<And>x. x \<in> S \<Longrightarrow> \<exists>y\<in>T : e(x) = f(y)"
  and "\<And>y. y \<in> T \<Longrightarrow> \<exists>x\<in>S : f(y) = e(x)"
  shows "{ e(x) : x \<in> S } = { f(y) : y \<in> T }"
using assms by auto

lemma subsetOfI [intro!]:
  assumes "a \<in> S" and "P(a)"
  shows "a \<in> { x \<in> S : P(x) }"
using assms by (blast intro: iffD2[OF subsetOf])

lemma subsetOfE [elim!]:
  assumes "a \<in> { x \<in> S : P(x) }" and "\<lbrakk> a \<in> S; P(a) \<rbrakk> \<Longrightarrow> Q"
  shows "Q"
using assms by (blast dest: iffD1[OF subsetOf])

lemma subsetOfD1:
  assumes "a \<in> { x \<in> S : P(x) }"
  shows "a \<in> S"
using assms by blast

lemma subsetOfD2:
  assumes "a \<in> { x \<in> S : P(x) }"
  shows "P(a)"
using assms by blast

lemma subsetOf_iff [simp]:
  "(a \<in> { x \<in> S : P(x) }) = (a \<in> S \<and> P(a))"
by blast

lemma subsetOf_cong:
  assumes "S = T" and "\<And>x. x \<in> T \<Longrightarrow> P(x) \<Leftrightarrow> Q(x)"
  shows "{x \<in> S : P(x)} = {y \<in> T : Q(y)}"
using assms by blast

lemma subsetOfEqual:
  assumes "\<And>x. \<lbrakk> x \<in> S; P(x) \<rbrakk> \<Longrightarrow> x \<in> T"
  and "\<And>x. \<lbrakk> x \<in> S; P(x) \<rbrakk> \<Longrightarrow> Q(x)"
  and "\<And>y. \<lbrakk> y \<in> T; Q(y) \<rbrakk> \<Longrightarrow> y \<in> S"
  and "\<And>y. \<lbrakk> y \<in> T; Q(y) \<rbrakk> \<Longrightarrow> P(y)"
  shows "{x \<in> S : P(x)} = {y \<in> T : Q(y)}"
by (safe elim!: assms)


subsection \<open> @{text UNION} -- basic rules for generalized union \<close>

lemma UNIONI [intro]:
  assumes "B \<in> C" and "a \<in> B"
  shows "a \<in> UNION C"
using assms by (blast intro: UNION[THEN iffD2])

lemma UNIONE [elim!]:
  assumes "a \<in> UNION C" and "\<And>B. \<lbrakk> a \<in> B; B \<in> C \<rbrakk> \<Longrightarrow> P"
  shows "P"
using assms by (blast dest: iffD1 [OF UNION])

lemma UNION_iff [simp]:
  "(a \<in> UNION C) = (\<exists>B\<in>C : a \<in> B)"
by blast


subsection \<open> The empty set \<close>

text \<open>
  Proving that the empty set has no elements is a bit tricky.
  We first show that the set @{term "{x \<in> {} : FALSE}"} is empty
  and then use the foundation axiom to show that it equals the
  empty set.
\<close>

lemma emptysetEmpty: "a \<notin> {}"
proof
  assume a: "a \<in> {}"
  let ?empty = "{ x \<in> {} : FALSE }"
  from foundation[where A="?empty"]
  have "{} = ?empty" by blast
  from this a have "a \<in> ?empty" by (rule subst)
  thus "FALSE" by blast
qed

text \<open> @{text "a \<in> {} \<Longrightarrow> P"} \<close>
lemmas emptyE [elim!] = emptysetEmpty[THEN notE]

lemma [simp]: "(a \<in> {}) = FALSE"
by blast

lemma emptysetI [intro!]:
  assumes "\<forall>x : x \<notin> A"
  shows "A = {}"
using assms by (blast intro: setEqualI)

lemmas emptysetI_rev [intro!] = sym[OF emptysetI]

lemma emptysetIffEmpty (*[simp]*): "(A = {}) = (\<forall>x : x \<notin> A)"
by blast

lemma emptysetIffEmpty' (*[simp]*): "({} = A) = (\<forall>x : x \<notin> A)"
by blast

lemma nonEmpty [simp]:
  "(A \<noteq> {}) = (\<exists>x : x \<in> A)"
  "({} \<noteq> A) = (\<exists>x : x \<in> A)"
by (blast+)

text \<open> Complete critical pairs \<close>
lemmas nonEmpty' [simp] = nonEmpty[simplified]
\<comment> \<open> @{text "((A = {}) = FALSE) = (\<exists>x : x \<in> A)"},
     @{text "(({} = A) = FALSE) = (\<exists>x : x \<in> A)"} \<close>

lemma emptysetD (*[dest]*):
  assumes "A = {}"
  shows "x \<notin> A"
using assms by blast

(* declare sym[THEN emptysetD, dest] *)

lemma emptySubset [iff]: "{} \<subseteq> A"
by blast

lemma nonEmptyI:
  assumes "a \<in> A"
  shows "A \<noteq> {}"
using assms by blast

lemma nonEmptyE:
  assumes "A \<noteq> {}" and "\<And>x. x \<in> A \<Longrightarrow> P"
  shows "P"
using assms by blast

lemma subsetEmpty [simp]: "(A \<subseteq> {}) = (A = {})"
by blast

lemma [simp]:
  "bAll({}, P) = TRUE"
  "bEx({}, P) = FALSE"
by (blast+)


subsection \<open> @{text SUBSET} -- the powerset operator \<close>

lemma SUBSETI [intro!]:
  assumes "A \<subseteq> B"
  shows "A \<in> SUBSET B"
using assms by (blast intro: iffD2[OF SUBSET])

lemma SUBSETD [dest!]:
  assumes "A \<in> SUBSET B"
  shows "A \<subseteq> B"
using assms by (blast dest: iffD1[OF SUBSET])

lemma SUBSET_iff [simp]:
  "(A \<in> SUBSET B) = (A \<subseteq> B)"
by blast

lemmas emptySUBSET = emptySubset[THEN SUBSETI] \<comment> \<open> @{term "{} \<in> SUBSET A"} \<close>
lemmas selfSUBSET = subsetRefl[THEN SUBSETI]   \<comment> \<open> @{term "A \<in> SUBSET A"} \<close>


subsection \<open> @{text INTER} -- basic rules for generalized intersection \<close>

text \<open>
  Generalized intersection is not officially part of \tlaplus{} but can
  easily be defined as above. Observe that the rules are not exactly
  dual to those for @{text UNION} because the intersection of the
  empty set is defined to be the empty set.
\<close>

lemma INTERI [intro]:
  assumes "\<And>B. B \<in> C \<Longrightarrow> a \<in> B" and "\<exists>B : B \<in> C"
  shows "a \<in> INTER C"
using assms unfolding INTER_def by blast

lemma INTERE [elim]:
  assumes "a \<in> INTER C" and "\<lbrakk> a \<in> UNION C; \<And>B. B \<in> C \<Longrightarrow> a \<in> B \<rbrakk> \<Longrightarrow> P"
  shows "P"
using assms unfolding INTER_def by blast

lemma INTER_iff [simp]:
  "(a \<in> INTER C) = (a \<in> UNION C \<and> (\<forall>B\<in>C : a \<in> B))"
by blast


subsection \<open> Binary union, intersection, and difference: basic rules \<close>

text \<open>
  We begin by proving some lemmas about the auxiliary pairing operator
  @{text upair}. None of these theorems is active by default, as the
  operator is not part of \tlaplus{} and should not occur in actual reasoning.
  The dependencies between these operators are quite tricky, therefore
  the order of the first few lemmas in this section is tightly constrained.
\<close>

lemma upairE:
  assumes "x \<in> upair(a,b)" and "x=a \<Longrightarrow> P" and "x=b \<Longrightarrow> P"
  shows "P"
using assms by (auto simp: upair_def)

lemma unionE [elim!]:
  assumes "x \<in> A \<union> B" and "x \<in> A \<Longrightarrow> P" and "x \<in> B \<Longrightarrow> P"
  shows "P"
using assms by (auto simp: union_def elim: upairE)

lemma upairI1: "a \<in> upair(a,b)"
by (auto simp: upair_def)

lemma upairI2: "b \<in> upair(a,b)"
by (auto simp: upair_def)

lemma upair_iff: "(c \<in> upair(a,b)) = (c=a \<or> c=b)"
by (blast intro: upairI1 upairI2 elim: upairE)

lemma unionI1:
  assumes "a \<in> A"
  shows "a \<in> A \<union> B"
using assms by (auto simp: union_def upair_iff)

lemma unionI2:
  assumes "a \<in> B"
  shows "a \<in> A \<union> B"
using assms by (auto simp: union_def upair_iff)

lemma union_iff [simp]: "(c \<in> A \<union> B) = (c \<in> A \<or> c \<in> B)"
by (auto simp: union_def upair_iff)

lemma unionCI [intro!]:
  assumes "c \<notin> B \<Longrightarrow> c \<in> A"
  shows "c \<in> A \<union> B"
using assms by auto

(** needed to reason about finite set enumerations **)
lemma addElt_iff [simp]: "(x \<in> addElt(a,A)) = (x = a \<or> x \<in> A)"
by (auto simp: addElt_def upair_iff)

lemma addEltI [intro!]:
  assumes "x \<noteq> a \<Longrightarrow> x \<in> A"
  shows "x \<in> addElt(a,A)"
using assms by auto

lemma addEltE [elim!]:
  assumes "x \<in> addElt(a,A)" and "x=a \<Longrightarrow> P" and "x \<in> A \<Longrightarrow> P"
  shows "P"
using assms by auto

lemma singleton_iff (*[simp]*): "(a \<in> {b}) = (a = b)"
  by auto

lemma singletonI (*[intro!]*): "a \<in> {a}"
by simp

lemma addEltSubsetI:
  assumes "a \<in> B" and "A \<subseteq> B"
  shows "addElt(a,A) \<subseteq> B"
using assms by blast

lemma addEltSubsetE [elim]:
  assumes "addElt(a,A) \<subseteq> B" and "\<lbrakk> a \<in> B; A \<subseteq> B \<rbrakk> \<Longrightarrow> P"
  shows "P"
using assms by blast

lemma addEltSubset_iff: "(addElt(a,A) \<subseteq> B) = (a \<in> B \<and> A \<subseteq> B)"
by blast

text \<open> Adding the two following lemmas to the simpset breaks proofs. \<close>
lemma addEltEqual_iff: "(addElt(a,A) = S) = (a \<in> S \<and> A \<subseteq> S \<and> S \<subseteq> addElt(a,A))"
by blast

lemma equalAddElt_iff: "(S = addElt(a,A)) = (a \<in> S \<and> A \<subseteq> S \<and> S \<subseteq> addElt(a,A))"
by blast

lemma addEltEqualAddElt:
  "(addElt(a,A) = addElt(b,B)) =
   (a \<in> addElt(b,B) \<and> A \<subseteq> addElt(b,B) \<and> b \<in> addElt(a,A) \<and> B \<subseteq> addElt(a,A))"
by (auto simp: addEltEqual_iff)

lemma inter_iff [simp]: "(c \<in> A \<inter> B) = (c \<in> A \<and> c \<in> B)"
by (simp add: inter_def)

lemma interI [intro!]:
  assumes "c \<in> A" and "c \<in> B"
  shows "c \<in> A \<inter> B"
using assms by simp

lemma interD1:
  assumes "c \<in> A \<inter> B"
  shows "c \<in> A"
using assms by simp

lemma interD2:
  assumes "c \<in> A \<inter> B"
  shows "c \<in> B"
using assms by simp

lemma interE [elim!]:
  assumes "c \<in> A \<inter> B" and "\<lbrakk> c \<in> A; c \<in> B \<rbrakk> \<Longrightarrow> P"
  shows "P"
using assms by simp

lemma setminus_iff [simp]: "(c \<in> A \<setminus> B) = (c \<in> A \<and> c \<notin> B)"
by (simp add: setminus_def)

lemma setminusI [intro!]:
  assumes "c \<in> A" and "c \<notin> B"
  shows "c \<in> A \<setminus> B"
using assms by simp

lemma setminusD1:
  assumes "c \<in> A \<setminus> B"
  shows "c \<in> A"
using assms by simp

lemma setminusD2:
  assumes "c \<in> A \<setminus> B"
  shows "c \<notin> B"
using assms by simp

lemma setminusE [elim!]:
  assumes "c \<in> A \<setminus> B" and "\<lbrakk> c \<in> A; c \<notin> B \<rbrakk> \<Longrightarrow> P"
  shows "P"
using assms by simp

lemma subsetAddElt_iff:
  "(B \<subseteq> addElt(a,A)) = (B \<subseteq> A \<or> (\<exists>C \<in> SUBSET A : B = addElt(a,C)))"
  (is "?lhs = ?rhs")
proof -
  have "?lhs \<Rightarrow> ?rhs"
  proof
    assume 1: "?lhs" show ?rhs
    proof (cases "a \<in> B")
      case True
      from 1 have "B \<setminus> {a} \<in> SUBSET A" by blast
      moreover
      from True 1 have "B = addElt(a, B \<setminus> {a})" by blast
      ultimately
      show ?thesis by blast
    next
      case False
      with 1 show ?thesis by blast
    qed
  qed
  moreover
  have "?rhs \<Rightarrow> ?lhs" by blast
  ultimately show ?thesis by blast
qed

lemma subsetAddEltE [elim]:
  assumes "B \<subseteq> addElt(a,A)" and "B \<subseteq> A \<Longrightarrow> P" and "\<And>C. \<lbrakk> C \<subseteq> A; B = addElt(a,C) \<rbrakk> \<Longrightarrow> P"
  shows "P"
using assms by (auto simp: subsetAddElt_iff)


subsection \<open> Consequences of the foundation axiom \<close>

lemma inAsym:
  assumes hyps: "a \<in> b" "\<not>P \<Longrightarrow> b \<in> a"
  shows "P"
proof (rule contradiction)
  assume "\<not>P"
  with foundation[where A="{a,b}"] hyps 
  show "FALSE" by blast
qed

lemma inIrrefl:
  assumes "a \<in> a"
  shows "P"
using assms by (rule inAsym, blast)

lemma inNonEqual:
  assumes "a \<in> A"
  shows "a \<noteq> A"
using assms by (blast elim: inIrrefl)

lemma equalNotIn:
  assumes "A = B"
  shows "A \<notin> B"
using assms by (blast elim: inIrrefl)


subsection \<open> Miniscoping of bounded quantifiers \<close>

lemma miniscope_bAll [simp]:
  "\<And>P Q. (\<forall>x\<in>A : P(x) \<and> Q) = ((\<forall>x\<in>A : P(x)) \<and> (A = {} \<or> Q))"
  "\<And>P Q. (\<forall>x\<in>A : P \<and> Q(x)) = ((A = {} \<or> P) \<and> (\<forall>x\<in>A : Q(x)))"
  "\<And>P Q. (\<forall>x\<in>A : P(x) \<or> Q) = ((\<forall>x\<in>A : P(x)) \<or> Q)"
  "\<And>P Q. (\<forall>x\<in>A : P \<or> Q(x)) = (P \<or> (\<forall>x\<in>A : Q(x)))"
  "\<And>P Q. (\<forall>x\<in>A : P(x) \<Rightarrow> Q) = ((\<exists>x\<in>A : P(x)) \<Rightarrow> Q)"
  "\<And>P Q. (\<forall>x\<in>A : P \<Rightarrow> Q(x)) = (P \<Rightarrow> (\<forall>x\<in>A : Q(x)))"
  "\<And>P. (\<not>(\<forall>x\<in>A : P(x))) = (\<exists>x\<in>A : \<not>P(x))"
  "\<And>P. (\<forall>x \<in> addElt(a,A) : P(x)) = (P(a) \<and> (\<forall>x\<in>A : P(x)))"
  "\<And>P. (\<forall>x \<in> UNION A : P(x)) = (\<forall>B \<in> A : \<forall>x\<in>B : P(x))"
  "\<And>P. (\<forall>x \<in> {e(y) : y\<in>A} : P(x)) = (\<forall>y\<in>A : P(e(y)))"
  "\<And>P Q. (\<forall>x \<in> {y \<in> A : P(y)} : Q(x)) = (\<forall>y\<in>A: P(y) \<Rightarrow> Q(y))"
by (blast+)

lemma bAllUnion [simp]:
  "(\<forall>x \<in> A \<union> B : P(x)) = ((\<forall>x\<in>A : P(x)) \<and> (\<forall>x\<in>B : P(x)))"
by blast

lemma bAllInter [simp]:
  "(\<forall>x \<in> A \<inter> B : P(x)) = (\<forall>x\<in>A : x \<in> B \<Rightarrow> P(x))"
by blast

lemma miniscope_bEx [simp]:
  "\<And>P Q. (\<exists>x\<in>A : P(x) \<and> Q) = ((\<exists>x\<in>A : P(x)) \<and> Q)"
  "\<And>P Q. (\<exists>x\<in>A : P \<and> Q(x)) = (P \<and> (\<exists>x\<in>A : Q(x)))"
  "\<And>P Q. (\<exists>x\<in>A : P(x) \<or> Q) = ((\<exists>x\<in>A : P(x)) \<or> (A \<noteq> {} \<and> Q))"
  "\<And>P Q. (\<exists>x\<in>A : P \<or> Q(x)) = ((A \<noteq> {} \<and> P) \<or> (\<exists>x\<in>A : Q(x)))"
  "\<And>P Q. (\<exists>x\<in>A : P(x) \<Rightarrow> Q) = ((\<forall>x\<in>A : P(x)) \<Rightarrow> (A \<noteq> {} \<and> Q))"
  "\<And>P Q. (\<exists>x\<in>A : P \<Rightarrow> Q(x)) = ((A={} \<or> P) \<Rightarrow> (\<exists>x\<in>A : Q(x)))"
  "\<And>P. (\<exists>x \<in> addElt(a,A) : P(x)) = (P(a) \<or> (\<exists>x\<in>A : P(x)))"
  "\<And>P. (\<not>(\<exists>x\<in>A : P(x))) = (\<forall>x\<in>A : \<not>P(x))"
  "\<And>P. (\<exists>x \<in> UNION A : P(x)) = (\<exists>B \<in> A : \<exists>x\<in>B : P(x))"
  "\<And>P. (\<exists>x \<in> {e(y) : y \<in> S} : P(x)) = (\<exists>y\<in>S : P(e(y)))"
  "\<And>P Q. (\<exists>x \<in> {y \<in> S : P(y)} : Q(x)) = (\<exists>y\<in>S : P(y) \<and> Q(y))"
by (blast+)

text \<open> completing critical pairs for negated assumption \<close>
lemma notbQuant' [simp]:
  "\<And>P. ((\<forall>x\<in>A : P(x)) = FALSE) = (\<exists>x\<in>A : \<not>P(x))"
  "\<And>P. ((\<exists>x\<in>A : P(x)) = FALSE) = (\<forall>x\<in>A : \<not>P(x))"
by (auto simp: miniscope_bAll[simplified] miniscope_bEx[simplified])

lemma bExistsUnion [simp]:
  "(\<exists>x \<in> A \<union> B : P(x)) = ((\<exists>x\<in>A : P(x)) \<or> (\<exists>x\<in>B : P(x)))"
by blast

lemma bExistsInter [simp]:
  "(\<exists>x \<in> A \<inter> B : P(x)) = (\<exists>x\<in>A : x \<in> B \<and> P(x))"
by blast

lemma bQuant_distribs: \<comment> \<open> not active by default \<close>
  "(\<forall>x\<in>A : P(x) \<and> Q(x)) = ((\<forall>x\<in>A : P(x)) \<and> (\<forall>x\<in>A : Q(x)))"
  "(\<exists>x\<in>A : P(x) \<or> Q(x)) = ((\<exists>x\<in>A : P(x)) \<or> (\<exists>x\<in>A : Q(x)))"
by (blast+)

lemma bQuantOnePoint [simp]:
  "(\<exists>x\<in>A : x=a) = (a \<in> A)"
  "(\<exists>x\<in>A : a=x) = (a \<in> A)"
  "(\<exists>x\<in>A : x=a \<and> P(x)) = (a \<in> A \<and> P(a))"
  "(\<exists>x\<in>A : a=x \<and> P(x)) = (a \<in> A \<and> P(a))"
  "(\<forall>x\<in>A : x=a \<Rightarrow> P(x)) = (a\<in>A \<Rightarrow> P(a))"
  "(\<forall>x\<in>A : a=x \<Rightarrow> P(x)) = (a\<in>A \<Rightarrow> P(a))"
by (blast+)


subsection \<open> Simplification of set comprehensions \<close>

lemma comprehensionSimps [simp]:
  "\<And>e. setOfAll({}, e) = {}"
  "\<And>P. subsetOf({}, P) = {}"
  "\<And>A P. { x \<in> A : P } = (IF P THEN A ELSE {})"
  "\<And>A a e. { e(x) : x \<in> addElt(a,A) } = addElt(e(a), { e(x) : x \<in> A })"
  "\<And>A a P. { x \<in> addElt(a,A) : P(x) } = (IF P(a) THEN addElt(a, {x \<in> A : P(x)}) ELSE {x \<in> A : P(x)})"
  "\<And>e f. { e(x) : x \<in> { f(y) : y \<in> A } } = { e(f(y)) : y \<in> A }"
  "\<And>P Q A. { x \<in> {y\<in>A : P(y)} : Q(x) } = { x \<in> A : P(x) \<and> Q(x) }"
  "\<And>P A. subsetOf(A, \<lambda>x. x \<in> { y \<in> B : Q(y) }) = { x \<in> A \<inter> B : Q(x) }"
  "\<And>e A B. subsetOf(A, \<lambda>x. x \<in> { e(y) : y \<in> B }) = { e(y) : y \<in> B } \<inter> A"
  (* the symmetrical { e(x) : x \<in> {y\<in>A : P(y)} } cannot be simplified *)
  "\<And>A e. setOfAll(A, \<lambda>x. e) = (IF A = {} THEN {} ELSE {e})"
by auto

text \<open> The following are not active by default. \<close>

lemma comprehensionDistribs:
  "\<And>e. { e(x) : x \<in> A \<union> B } = {e(x) : x\<in>A} \<union> {e(x) : x\<in>B}"
  "\<And>P. { x \<in> A \<union> B : P(x) } = {x\<in>A : P(x)} \<union> {x\<in>B : P(x)}"
  \<comment> \<open> @{text setOfAll} and intersection or difference do not distribute \<close>
  "\<And>P. { x \<in> A \<inter> B : P(x) } = {x\<in>A : P(x)} \<inter> {x\<in>B : P(x)}"
  "\<And>P. { x \<in> A \<setminus> B : P(x) } = {x\<in>A : P(x)} \<setminus> {x\<in>B : P(x)}"
by (blast+)


subsection \<open> Binary union, intersection, and difference: inclusions and equations \<close>

text \<open>
  The following list contains many simple facts about set theory.
  Only the most trivial of these are included in the default set
  of rewriting rules.
\<close>

lemma addEltCommute: "addElt(a, addElt(b, C)) = addElt(b, addElt(a, C))"
by blast

lemma addEltAbsorb: "a \<in> A \<Longrightarrow> addElt(a,A) = A"
by blast

lemma addEltTwice: "addElt(a, addElt(a, A)) = addElt(a, A)"
by blast

lemma interAddEltLeft: "addElt(a,B) \<inter> C = (IF a \<in> C THEN addElt(a, B \<inter> C) ELSE B \<inter> C)"
by (blast intro: condI elim: condE)

lemma interAddEltRight: "C \<inter> addElt(a,B) = (IF a \<in> C THEN addElt(a, C \<inter> B) ELSE C \<inter> B)"
by (blast intro: condI elim: condE)

lemma addEltInter: "addElt(a, B \<inter> C) = addElt(a,B) \<inter> addElt(a,C)"
by blast

lemma setminusAddEltLeft: "addElt(a,B) \<setminus> C = (IF a \<in> C THEN B \<setminus> C ELSE addElt(a, B \<setminus> C))"
by (blast intro: condI elim: condE)

lemma interSubset: "(C \<subseteq> A \<inter> B) = (C \<subseteq> A \<and> C \<subseteq> B)"
by blast

lemma interLB1: "A \<inter> B \<subseteq> A"
by blast

lemma interLB2: "A \<inter> B \<subseteq> B"
by blast

lemma interGLB:
  assumes "C \<subseteq> A" and "C \<subseteq> B"
  shows "C \<subseteq> A \<inter> B"
using assms by blast

lemma interEmpty [simp]:
  "A \<inter> {} = {}"
  "{} \<inter> A = {}"
by blast+

lemma interAbsorb [simp]: "A \<inter> A = A"
by blast

lemma interLeftAbsorb: "A \<inter> (A \<inter> B) = A \<inter> B"
by blast

lemma interCommute: "A \<inter> B = B \<inter> A"
by blast

lemma interLeftCommute: "A \<inter> (B \<inter> C) = B \<inter> (A \<inter> C)"
by blast

lemma interAssoc: "(A \<inter> B) \<inter> C = A \<inter> (B \<inter> C)"
by blast

text \<open> Intersection is an AC operator: can be added to simp where appropriate \<close>
lemmas interAC = interAssoc interCommute interLeftCommute interLeftAbsorb

lemma subsetOfInter: "{x\<in>A : P(x)} \<inter> B = {x \<in> A \<inter> B : P(x)}"
by blast

lemma interSubsetOf:
  "B \<inter> {x\<in>A : P(x)} = {x \<in> B\<inter>A : P(x)}"
by blast

lemma subsetOfDisj:
  "{x\<in>A : P(x) \<or> Q(x)} = {x\<in>A : P(x)} \<union> {x\<in>A : Q(x)}"
by blast

lemma subsetOfConj:
  "{x\<in>A : P(x) \<and> Q(x)} = {x\<in>A : P(x)} \<inter> {x\<in>A : Q(x)}"
by blast

lemma subsetUnion: "(A \<union> B \<subseteq> C) = (A \<subseteq> C \<and> B \<subseteq> C)"
by blast

lemma unionUB1: "A \<subseteq> A \<union> B"
by blast

lemma unionUB2: "B \<subseteq> A \<union> B"
by blast

lemma unionLUB:
  assumes "A \<subseteq> C" and "B \<subseteq> C"
  shows "A \<union> B \<subseteq> C"
using assms by blast

lemma unionEmpty [simp]:
  "A \<union> {} = A"
  "{} \<union> A = A"
by blast+

lemma unionAddEltLeft: "addElt(a,B) \<union> C = addElt(a, B \<union> C)"
by blast

lemma unionAddEltRight: "C \<union> addElt(a,B) = addElt(a, C \<union> B)"
by blast

lemma addEltUnion: "addElt(a, B \<union> C) = addElt(a,B) \<union> addElt(a,C)"
by blast

lemma unionAbsorb [simp]: "A \<union> A = A"
by blast

lemma unionLeftAbsorb: "A \<union> (A \<union> B) = A \<union> B"
by blast

lemma unionCommute: "A \<union> B = B \<union> A"
by blast

lemma unionLeftCommute: "A \<union> (B \<union> C) = B \<union> (A \<union> C)"
by blast

lemma unionAssoc: "(A \<union> B) \<union> C = A \<union> (B \<union> C)"
by blast

text \<open> Union is an AC operator: can be added to simp where appropriate \<close>
lemmas unionAC = unionAssoc unionCommute unionLeftCommute unionLeftAbsorb

text \<open> Lemmas useful for simplifying enumerated sets are active by default \<close>
lemmas enumeratedSetSimps [simp] =
  addEltSubset_iff addEltEqualAddElt addEltCommute addEltTwice
  interAddEltLeft interAddEltRight unionAddEltLeft unionAddEltRight setminusAddEltLeft

(* included below
lemma unionEqualEmpty [simp]: "(A \<union> B = {}) = (A = {} \<and> B = {})"
by blast
*)

lemma interUnionDistrib: "A \<inter> (B \<union> C) = (A \<inter> B) \<union> (A \<inter> C)"
by blast

lemma unionInterDistrib: "A \<union> (B \<inter> C) = (A \<union> B) \<inter> (A \<union> C)"
by blast

lemma setminusSubset: "A \<setminus> B \<subseteq> A"
by blast

lemma subsetSetminus:
  assumes "C \<subseteq> A" and "C \<inter> B = {}"
  shows "C \<subseteq> A \<setminus> B"
using assms by blast

lemma setminusSelf [simp]: "A \<setminus> A = {}"
by blast

lemma setminusDisjoint:
  assumes "A \<inter> B = {}"
  shows "A \<setminus> B = A"
using assms by blast

lemma emptySetminus [simp]: "{} \<setminus> A = {}"
by blast

lemma setminusAddElt: "A \<setminus> addElt(a,B) = (A \<setminus> B) \<setminus> {a}"
by blast

lemma unionSetminusSelf: "A \<union> (B \<setminus> A) = A \<union> B"
by blast

lemma setminusUnionLeft: "(A \<union> B) \<setminus> C = (A \<setminus> C) \<union> (B \<setminus> C)"
by blast

lemma setminusUnionRight: "A \<setminus> (B \<union> C) = (A \<setminus> B) \<inter> (A \<setminus> C)"
by blast

lemma unionSetminusLeft: "(A \<setminus> B) \<union> C = (A \<union> C) \<setminus> (A \<inter> (B \<setminus> C))"
by blast

lemma unionSetminusRight: "C \<union> (A \<setminus> B) = (C \<union> A) \<setminus> (A \<inter> (B \<setminus> C))"
by blast

lemma setminusInterLeft: "(A \<inter> B) \<setminus> C = A \<inter> (B \<setminus> C)"
by blast

lemma setminusInterRight: "A \<setminus> (B \<inter> C) = (A \<setminus> B) \<union> (A \<setminus> C)"
by blast

lemma interSetminusLeft: "(A \<setminus> B) \<inter> C = (A \<inter> C) \<setminus> B"
by blast

lemma interSetminusRight: "C \<inter> (A \<setminus> B) = (C \<inter> A) \<setminus> B"
by blast

lemma isEmptySimps [simp]:
  "(S \<union> T = {}) = ((S = {}) \<and> (T = {}))"
  "({} = S \<union> T) = ((S = {}) \<and> (T = {}))"
  "(S \<inter> T = {}) = (\<forall>x \<in> S : x \<notin> T)"
  "({} = S \<inter> T) = (\<forall>x \<in> S : x \<notin> T)"
  "(A \<setminus> B = {}) = (A \<subseteq> B)"
  "({} = A \<setminus> B) = (A \<subseteq> B)"
  "(subsetOf(S,P) = {}) = (\<forall>x \<in> S : \<not> P(x))"
  "({} = subsetOf(S,P)) = (\<forall>x \<in> S : \<not> P(x))"
  "(setOfAll(S,e) = {}) = (S = {})"
  "({} = setOfAll(S,e)) = (S = {})"
  "(addElt(a,S) = {}) = FALSE"
  "({} = addElt(a,S)) = FALSE"
  "(SUBSET S = {}) = FALSE"
  "({} = SUBSET S) = FALSE"
by blast+


subsection \<open> Generalized union: inclusions and equalities \<close>

lemma UNIONSimps [simp]:
  "UNION {} = {}"
  "UNION addElt(a,A) = (a \<union> UNION A)"
  "(UNION S = {}) = (\<forall>A \<in> S : A = {})"
by blast+

lemma UNIONIsSubset [simp]: "(UNION A \<subseteq> C) = (\<forall>x\<in>A : x \<subseteq> C)"
by blast

lemma UNION_UB:
  assumes "B \<in> A"
  shows "B \<subseteq> UNION A"
using assms by blast

lemma UNION_LUB:
  assumes "\<And>B. B \<in> A \<Longrightarrow> B \<subseteq> C"
  shows "UNION A \<subseteq> C"
using assms by blast

lemma UNIONunionDistrib: "UNION (A \<union> B) = UNION A \<union> UNION B"
by blast

lemma UNIONinter: "UNION (A \<inter> B) \<subseteq> UNION A \<inter> UNION B"
by blast

lemma UNIONDisjoint: "((UNION A) \<inter> C = {}) = (\<forall>B\<in>A : B \<inter> C = {})"
by blast

lemma interUNION: "(UNION A) \<inter> B = UNION { C \<inter> B : C \<in> A }"
by blast

lemma setminusUNIONLeft: "(UNION A) \<setminus> B = UNION { C \<setminus> B : C \<in> A }"
by blast

lemma UNION_mono:
  assumes "A \<subseteq> B"
  shows "UNION A \<subseteq> UNION B"
using assms by blast


subsection \<open> Generalized intersection: inclusions and equations \<close>


lemma INTERSimps [simp]:
  "INTER {} = {}"
  "INTER {A} = A"
  "A \<noteq> {} \<Longrightarrow> INTER addElt(a,A) = (a \<inter> INTER A)"
by (blast+)

lemma subsetINTER [simp]:
  assumes "A \<noteq> {}"
  shows "(C \<subseteq> INTER A) = (\<forall>B\<in>A : C \<subseteq> B)"
using assms by blast

lemma INTER_LB:
  assumes "B \<in> A"
  shows "INTER A \<subseteq> B"
using assms by blast

lemma INTER_GLB:
  assumes "A \<noteq> {}" and "\<And>B. B \<in> A \<Longrightarrow> C \<subseteq> B"
  shows "C \<subseteq> INTER A"
using assms by blast

lemma INTERunionDistrib:
  assumes "A \<noteq> {}" and "B \<noteq> {}"
  shows "INTER (A \<union> B) = INTER A \<inter> INTER B"
using assms by auto

lemma interINTER: "(INTER A) \<inter> B \<subseteq> INTER {C \<inter> B : C \<in> A}"
by blast

lemma unionINTER:
  assumes "A \<noteq> {}"
  shows "(INTER A) \<union> B = INTER {C \<union> B : C \<in> A}"
using assms by auto

lemma setminusINTERLeft: "(INTER A) \<setminus> B = INTER {C \<setminus> B : C \<in> A}"
by auto

lemma setminusINTERRight:
  assumes "A \<noteq> {}"
  shows "B \<setminus> (INTER A) = UNION {B \<setminus> C : C \<in> A}"
using assms by auto

lemma bAllSubset:
  assumes "\<forall>x \<in> A : P(x)" and "B \<subseteq> A" and "b \<in> B"
  shows "P(b)"
using assms by blast

lemma INTER_anti_mono:
  assumes "A \<noteq> {}" and "A \<subseteq> B"
  shows "INTER B \<subseteq> INTER A"
using assms by (auto simp: INTER_def)


subsection \<open> Powerset: inclusions and equations \<close>

lemma SUBSETEmpty [simp]: "SUBSET {} = { {} }"
by blast

lemma SUBSETaddElt:
  "SUBSET addElt(a,A) = SUBSET A \<union> {addElt(a,X) : X \<in> SUBSET A}"
by (rule setEqualI, auto)

lemma unionSUBSET: "(SUBSET A) \<union> (SUBSET B) \<subseteq> SUBSET (A \<union> B)"
by blast

lemma UNION_SUBSET [simp]: "UNION (SUBSET A) = A"
by blast

lemma SUBSET_UNION: "A \<subseteq> SUBSET (UNION A)"
by blast

lemma UNION_in_SUBSET: "(UNION A \<in> SUBSET B) = (A \<in> SUBSET (SUBSET B))"
by blast

lemma SUBSETinter: "SUBSET (A \<inter> B) = SUBSET A \<inter> SUBSET B"
by blast

end
