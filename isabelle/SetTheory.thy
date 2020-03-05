(*  Title:      TLA+/SetTheory.thy
    Author:     Stephan Merz, LORIA
    Copyright (C) 2008-2011  INRIA and Microsoft Corporation
    License:    BSD
    Version:    Isabelle2011-1
    Time-stamp: <2011-10-11 17:38:48 merz>
*)

header {* \tlaplus{} Set Theory *}

theory SetTheory
imports PredicateLogic
begin

text {*
  This theory defines the version of Zermelo-Fr\"ankel set theory
  that underlies \tlaplus{}.
*}

subsection {* Basic syntax and axiomatic basis of set theory. *}

text {*
  We take the set-theoretic constructs of \tlaplus{}, but add generalized
  intersection for symmetry and convenience. (Note that @{text "INTER {} = {}"}.)
*}

consts
  emptyset  ::  "c"        ("{}" 100)      -- {* empty set *}
  upair     ::  "[c, c] \<Rightarrow> c"              -- {* unordered pairs *}
  addElt    ::  "[c, c] \<Rightarrow> c"              -- {* add element to set *}
  infinity  ::  "c"                        -- {* infinity set *}
  SUBSET    ::  "c \<Rightarrow> c"   ("SUBSET _" [100]90) -- {* power set *}
  UNION     ::  "c \<Rightarrow> c"   ("UNION _" [100]90)  -- {* generalized union *}
  INTER     ::  "c \<Rightarrow> c"   ("INTER _" [100]90)  -- {* generalized intersection *}
  "cup"     ::  "[c, c] \<Rightarrow> c" (infixl "\\cup" 65)  -- {* binary union *}
  "cap"     ::  "[c, c] \<Rightarrow> c" (infixl "\\cap" 70)  -- {* binary intersection *}
  "setminus"::  "[c, c] \<Rightarrow> c" (infixl "\\" 65)  -- {* binary set difference *}
  "in"      ::  "[c, c] \<Rightarrow> c" (infixl "\\in" 50)  -- {* membership relation *}
  "subseteq"::  "[c, c] \<Rightarrow> c" (infixl "\\subseteq" 50)  -- {* subset relation *}
  subsetOf  ::  "[c, c \<Rightarrow> c] \<Rightarrow> c"  -- {*@{text "subsetOf(S,p)"} = $\{x \in S : p\}$*}
  setOfAll  ::  "[c, c \<Rightarrow> c] \<Rightarrow> c"  -- {*@{text "setOfAll(S,e)"} = $\{e : x \in S\}$*}
  bChoice   ::  "[c, c \<Rightarrow> c] \<Rightarrow> c"         -- {* bounded choice *}
  bAll      ::  "[c, c \<Rightarrow> c] \<Rightarrow> c"         -- {* bounded universal quantifier *}
  bEx       ::  "[c, c \<Rightarrow> c] \<Rightarrow> c"         -- {* bounded existential quantifier *}

notation (xsymbols)
  "cup"        (infixl "\<union>" 65)  and
  "cap"        (infixl "\<inter>" 70)  and
  "setminus"   (infixl "\<setminus>" 65)  and
  "in"         (infixl "\<in>" 50)  and
  "subseteq"   (infixl "\<subseteq>" 50)

notation (HTML output)
  "cup"        (infixl "\<union>" 65)  and
  "cap"        (infixl "\<inter>" 70)  and
  "setminus"   (infixl "\<setminus>" 65)  and
  "in"         (infixl "\<in>" 50)  and
  "subseteq"   (infixl "\<subseteq>" 50)

abbreviation "notin(a, S) \<equiv> \<not>(a \<in> S)"   -- {* negated membership *}

notation
  "notin"      (infixl "\\notin" 50)
notation (xsymbols)
  "notin"      (infixl "\<notin>" 50)
notation (HTML output)
  "notin"      (infixl "\<notin>" 50)

abbreviation (input) "supseteq(S, T) \<equiv> T \<subseteq> S"
notation
  "supseteq"    (infixl "\\supseteq" 50)
notation (xsymbols)
  "supseteq"    (infixl "\<supseteq>" 50)
notation (HTML output)
  "supseteq"    (infixl "\<supseteq>" 50)

text {* Concrete syntax: proper sub and superset *}

definition "psubset" :: "[c, c] \<Rightarrow> c" (infixl "\\subset" 50)
where "S \\subset T \<equiv> S \<subseteq> T \<and> S \<noteq> T"

notation (xsymbols)
  "psubset"   (infixl "\<subset>" 50)
notation (HTML output)
  "psubset"   (infixl "\<subset>" 50)

abbreviation (input) "psupset(S,T) \<equiv> T \<subset> S"
notation
  "psupset"  (infix "\\supset" 50)
notation (xsymbols)
  "psupset"  (infix "\<supset>" 50)
notation (HTML output)
  "psupset"  (infix "\<supset>" 50)

lemma psubset_intro [intro!]:
  "\<lbrakk> S \<subseteq> T ; S \<noteq> T \<rbrakk> \<Longrightarrow> S \<subset> T"
unfolding psubset_def by safe

lemma psubset_elim [elim!]:
  "\<lbrakk> S \<subset> T ; \<lbrakk> S \<subseteq> T ; S \<noteq> T \<rbrakk> \<Longrightarrow> C \<rbrakk> \<Longrightarrow> C"
unfolding psubset_def by safe


text {* Concrete syntax: set enumerations *}

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

text {* Concrete syntax: bounded quantification *}

(*** FIXME: allow multiple bindings as in "ALL x:S, y:T. P(x,y)".
  The following was a valiant attempt to define appropriate syntax
  translations, but for some reason the first translation rule below
  is not accepted -- do we need to program a parse translation?

nonterminal sbinds

syntax
  "@sbind"    ::  "[idt,c] \<Rightarrow> sbinds"         ("_ \\in _")
  "@sbinds"   ::  "[idt,c,sbinds] \<Rightarrow> sbinds"   ("_ \\in _,/ _")
syntax (xsymbols)
  "@sbind"    ::  "[idt,c] \<Rightarrow> sbinds"         ("_ \<in> _")
  "@sbinds"   ::  "[idt,c, sbinds] \<Rightarrow> sbinds"  ("_ \<in> _,/ _")

syntax
  "@bChoice" ::  "[sbinds, c] \<Rightarrow> c"          ("(3CHOOSE _ :/ _)" 10)
  "@bEx"     ::  "[sbinds, c] \<Rightarrow> c"          ("(3\\E _ :/ _)" 10)
  "@bAll"    ::  "[sbinds, c] \<Rightarrow> c"          ("(3\\A _ :/ _)" 10)
syntax (xsymbols)
  "@bEx"     ::  "[sbinds, c] \<Rightarrow> c"          ("(3\<exists>_ :/ _)" 10)
  "@bAll"    ::  "[sbinds, c] \<Rightarrow> c"          ("(3\<forall>_ :/ _)" 10)

translations
  "ALL x:S, sbs. P"  \<rightleftharpoons>  "bAll(S, (ALL sbs. (\<lambda>x. P)))"
  "ALL x:S. P"       \<rightleftharpoons>  "bAll(S, \<lambda>x. P)"
***)

(*** TEMPORARY FIX:
  concrete syntax for bounded quantification, only single binding allowed
  (but possibly multiple variables in input)
***)

syntax
  (* Again, only single variable for bounded choice. *)
  "@bChoice" ::  "[idt, c, c] \<Rightarrow> c"       ("(3CHOOSE _ \\in _ :/ _)" [100,0,0] 10)
  "@bEx"     ::  "[cidts, c, c] \<Rightarrow> c"     ("(3EX _ in _ :/ _)" [100,0,0] 10)
  "@bAll"    ::  "[cidts, c, c] \<Rightarrow> c"     ("(3ALL _ in _ :/ _)" [100,0,0] 10)
syntax (xsymbols)
  "@bChoice" ::  "[idt, c, c] \<Rightarrow> c"       ("(3CHOOSE _ \<in> _ :/ _)" [100,0,0]10)
  "@bEx"     ::  "[cidts, c, c] \<Rightarrow> c"     ("(3\<exists>_ \<in> _ :/ _)" [100,0,0] 10)
  "@bAll"    ::  "[cidts, c, c] \<Rightarrow> c"     ("(3\<forall>_ \<in> _ :/ _)" [100,0,0] 10)
translations
  "CHOOSE x \<in> S : P"      \<rightleftharpoons>  "CONST bChoice(S, \<lambda>x. P)"
  (* the following cannot be a print macro because the RHS is non-linear
     -- need a print translation for display *)
  "\<exists>x, xs \<in> S : P"        \<rightharpoonup>  "CONST bEx(S, \<lambda>x. \<exists>xs \<in> S : P)"
  "\<exists>x \<in> S : P"            \<rightharpoonup>  "CONST bEx(S, \<lambda>x. P)"
  "\<forall>x, xs \<in> S : P"        \<rightharpoonup>  "CONST bAll(S, \<lambda>x. \<forall>xs \<in> S : P)"
  "\<forall>x \<in> S : P"            \<rightharpoonup>  "CONST bAll(S, \<lambda>x. P)"

print_translation {*
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
  in  [(@{const_syntax "bEx"}, bEx_tr'), (@{const_syntax "bAll"}, bAll_tr')]
  end
*}

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

text {* Concrete syntax: set comprehension *}

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
  "@setOfAll" :: "[c, idt, c] \<Rightarrow> c"         ("(1{_ : _ \\in _})")
  "@subsetOf" :: "[idt, c, c] \<Rightarrow> c"         ("(1{_ \\in _ : _})")
syntax (xsymbols)
  "@setOfAll" :: "[c, idt, c] \<Rightarrow> c"         ("(1{_ : _ \<in> _})")
  "@subsetOf" :: "[idt, c, c] \<Rightarrow> c"         ("(1{_ \<in> _ : _})")
translations
  "{e : x \<in> S}"  \<rightleftharpoons>  "CONST setOfAll(S, \<lambda>x. e)"
  "{x \<in> S : P}"  \<rightleftharpoons>  "CONST subsetOf(S, \<lambda>x. P)"

text {* 
  The following definitions make the axioms of set theory more readable.
  Observe that @{text \<in>} is treated as an uninterpreted predicate symbol.
*}

defs
  bChoose_def:  "bChoice(A,P)  \<equiv>  CHOOSE x : x \<in> A \<and> P(x)"
  bEx_def:      "bEx(A, P)  \<equiv>  \<exists>x : x \<in> A \<and> P(x)"
  bAll_def:     "bAll(A, P) \<equiv>  \<forall>x : x \<in> A \<Rightarrow> P(x)"
  subset_def:   "A \<subseteq> B     \<equiv>  \<forall>x \<in> A : x \<in> B"

text {*
  We now state a first batch of axioms of set theory: extensionality
  and the definitions of @{text UNION}, @{text SUBSET}, and @{text setOfAll}.
  Membership is also asserted to be produce Boolean values---in traditional
  presentations of ZF set theory this is ensured by distinguishing sorts of
  terms and formulas.
*}

axiomatization where
  inIsBool [intro!,simp]: "isBool(x \<in> A)"
and
  extension:    "(A = B) \<Leftrightarrow> (A \<subseteq> B) \<and> (B \<subseteq> A)"
and
  UNION:        "(A \<in> UNION S) \<Leftrightarrow> (\<exists>B\<in>S : A \<in> B)"
and
  SUBSET:       "(A \<in> SUBSET S) \<Leftrightarrow> (A \<subseteq> S)"
and
  setOfAll:     "(y \<in> { e(x) : x \<in> S }) \<Leftrightarrow> (\<exists>x\<in>S : y = e(x))"
and
  subsetOf:     "(y \<in> { x \<in> S : P(x) }) \<Leftrightarrow> (y \<in> S \<and> P(y))"

text {*
  Armed with this understanding, we can now define the remaining operators
  of set theory.
*}

defs
  upair_def:    "upair(a,b)  \<equiv>  { IF x={} THEN a ELSE b : x \<in> SUBSET (SUBSET {}) }"
  cup_def:      "A \<union> B  \<equiv>  UNION upair(A,B)"
  addElt_def:   "addElt(a, A)  \<equiv>  upair(a,a) \<union> A"
  cap_def:      "A \<inter> B  \<equiv>  subsetOf(A, \<lambda>x. x \<in> B)"
  diff_def:     "A \<setminus> B  \<equiv>  {x \<in> A : x \<notin> B}"
  INTER_def:    "INTER A \<equiv> { x \<in> UNION A : \<forall>B \<in> A : x \<in> B }"

text {*
  The following two axioms complete our presentation of set theory.
*}

axiomatization where
  -- {* @{term infinity} is some infinite set, but it is not uniquely defined. *}
  infinity:     "({} \<in> infinity) \<and> (\<forall>x \<in> infinity : {x} \<union> x \<in> infinity)"
and
  -- {* The foundation axiom rules out sets that are ``too big''. *}
  foundation:   "(A = {}) \<or> (\<exists>x \<in> A : \<forall>y \<in> x : y \<notin> A)"

subsection {* Boolean operators *}

text {*
  The following lemmas assert that certain operators always return
  Boolean values; these are helpful for the automated reasoning methods.
*}

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


subsection {* Substitution rules *}

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


subsection {* Bounded quantification *}

lemma bAllI [intro!]:
  assumes "\<And>x. x \<in> A \<Longrightarrow> P(x)"
  shows "\<forall>x\<in>A : P(x)"
using assms unfolding bAll_def by blast

lemma bspec [dest?]:
  assumes "\<forall>x\<in>A : P(x)" and "x \<in> A"
  shows "P(x)"
using assms unfolding bAll_def by blast

(*** currently inactive -- causes several obscure warnings about renamed
     variables and seems to slow down large examples such as AtomicBakery
ML {*
  structure Simpdata =
  struct

    open Simpdata;

    val mksimps_pairs = [(@{const_name bAll}, (@{thms bspec}, false))] @ mksimps_pairs;

  end;

  open Simpdata;
*}

declaration {* fn _ =>
  Simplifier.map_ss (fn ss => ss setmksimps (mksimps mksimps_pairs))
*}
***)

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

lemma bExCI:  -- {* implicit proof by contradiction *}
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

(***
  TYPE CHECKING CURRENTLY NOT INSTALLED

  The solver installed by the type checking package breaks some proofs
  and makes the auto tactic loop for unfathomable reasons. Type checking
  itself works, but is not used anywhere.

  TODO: investigate the issue and find out what is really needed about
  type checking.

subsubsection {* Setting up type checking for \tlaplus{}. *}

text {*
  Type checking is intended to solve simple goals, for example showing
  that conjunctions are Boolean, and that the result of a conditional
  expression is a natural number if both branches yield naturals. Unlike
  simplification (Isabelle's rewriting machinery), type checking may
  instantiate unknowns. It is used as a ``solver'' of the simplifier,
  in particular for proving hypotheses of conditional rewrite rules,
  and due to this, proofs by simplification may actually instantiate
  unknowns.

  The code is essentially taken from Isabelle/ZF.
*}

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


subsection {* Simplification of conditional expressions *}

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


subsection {* Rules for subsets and set equality *}

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

lemma subsetCE [elim]: -- {* elimination rule for classical logic *}
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

text {* The subset relation is a partial order. *}

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

text {*
  The rule @{text setEqualI} is too general for use as a default
  introduction rule: we don't want to apply it for Booleans, for
  example. However, instances where at least one term results from
  a set constructor are useful.
*}

lemmas
(** the instances for the empty set are superseded by rules below
  setEqualI [where A = "{}", standard, intro!]
  setEqualI [where B = "{}", standard, intro!]
**)
  setEqualI [where A = "addElt(a,C)", standard, intro!]
  setEqualI [where B = "addElt(a,C)", standard, intro!]
  setEqualI [where A = "SUBSET C", standard, intro!]
  setEqualI [where B = "SUBSET C", standard, intro!]
  setEqualI [where A = "UNION C", standard, intro!]
  setEqualI [where B = "UNION C", standard, intro!]
  setEqualI [where A = "INTER C", standard, intro!]
  setEqualI [where B = "INTER C", standard, intro!]
  setEqualI [where A = "C \<union> D", standard, intro!]
  setEqualI [where B = "C \<union> D", standard, intro!]
  setEqualI [where A = "C \<inter> D", standard, intro!]
  setEqualI [where B = "C \<inter> D", standard, intro!]
  setEqualI [where A = "C \<setminus> D", standard, intro!]
  setEqualI [where B = "C \<setminus> D", standard, intro!]
  setEqualI [where A = "subsetOf(S,P)", standard, intro!]
  setEqualI [where B = "subsetOf(S,P)", standard, intro!]
  setEqualI [where A = "setOfAll(S,e)", standard, intro!]
  setEqualI [where B = "setOfAll(S,e)", standard, intro!]

lemmas setEqualD1 = extension[THEN iffD1, THEN conjD1, standard] -- {* @{text "A = B \<Longrightarrow> A \<subseteq> B"} *}
lemmas setEqualD2 = extension[THEN iffD1, THEN conjD2, standard] -- {* @{text "A = B \<Longrightarrow> B \<subseteq> A"} *}

text {*
  We declare the elimination rule for set equalities as an unsafe
  rule to use with the classical reasoner, so it will be tried if
  the more obvious uses of equality fail.
*}
lemma setEqualE [elim]:
  assumes "A = B"
  and "\<lbrakk> c \<in> A; c \<in> B \<rbrakk> \<Longrightarrow> P" and "\<lbrakk> c \<notin> A; c \<notin> B \<rbrakk> \<Longrightarrow> P"
  shows "P"
using assms by (blast dest: setEqualD1 setEqualD2)

lemma setEqual_iff: "(A = B) = (\<forall>x : x \<in> A \<Leftrightarrow> x \<in> B)"
by (blast intro: setEqualI (*elim: setEqualE*))


subsection {* Set comprehension: @{text setOfAll} and @{text subsetOf} *}

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

text {*
  The following rule for showing equality of sets defined by comprehension
  is probably too general to use by default with the automatic proof methods.
*}

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


subsection {* @{text UNION} -- basic rules for generalized union *}

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


subsection {* The empty set *}

text {*
  Proving that the empty set has no elements is a bit tricky.
  We first show that the set @{term "{x \<in> {} : FALSE}"} is empty
  and then use the foundation axiom to show that it equals the
  empty set.
*}

lemma emptysetEmpty: "a \<notin> {}"
proof
  assume a: "a \<in> {}"
  let ?empty = "{ x \<in> {} : FALSE }"
  from foundation[where A="?empty"]
  have "{} = ?empty" by blast
  from this a have "a \<in> ?empty" by (rule subst)
  thus "FALSE" by blast
qed

text {* @{text "a \<in> {} \<Longrightarrow> P"} *}
lemmas emptyE [elim!] = emptysetEmpty[THEN notE, standard]

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

text {* Complete critical pairs *}
lemmas nonEmpty' [simp] = nonEmpty[simplified]
-- {* @{text "((A = {}) = FALSE) = (\<exists>x : x \<in> A)"},
      @{text "(({} = A) = FALSE) = (\<exists>x : x \<in> A)"} *}

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


subsection {* @{text SUBSET} -- the powerset operator *}

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

lemmas emptySUBSET = emptySubset[THEN SUBSETI, standard] -- {* @{term "{} \<in> SUBSET A"} *}
lemmas selfSUBSET = subsetRefl[THEN SUBSETI, standard] -- {* @{term "A \<in> SUBSET A"} *}


subsection {* @{text INTER} -- basic rules for generalized intersection *}

text {*
  Generalized intersection is not officially part of \tlaplus{} but can
  easily be defined as above. Observe that the rules are not exactly
  dual to those for @{text UNION} because the intersection of the
  empty set is defined to be the empty set.
*}

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


subsection {* Binary union, intersection, and difference: basic rules *}

text {*
  We begin by proving some lemmas about the auxiliary pairing operator
  @{text upair}. None of these theorems is active by default, as the
  operator is not part of \tlaplus{} and should not occur in actual reasoning.
  The dependencies between these operators are quite tricky, therefore
  the order of the first few lemmas in this section is tightly constrained.
*}

lemma upairE:
  assumes "x \<in> upair(a,b)" and "x=a \<Longrightarrow> P" and "x=b \<Longrightarrow> P"
  shows "P"
using assms by (auto simp: upair_def)

lemma cupE [elim!]:
  assumes "x \<in> A \<union> B" and "x \<in> A \<Longrightarrow> P" and "x \<in> B \<Longrightarrow> P"
  shows "P"
using assms by (auto simp: cup_def elim: upairE)

lemma upairI1: "a \<in> upair(a,b)"
by (auto simp: upair_def)

lemma singleton_iff [simp]: "(a \<in> {b}) = (a = b)"
proof auto
  assume a: "a \<in> {b}"
  thus "a = b"
    by (auto simp: addElt_def elim: upairE)
next
  show "b \<in> {b}"
    by (auto simp: addElt_def cup_def intro: upairI1)
qed

lemma singletonI (*[intro!]*): "a \<in> {a}"
by simp

lemma upairI2: "b \<in> upair(a,b)"
by (auto simp: upair_def)

lemma upair_iff: "(c \<in> upair(a,b)) = (c=a \<or> c=b)"
by (blast intro: upairI1 upairI2 elim: upairE)

lemma cupI1: 
  assumes "a \<in> A"
  shows "a \<in> A \<union> B"
using assms by (auto simp: cup_def upair_iff)

lemma cupI2:
  assumes "a \<in> B"
  shows "a \<in> A \<union> B"
using assms by (auto simp: cup_def upair_iff)

lemma cup_iff [simp]: "(c \<in> A \<union> B) = (c \<in> A \<or> c \<in> B)"
by (auto simp: cup_def upair_iff)

lemma cupCI [intro!]:
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

-- {* Adding the two following lemmas to the simpset breaks proofs. *}
lemma addEltEqual_iff: "(addElt(a,A) = S) = (a \<in> S \<and> A \<subseteq> S \<and> S \<subseteq> addElt(a,A))"
by blast

lemma equalAddElt_iff: "(S = addElt(a,A)) = (a \<in> S \<and> A \<subseteq> S \<and> S \<subseteq> addElt(a,A))"
by blast

lemma addEltEqualAddElt:
  "(addElt(a,A) = addElt(b,B)) = 
   (a \<in> addElt(b,B) \<and> A \<subseteq> addElt(b,B) \<and> b \<in> addElt(a,A) \<and> B \<subseteq> addElt(a,A))"
by (auto simp: addEltEqual_iff)

lemma cap_iff [simp]: "(c \<in> A \<inter> B) = (c \<in> A \<and> c \<in> B)"
by (simp add: cap_def)

lemma capI [intro!]:
  assumes "c \<in> A" and "c \<in> B"
  shows "c \<in> A \<inter> B"
using assms by simp

lemma capD1:
  assumes "c \<in> A \<inter> B"
  shows "c \<in> A"
using assms by simp

lemma capD2:
  assumes "c \<in> A \<inter> B"
  shows "c \<in> B"
using assms by simp

lemma capE [elim!]:
  assumes "c \<in> A \<inter> B" and "\<lbrakk> c \<in> A; c \<in> B \<rbrakk> \<Longrightarrow> P"
  shows "P"
using assms by simp

lemma diff_iff [simp]: "(c \<in> A \<setminus> B) = (c \<in> A \<and> c \<notin> B)"
by (simp add: diff_def)

lemma diffI [intro!]:
  assumes "c \<in> A" and "c \<notin> B"
  shows "c \<in> A \<setminus> B"
using assms by simp

lemma diffD1:
  assumes "c \<in> A \<setminus> B"
  shows "c \<in> A"
using assms by simp

lemma diffD2:
  assumes "c \<in> A \<setminus> B"
  shows "c \<notin> B"
using assms by simp

lemma diffE [elim!]:
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


subsection {* Consequences of the foundation axiom *}

lemma inAsym:
  assumes hyps: "a \<in> b" "\<not>P \<Longrightarrow> b \<in> a"
  shows "P"
proof (rule contradiction)
  assume "\<not>P"
  with foundation[where A="{a,b}"] hyps show "FALSE" by blast
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


subsection {* Miniscoping of bounded quantifiers *}

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

lemma bAllCup [simp]:
  "(\<forall>x \<in> A \<union> B : P(x)) = ((\<forall>x\<in>A : P(x)) \<and> (\<forall>x\<in>B : P(x)))"
by blast

lemma bAllCap [simp]:
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

-- {* completing critical pairs for negated assumption *}
lemma notbQuant' [simp]:
  "\<And>P. ((\<forall>x\<in>A : P(x)) = FALSE) = (\<exists>x\<in>A : \<not>P(x))"
  "\<And>P. ((\<exists>x\<in>A : P(x)) = FALSE) = (\<forall>x\<in>A : \<not>P(x))"
by (auto simp: miniscope_bAll[simplified] miniscope_bEx[simplified])

lemma bExistsCup [simp]:
  "(\<exists>x \<in> A \<union> B : P(x)) = ((\<exists>x\<in>A : P(x)) \<or> (\<exists>x\<in>B : P(x)))"
by blast

lemma bExistsCap [simp]:
  "(\<exists>x \<in> A \<inter> B : P(x)) = (\<exists>x\<in>A : x \<in> B \<and> P(x))"
by blast

lemma bQuant_distribs: -- {* not active by default *}
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


subsection {* Simplification of set comprehensions *}

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

text {* The following are not active by default. *}

lemma comprehensionDistribs:
  "\<And>e. { e(x) : x \<in> A \<union> B } = {e(x) : x\<in>A} \<union> {e(x) : x\<in>B}"
  "\<And>P. { x \<in> A \<union> B : P(x) } = {x\<in>A : P(x)} \<union> {x\<in>B : P(x)}"
  -- {* @{text setOfAll} and intersection or difference do not distribute *}
  "\<And>P. { x \<in> A \<inter> B : P(x) } = {x\<in>A : P(x)} \<inter> {x\<in>B : P(x)}"
  "\<And>P. { x \<in> A \<setminus> B : P(x) } = {x\<in>A : P(x)} \<setminus> {x\<in>B : P(x)}"
by (blast+)


subsection {* Binary union, intersection, and difference: inclusions and equalities *}

text {*
  The following list contains many simple facts about set theory.
  Only the most trivial of these are included in the default set
  of rewriting rules.
*}

lemma addEltCommute: "addElt(a, addElt(b, C)) = addElt(b, addElt(a, C))"
by blast

lemma addEltAbsorb: "a \<in> A \<Longrightarrow> addElt(a,A) = A"
by blast

lemma addEltTwice: "addElt(a, addElt(a, A)) = addElt(a, A)"
by blast

lemma capAddEltLeft: "addElt(a,B) \<inter> C = (IF a \<in> C THEN addElt(a, B \<inter> C) ELSE B \<inter> C)"
by (blast intro: condI elim: condE)

lemma capAddEltRight: "C \<inter> addElt(a,B) = (IF a \<in> C THEN addElt(a, C \<inter> B) ELSE C \<inter> B)"
by (blast intro: condI elim: condE)

lemma addEltCap: "addElt(a, B \<inter> C) = addElt(a,B) \<inter> addElt(a,C)"
by blast

lemma diffAddEltLeft: "addElt(a,B) \<setminus> C = (IF a \<in> C THEN B \<setminus> C ELSE addElt(a, B \<setminus> C))"
by (blast intro: condI elim: condE)

lemma capSubset: "(C \<subseteq> A \<inter> B) = (C \<subseteq> A \<and> C \<subseteq> B)"
by blast

lemma capLB1: "A \<inter> B \<subseteq> A"
by blast

lemma capLB2: "A \<inter> B \<subseteq> B"
by blast

lemma capGLB:
  assumes "C \<subseteq> A" and "C \<subseteq> B"
  shows "C \<subseteq> A \<inter> B"
using assms by blast

lemma capEmpty [simp]:
  "A \<inter> {} = {}"
  "{} \<inter> A = {}"
by blast+

lemma capAbsorb [simp]: "A \<inter> A = A"
by blast

lemma capLeftAbsorb: "A \<inter> (A \<inter> B) = A \<inter> B"
by blast

lemma capCommute: "A \<inter> B = B \<inter> A"
by blast

lemma capLeftCommute: "A \<inter> (B \<inter> C) = B \<inter> (A \<inter> C)"
by blast

lemma capAssoc: "(A \<inter> B) \<inter> C = A \<inter> (B \<inter> C)"
by blast

text {* Intersection is an AC operator: can be added to simp where appropriate *}
lemmas capAC = capAssoc capCommute capLeftCommute capLeftAbsorb

lemma subsetOfCap: "{x\<in>A : P(x)} \<inter> B = {x \<in> A \<inter> B : P(x)}"
by blast

lemma capSubsetOf:
  "B \<inter> {x\<in>A : P(x)} = {x \<in> B\<inter>A : P(x)}"
by blast

lemma subsetOfDisj:
  "{x\<in>A : P(x) \<or> Q(x)} = {x\<in>A : P(x)} \<union> {x\<in>A : Q(x)}"
by blast

lemma subsetOfConj:
  "{x\<in>A : P(x) \<and> Q(x)} = {x\<in>A : P(x)} \<inter> {x\<in>A : Q(x)}"
by blast

lemma subsetCup: "(A \<union> B \<subseteq> C) = (A \<subseteq> C \<and> B \<subseteq> C)"
by blast

lemma cupUB1: "A \<subseteq> A \<union> B"
by blast

lemma cupUB2: "B \<subseteq> A \<union> B"
by blast

lemma cupLUB:
  assumes "A \<subseteq> C" and "B \<subseteq> C"
  shows "A \<union> B \<subseteq> C"
using assms by blast

lemma cupEmpty [simp]:
  "A \<union> {} = A"
  "{} \<union> A = A"
by blast+

lemma cupAddEltLeft: "addElt(a,B) \<union> C = addElt(a, B \<union> C)"
by blast

lemma cupAddEltRight: "C \<union> addElt(a,B) = addElt(a, C \<union> B)"
by blast

lemma addEltCup: "addElt(a, B \<union> C) = addElt(a,B) \<union> addElt(a,C)"
by blast

lemma cupAbsorb [simp]: "A \<union> A = A"
by blast

lemma cupLeftAbsorb: "A \<union> (A \<union> B) = A \<union> B"
by blast

lemma cupCommute: "A \<union> B = B \<union> A"
by blast

lemma cupLeftCommute: "A \<union> (B \<union> C) = B \<union> (A \<union> C)"
by blast

lemma cupAssoc: "(A \<union> B) \<union> C = A \<union> (B \<union> C)"
by blast

text {* Union is an AC operator: can be added to simp where appropriate *}
lemmas cupAC = cupAssoc cupCommute cupLeftCommute cupLeftAbsorb

text {* Lemmas useful for simplifying enumerated sets are active by default *}
lemmas enumeratedSetSimps [simp] = 
  addEltSubset_iff addEltEqualAddElt addEltCommute addEltTwice 
  capAddEltLeft capAddEltRight cupAddEltLeft cupAddEltRight diffAddEltLeft

lemma cupEqualEmpty [simp]: "(A \<union> B = {}) = (A = {} \<and> B = {})"
by blast

lemma capCupDistrib: "A \<inter> (B \<union> C) = (A \<inter> B) \<union> (A \<inter> C)"
by blast

lemma cupCapDistrib: "A \<union> (B \<inter> C) = (A \<union> B) \<inter> (A \<union> C)"
by blast

lemma diffSubset: "A \<setminus> B \<subseteq> A"
by blast

lemma subsetDiff:
  assumes "C \<subseteq> A" and "C \<inter> B = {}"
  shows "C \<subseteq> A \<setminus> B"
using assms by blast

lemma diffSelf [simp]: "A \<setminus> A = {}"
by blast

lemma diffDisjoint:
  assumes "A \<inter> B = {}"
  shows "A \<setminus> B = A"
using assms by blast

lemma emptyDiff [simp]: "{} \<setminus> A = {}"
by blast

lemma diffAddElt: "A \<setminus> addElt(a,B) = (A \<setminus> B) \<setminus> {a}"
by blast

lemma cupDiffSelf: "A \<union> (B \<setminus> A) = A \<union> B"
by blast

lemma diffCupLeft: "(A \<union> B) \<setminus> C = (A \<setminus> C) \<union> (B \<setminus> C)"
by blast

lemma diffCupRight: "A \<setminus> (B \<union> C) = (A \<setminus> B) \<inter> (A \<setminus> C)"
by blast

lemma cupDiffLeft: "(A \<setminus> B) \<union> C = (A \<union> C) \<setminus> (A \<inter> (B \<setminus> C))"
by blast

lemma cupDiffRight: "C \<union> (A \<setminus> B) = (C \<union> A) \<setminus> (A \<inter> (B \<setminus> C))"
by blast

lemma diffCapLeft: "(A \<inter> B) \<setminus> C = A \<inter> (B \<setminus> C)"
by blast

lemma diffCapRight: "A \<setminus> (B \<inter> C) = (A \<setminus> B) \<union> (A \<setminus> C)"
by blast

lemma capDiffLeft: "(A \<setminus> B) \<inter> C = (A \<inter> C) \<setminus> B"
by blast

lemma capDiffRight: "C \<inter> (A \<setminus> B) = (C \<inter> A) \<setminus> B"
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
by (blast+)


subsection {* Generalized union: inclusions and equalities *}

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

lemma UNIONCupDistrib: "UNION (A \<union> B) = UNION A \<union> UNION B"
by blast

lemma UNIONCap: "UNION (A \<inter> B) \<subseteq> UNION A \<inter> UNION B"
by blast

lemma UNIONDisjoint: "((UNION A) \<inter> C = {}) = (\<forall>B\<in>A : B \<inter> C = {})"
by blast

lemma capUNION: "(UNION A) \<inter> B = UNION { C \<inter> B : C \<in> A }"
by blast

lemma diffUNIONLeft: "(UNION A) \<setminus> B = UNION { C \<setminus> B : C \<in> A }"
by blast

lemma UNION_mono:
  assumes "A \<subseteq> B"
  shows "UNION A \<subseteq> UNION B"
using assms by blast


subsection {* Generalized intersection: inclusions and equalities *}


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

lemma INTERCupDistrib:
  assumes "A \<noteq> {}" and "B \<noteq> {}"
  shows "INTER (A \<union> B) = INTER A \<inter> INTER B"
using assms by auto

lemma capINTER: "(INTER A) \<inter> B \<subseteq> INTER {C \<inter> B : C \<in> A}"
by blast

lemma cupINTER:
  assumes "A \<noteq> {}"
  shows "(INTER A) \<union> B = INTER {C \<union> B : C \<in> A}"
using assms by auto

lemma diffINTERLeft: "(INTER A) \<setminus> B = INTER {C \<setminus> B : C \<in> A}"
by auto

lemma diffINTERRight:
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


subsection {* Powerset: inclusions and equalities *}

lemma SUBSETEmpty [simp]: "SUBSET {} = { {} }"
by blast

lemma SUBSETAddElt:
  "SUBSET addElt(a,A) = SUBSET A \<union> {addElt(a,X) : X \<in> SUBSET A}"
by (rule setEqualI, auto)

lemma cupSUBSET: "(SUBSET A) \<union> (SUBSET B) \<subseteq> SUBSET (A \<union> B)"
by blast

lemma UNION_SUBSET [simp]: "UNION (SUBSET A) = A"
by blast

lemma SUBSET_UNION: "A \<subseteq> SUBSET (UNION A)"
by blast

lemma UNION_in_SUBSET: "(UNION A \<in> SUBSET B) = (A \<in> SUBSET (SUBSET B))"
by blast

lemma SUBSETcap: "SUBSET (A \<inter> B) = SUBSET A \<inter> SUBSET B"
by blast

end
