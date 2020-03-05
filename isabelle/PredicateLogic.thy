(*  Title:      TLA+/PredicateLogic.thy
    Author:     Stephan Merz, LORIA
    Copyright (C) 2008-2011  INRIA and Microsoft Corporation
    License:    BSD
    Version:    Isabelle2011-1
    Time-stamp: <2011-10-11 17:38:37 merz>
*)

header {* First-order logic for TLA+ *}

theory PredicateLogic
imports Pure
uses
  "~~/src/Tools/misc_legacy.ML"
  "~~/src/Tools/intuitionistic.ML"
  "~~/src/Provers/splitter.ML"
  "~~/src/Provers/hypsubst.ML"
  "~~/src/Tools/atomize_elim.ML"
  "~~/src/Provers/classical.ML"
  "~~/src/Provers/blast.ML"
  "~~/src/Provers/quantifier1.ML"
  "~~/src/Provers/clasimp.ML"
  "~~/src/Tools/IsaPlanner/isand.ML" "~~/src/Tools/IsaPlanner/rw_tools.ML" "~~/src/Tools/IsaPlanner/rw_inst.ML" "~~/src/Tools/IsaPlanner/zipper.ML" "~~/src/Tools/eqsubst.ML"
  "~~/src/Tools/induct.ML"
  ("simplifier_setup.ML")
begin

declare [[ eta_contract = false ]]
(* eta contraction doesn't make much sense for first-order logics *)

text {*
  We define classical first-order logic as a basis for an encoding
  of \tlaplus{}. \tlaplus{} is untyped, to the extent that it does not
  even distinguish between terms and formulas. We therefore
  declare a single type $c$ that represents the universe of
  ``constants'' rather than introducing the traditional types $i$ and
  $o$ of first-order logic that, for example, underly Isabelle/ZF.
*}

(* First-order syntax for applications: f(x,y) instead of (f x y) *)
setup Pure_Thy.old_appl_syntax_setup

setup {* Intuitionistic.method_setup @{binding iprover} *}

typedecl c

text {*
  The following (implicit) lifting from the object to the Isabelle 
  meta level is always needed when formalizing a logic. It corresponds
  to judgments $\vdash F$ or $\models F$ in standard presentations,
  asserting that a formula is considered true (either because
  it is an assumption or because it is a theorem).
*}

judgment
  Trueprop :: "c \<Rightarrow> prop"    ("(_)" 5)

subsection {* Equality *}

text {*
  The axioms for equality are reflexivity and a rule that asserts that
  equal terms are interchangeable at the meta level (this is essential
  for setting up Isabelle's rewriting machinery). In particular, we
  can derive a substitution rule.
*}

axiomatization
  "eq" :: "c \<Rightarrow> c \<Rightarrow> c"                (infixl "=" 50)
where
  refl [intro!]:  "a = a"
and
  eq_reflection: "t = u \<Longrightarrow> t \<equiv> u"

text {*
  Left and right hand sides of definitions are equal. This is the
  converse of axiom @{thm eq_reflection}.
*}

theorem meta_to_obj_eq:
  assumes df: "t \<equiv> u"
  shows "t = u"
by (unfold df, rule refl)

theorem subst:
  assumes eq: "a = b" and p: "P(a)"
  shows "P(b)"
proof -
  from eq have ab: "a \<equiv> b"
    by (rule eq_reflection)
  from p show "P(b)"
    by (unfold ab)
qed

theorem sym [sym]:
  "a = b \<Longrightarrow> b = a"
proof (elim subst)
  show "a=a" ..
qed

theorem trans [trans]:
  "a=b \<Longrightarrow> b=c \<Longrightarrow> a=c"
by (rule subst)

theorems ssubst = sym[THEN subst]

text {*
  \textsc{let}-expressions in \tlaplus{} expressions.

  \emph{Limitation:} bindings cannot be unfolded selectively.
  Rewrite with @{text Let_def} in order to expand \emph{all} bindings
  within an expression or a context.
*}

definition
  Let :: "'b \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> 'a"
where
  "Let(b,e) \<equiv> e(b)"

nonterminal
  letbinds and letbind

syntax
  "_bind"       :: "[pttrn, 'a] => letbind"              ("(2_ ==/ _)" 10)
  ""            :: "letbind => letbinds"                 ("_")
  "_binds"      :: "[letbind, letbinds] => letbinds"     ("_/ _")
  "_Let"        :: "[letbinds, 'a] => 'a"                ("(LET (_)/ IN (_))" 10)

syntax (xsymbols)
  "_bind"       :: "[pttrn, 'a] => letbind"              ("(2_ \<equiv>/ _)" 10)
syntax (xsymbols)
  "_bind"       :: "[pttrn, 'a] => letbind"              ("(2_ \<triangleq>/ _)" 10)

translations
  "_Let( _binds(b, bs), e)" \<rightleftharpoons> "_Let(b, _Let(bs, e))"
  "LET x \<triangleq> a IN e"         \<rightleftharpoons> "CONST Let(a, (%x. e))"


subsection {* Propositional logic *}

text {*
  Propositional logic is introduced in a rather non-standard way
  by declaring constants @{text TRUE} and @{text FALSE} as well as
  conditional expressions. The Boolean connectives
  are defined such that they always return either @{text TRUE} or
  @{text FALSE}, irrespectively of their arguments. This allows us
  to prove many equational laws of propositional logic, which is
  useful for automatic reasoning based on rewriting. Note that we
  have equivalence as well as equality. The two relations agree over
  Boolean values, but equivalence may be stricter weaker than
  equality over non-Booleans.
*}

consts
  TRUE  :: "c"
  FALSE :: "c"
  cond  :: "c \<Rightarrow> c \<Rightarrow> c \<Rightarrow> c"   ("(IF (_)/ THEN (_)/ ELSE (_))" 10)

consts
  Not   :: "c \<Rightarrow> c"             ("~ _" [40] 40)
  conj  :: "c \<Rightarrow> c \<Rightarrow> c"        (infixr "&" 35)
  disj  :: "c \<Rightarrow> c \<Rightarrow> c"        (infixr "|" 30)
  imp   :: "c \<Rightarrow> c \<Rightarrow> c"        (infixr "=>" 25)
  iff   :: "c \<Rightarrow> c \<Rightarrow> c"        (infixr "<=>" 25)

abbreviation not_equal :: "c \<Rightarrow> c \<Rightarrow> c"    (infixl "~=" 50)
where "x ~= y \<equiv> ~ (x = y)"

notation (xsymbols)
    Not           ("\<not> _" [40] 40)
and conj          (infixr "\<and>" 35)
and disj          (infixr "\<or>" 30)
and imp           (infixr "\<Rightarrow>" 25)
and iff           (infixr "\<Leftrightarrow>" 25)
and not_equal     (infix "\<noteq>" 50)

notation (HTML output)
    Not           ("\<not> _" [40] 40)
and conj          (infixr "\<and>" 35)
and disj          (infixr "\<or>" 30)
and imp           (infixr "\<Rightarrow>" 25)
and iff           (infixr "\<Leftrightarrow>" 25)
and not_equal     (infix "\<noteq>" 50)

defs
  not_def:   "\<not> A \<equiv> IF A THEN FALSE ELSE TRUE"
  conj_def:  "A \<and> B \<equiv> IF A THEN (IF B THEN TRUE ELSE FALSE) ELSE FALSE"
  disj_def:  "A \<or> B \<equiv> IF A THEN TRUE ELSE IF B THEN TRUE ELSE FALSE"
  imp_def:   "A \<Rightarrow> B \<equiv> IF A THEN (IF B THEN TRUE ELSE FALSE) ELSE TRUE"
  iff_def:   "A \<Leftrightarrow> B \<equiv> (A \<Rightarrow> B) \<and> (B \<Rightarrow> A)"

text {*
  We adopt the following axioms of propositional logic:
  \begin{enumerate}
  \item $A$ is a theorem if and only if it equals @{term TRUE}.
  \item @{term FALSE} (more precisely, @{text "\<not> TRUE"}) implies anything.
  \item Conditionals are reasoned about by case distinction.
  \end{enumerate}
  We also assert that the equality predicate returns either @{term TRUE} 
  or @{term FALSE}.
*}

axiomatization where
  trueI [intro!]:   "TRUE"
and
  eqTrueI:          "A \<Longrightarrow> A = TRUE"
and
  notTrueE [elim!]: "\<not> TRUE \<Longrightarrow> A"
and
  condI:  "\<lbrakk> A \<Longrightarrow> P(t); \<not> A \<Longrightarrow> P(e) \<rbrakk> \<Longrightarrow> P(IF A THEN t ELSE e)"
and
  eqBoolean :       "x \<noteq> y \<Longrightarrow> (x=y) = FALSE"

text {*
  We now derive the standard proof rules of propositional logic.
  The first lemmas are about @{term TRUE}, @{term FALSE}, and
  conditional expressions.
*}

lemma eqTrueD:         -- {* converse of eqTrueI *}
  assumes a: "A = TRUE"
  shows "A"
by (unfold a[THEN eq_reflection], rule trueI)

text {*
  Assumption @{term TRUE} is useless and can be deleted.
*}

lemma TrueAssumption: "(TRUE \<Longrightarrow> PROP P) == PROP P"
proof
  assume h: "TRUE \<Longrightarrow> PROP P" show "PROP P"
    by (rule h, rule trueI)
next
  assume "PROP P" thus "PROP P" .
qed

lemma condT: "(IF TRUE THEN t ELSE e) = t"
proof (rule condI)
  show "t = t" ..
next
  assume "\<not> TRUE" thus "e = t" ..
qed

lemma notTrue: "(\<not> TRUE) = FALSE"
by (unfold not_def, rule condT)

theorem falseE [elim!]:
  assumes f: "FALSE"
  shows "A"
proof (rule notTrueE)
  have "FALSE = (\<not> TRUE)"
    by (rule sym[OF notTrue])
  hence r: "FALSE \<equiv> \<not> TRUE"
    by (rule eq_reflection)
  from f show "\<not> TRUE"
    by (unfold r)
qed

lemma condF: "(IF FALSE THEN t ELSE e) = e"
proof (rule condI)
  assume "FALSE" thus "t = e" ..
next
  show "e = e" ..
qed

lemma notFalse: "(\<not> FALSE) = TRUE"
by (unfold not_def, rule condF)

lemma condThen:
  assumes a: "A"
  shows "(IF A THEN t ELSE e) = t"
proof -
  from a have "A = TRUE"
    by (rule eqTrueI)
  hence r: "A \<equiv> TRUE"
    by (rule eq_reflection)
  show ?thesis
    by (unfold r, rule condT)
qed

lemma condD1 [elim 2]:
  assumes c: "IF A THEN P ELSE Q" (is ?if) and a: "A"
  shows "P"
proof (rule eqTrueD)
  from c have "?if = TRUE" by (rule eqTrueI)
  hence "TRUE = ?if" by (rule sym)
  also from a have "?if = P" by (rule condThen)
  finally show "P = TRUE" by (rule sym)
qed

lemma condElse:
  assumes na: "\<not> A"
  shows "(IF A THEN t ELSE e) = e"
proof (rule condI)
  assume "A" hence "A = TRUE"
    by (rule eqTrueI)
  hence r: "A \<equiv> TRUE"
    by (rule eq_reflection)
  from na have "\<not> TRUE"
    by (unfold r)
  thus "t = e" ..
next
  show "e = e" ..
qed

lemma condD2 [elim 2]:
  assumes c: "IF A THEN P ELSE Q" (is ?if) and a: "\<not> A"
  shows "Q"
proof (rule eqTrueD)
  from c have "?if = TRUE" by (rule eqTrueI)
  hence "TRUE = ?if" by (rule sym)
  also from a have "?if = Q" by (rule condElse)
  finally show "Q = TRUE" by (rule sym)
qed

text {*
  The following theorem shows that we have a classical logic.
*}

lemma cond_id: "(IF A THEN t ELSE t) = t"
proof (rule condI)
  show "t=t" ..
  show "t=t" ..
qed

theorem case_split:
  assumes p: "P \<Longrightarrow> Q"
  and np: "\<not> P \<Longrightarrow> Q"
  shows "Q"
proof -
  from p np have "IF P THEN Q ELSE Q" by (rule condI)
  thus "Q" by (unfold eq_reflection[OF cond_id])
qed

theorem condE:
  -- {* use conditionals in hypotheses *}
  assumes p: "P(IF A THEN t ELSE e)"
  and pos: "\<lbrakk> A; P(t) \<rbrakk> \<Longrightarrow> B"
  and neg: "\<lbrakk> \<not> A; P(e) \<rbrakk> \<Longrightarrow> B"
  shows "B"
proof (rule case_split[of "A"])
  assume a: "A"
  hence r: "IF A THEN t ELSE e \<equiv> t"
    by (unfold eq_reflection[OF condThen])
  with p have "P(t)"
    by (unfold r)
  with a show "B"
    by (rule pos)
next
  assume a: "\<not> A"
  hence r: "IF A THEN t ELSE e \<equiv> e"
    by (unfold eq_reflection[OF condElse])
  with p have "P(e)"
    by (unfold r)
  with a show "B"
    by (rule neg)
qed

text {*
  Theorems @{text "condI"} and @{text "condE"} require higher-order
  unification and are therefore unsuitable for automatic tactics
  (in particular the \texttt{blast} method). We now derive some special
  cases that can be given to these methods.
*}

-- {* @{text "\<lbrakk>A \<Longrightarrow> t; \<not>A \<Longrightarrow> e\<rbrakk> \<Longrightarrow> IF A THEN t ELSE e"} *}
lemmas cond_boolI [intro!] = condI[where P="\<lambda> Q. Q"]

lemma cond_eqLI [intro!]:
  assumes 1: "A \<Longrightarrow> t = v" and 2: "\<not>A \<Longrightarrow> u = v"
  shows "(IF A THEN t ELSE u) = v"
proof (rule condI)
  show "A \<Longrightarrow> t=v" by (rule 1)
next
  show "\<not>A \<Longrightarrow> u=v" by (rule 2)
qed

lemma cond_eqRI [intro!]:
  assumes 1: "A \<Longrightarrow> v = t" and 2: "\<not>A \<Longrightarrow> v = u"
  shows "v = (IF A THEN t ELSE u)"
proof (rule condI)
  show "A \<Longrightarrow> v = t" by (rule 1)
next
  show "\<not>A \<Longrightarrow> v = u" by (rule 2)
qed

-- {* @{text "\<lbrakk>IF A THEN t ELSE e; \<lbrakk>A;t\<rbrakk> \<Longrightarrow> B; \<lbrakk>\<not>A;e\<rbrakk> \<Longrightarrow> B\<rbrakk> \<Longrightarrow> B"} *}
lemmas cond_boolE [elim!] = condE[where P="\<lambda> Q. Q"]

lemma cond_eqLE [elim!]:
  assumes maj: "(IF A THEN t ELSE e) = u"
  and 1: "\<lbrakk> A; t=u \<rbrakk> \<Longrightarrow> B" and 2: "\<lbrakk> \<not>A; e=u \<rbrakk> \<Longrightarrow> B"
  shows "B"
using maj
proof (rule condE)
  show "\<lbrakk> A; t=u \<rbrakk> \<Longrightarrow> B" by (rule 1)
next
  show "\<lbrakk> \<not>A; e=u \<rbrakk> \<Longrightarrow> B" by (rule 2)
qed

lemma cond_eqRE [elim!]:
  assumes maj: "u = (IF A THEN t ELSE e)"
  and 1: "\<lbrakk> A; u=t \<rbrakk> \<Longrightarrow> B" and 2: "\<lbrakk> \<not>A; u=e \<rbrakk> \<Longrightarrow> B"
  shows "B"
using maj
proof (rule condE)
  show "\<lbrakk> A; u=t \<rbrakk> \<Longrightarrow> B" by (rule 1)
next
  show "\<lbrakk> \<not>A; u=e \<rbrakk> \<Longrightarrow> B" by (rule 2)
qed

text {*
  Derive standard propositional proof rules, based on the
  operator definitions in terms of @{text "IF _ THEN _ ELSE _"}.
*}

theorem notI [intro!]:
  assumes hyp: "A \<Longrightarrow> FALSE"
  shows "\<not> A"
proof (unfold not_def, rule condI)
  assume "A" thus "FALSE"
    by (rule hyp)
next
  show "TRUE" ..
qed

lemma false_neq_true: "FALSE \<noteq> TRUE"
proof
  assume "FALSE = TRUE"
  thus "FALSE" by (rule eqTrueD)
qed

lemma false_eq_trueE:
  assumes ft: "FALSE = TRUE"
  shows "B"
proof (rule falseE)
  from ft show "FALSE"
    by (rule eqTrueD)
qed

lemmas true_eq_falseE = sym[THEN false_eq_trueE]

lemma notFalseI: "\<not> FALSE"
by iprover

lemma A_then_notA_false:
  assumes a: "A"
  shows "(\<not> A) = FALSE"
using a
by (unfold not_def, rule condThen)

text {*
  The following is an alternative introduction rule for negation
  that is useful when we know that @{text A} is Boolean.
*}

lemma eq_false_not:
  assumes a: "A = FALSE"
  shows "\<not> A"
proof (rule eqTrueD)
  show "(\<not> A) = TRUE" by (unfold eq_reflection[OF a], rule notFalse)
qed

text {*
  Note that we do not have @{text "\<not> A \<Longrightarrow> A = FALSE"}: this
  is true only for Booleans, not for arbitrary values. However,
  we have the following theorem, which is just the ordinary
  elimination rule for negation.
*}

theorem notE:
  assumes notA: "\<not> A" and a: "A"
  shows "B"
proof (rule false_eq_trueE)
  from a have "(\<not> A) = FALSE"
    by (rule A_then_notA_false)
  hence "FALSE = (\<not> A)"
    by (rule sym)
  also from notA have "(\<not> A) = TRUE"
    by (rule eqTrueI)
  finally show "FALSE = TRUE" .
qed

theorem notE' [elim 2]:
  assumes notA: "\<not> A" and r: "\<not> A \<Longrightarrow> A"
  shows "B"
using notA
proof (rule notE)
  from notA show "A" by (rule r)
qed

lemma notnotI:
  assumes a: "A"
  shows "\<not>\<not> A"
proof
  assume "\<not> A"
  from this a show "FALSE" ..
qed

theorem not_sym [sym]:
  assumes hyp: "a \<noteq> b"
  shows "b \<noteq> a"
proof
  assume "b = a"
  hence "a = b" ..
  with hyp show "FALSE" ..
qed

text {*
  Some derived proof rules of classical logic.
*}

theorem contradiction:
  assumes hyp: "\<not> A \<Longrightarrow> FALSE"
  shows "A"
proof (rule case_split[of "A"])
  assume "\<not> A" hence "FALSE"
    by (rule hyp)
  thus "A" ..
qed -- {* the other case is trivial *}

theorem classical:
  assumes c: "\<not> A \<Longrightarrow> A"
  shows "A"
proof (rule contradiction)
  assume na: "\<not> A" hence "A" by (rule c)
  with na show "FALSE" ..
qed

theorem swap:
  assumes a: "\<not> A" and r: "\<not> B \<Longrightarrow> A"
  shows "B"
proof (rule contradiction)
  assume "\<not> B"
  with r have "A" .
  with a show "FALSE" ..
qed

theorem notnotD [dest]:
  assumes nn: "\<not>\<not> A" shows "A"
proof (rule contradiction)
  assume "\<not> A"
  with nn show "FALSE" ..
qed

text {*
  Note again: @{text A} and @{text "\<not>\<not> A"} are inter-derivable
  (and hence equivalent), but not equal!
*}

lemma contrapos:
  assumes b: "\<not> B" and ab: "A \<Longrightarrow> B"
  shows "\<not> A"
proof
  assume "A"
  hence "B" by (rule ab)
  with b show "FALSE" ..
qed

lemma contrapos2:
  assumes b: "B" and ab: "\<not>A \<Longrightarrow> \<not>B"
  shows "A"
proof -
  have "\<not>\<not> A"
  proof
    assume "\<not> A"
    hence "\<not> B" by (rule ab)
    from this b show "FALSE" ..
  qed
  thus "A" ..
qed

theorem conjI [intro!]:
  assumes a: "A" and b: "B"
  shows "A \<and> B"
proof (rule eqTrueD)
  from a have "(A \<and> B) = (IF B THEN TRUE ELSE FALSE)"
    by (unfold conj_def, rule condThen)
  also from b have "\<dots> = TRUE" by (rule condThen)
  finally show "(A \<and> B) = TRUE" .
qed

theorem conjD1:
  assumes ab: "A \<and> B"
  shows "A"
proof (rule contradiction)
  assume "\<not> A"
  with ab show "FALSE"
    by (unfold conj_def, elim condD2)
qed

theorem conjD2:
  assumes ab: "A \<and> B"
  shows "B"
proof (rule contradiction)
  assume b: "\<not> B"
  from ab have "A" by (rule conjD1)
  with ab have "IF B THEN TRUE ELSE FALSE" 
    by (unfold conj_def, elim condD1)
  with b show "FALSE" by (elim condD2)
qed

theorem conjE [elim!]:
  assumes ab: "A \<and> B" and c: "A \<Longrightarrow> B \<Longrightarrow> C"
  shows "C"
proof (rule c)
  from ab show "A" by (rule conjD1)
  from ab show "B" by (rule conjD2)
qed

text {* Disjunction *}

theorem disjI1 [elim]:
  assumes a: "A"
  shows "A \<or> B"
proof (unfold disj_def, rule)
  show "TRUE" ..
next
  assume "\<not> A"
  from this a show "IF B THEN TRUE ELSE FALSE" ..
qed

theorem disjI2 [elim]:
  assumes b: "B"
  shows "A \<or> B"
proof (unfold disj_def, rule)
  show "TRUE" ..
next
  show "IF B THEN TRUE ELSE FALSE"
  proof
    show "TRUE" ..
  next
    assume "\<not> B"
    from this b show "FALSE" ..
  qed
qed

theorem disjI [intro!]: -- {* classical introduction rule *}
  assumes ab: "\<not> A \<Longrightarrow> B"
  shows "A \<or> B"
proof (unfold disj_def, rule)
  show "TRUE" ..
next
  assume "\<not> A"
  hence b: "B" by (rule ab)
  show "IF B THEN TRUE ELSE FALSE"
  proof
    show "TRUE" ..
  next
    assume "\<not> B"
    from this b show "FALSE"..
  qed
qed

theorem disjE [elim!]:
  assumes ab: "A \<or> B" and ac: "A \<Longrightarrow> C" and bc: "B \<Longrightarrow> C"
  shows "C"
proof (rule case_split[where P=A])
  assume "A" thus "C" by (rule ac)
next
  assume nota: "\<not> A"
  have "B"
  proof (rule contradiction)
    assume notb: "\<not> B"
    from nota have "IF B THEN TRUE ELSE FALSE"
      by (rule ab[unfolded disj_def, THEN condD2])
    from this notb show "FALSE" by (rule condD2)
  qed
  thus "C" by (rule bc)
qed

theorem excluded_middle: "A \<or> \<not> A"
proof
  assume "\<not> A" thus "\<not> A" .
qed

text {* Implication *}

theorem impI [intro!]:
  assumes ab: "A \<Longrightarrow> B"
  shows "A \<Rightarrow> B"
proof (unfold imp_def, rule)
  assume "A"
  hence b: "B" by (rule ab)
  show "IF B THEN TRUE ELSE FALSE"
  proof
    show "TRUE" ..
  next
    assume "\<not> B"
    from this b show "FALSE" ..
  qed
next
  show "TRUE" ..
qed

theorem mp (*[elim 2]*):
  assumes ab: "A \<Rightarrow> B" and a: "A"
  shows "B"
proof (rule contradiction)
  assume notb: "\<not> B"
  from a have "IF B THEN TRUE ELSE FALSE"
    by (rule ab[unfolded imp_def, THEN condD1])
  from this notb show "FALSE" by (rule condD2)
qed

theorem rev_mp (*[elim 2]*):
  assumes a: "A" and ab: "A \<Rightarrow> B"
  shows "B"
using ab a by (rule mp)

theorem impE:
  assumes ab: "A \<Rightarrow> B" and a: "A" and bc: "B \<Longrightarrow> C"
  shows "C"
proof -
  from ab a have "B" by (rule mp)
  thus "C" by (rule bc)
qed

theorem impCE [elim]:
  assumes ab: "A \<Rightarrow> B" and b: "B \<Longrightarrow> P" and a: "\<not> A \<Longrightarrow> P"
  shows "P"
proof (rule classical)
  assume contra: "\<not> P"
  have "A"
  proof (rule contradiction)
    assume "\<not> A" hence "P" by (rule a)
    with contra show "FALSE" ..
  qed
  with ab have "B" by (rule mp)
  thus "P" by (rule b)
qed

theorem impCE':  (* used for classical prover *)
  assumes ab: "A \<Rightarrow> B" and a: "\<not>C \<Longrightarrow> A" and b: "B \<Longrightarrow> C"
  shows "C"
proof (rule classical)
  assume "\<not>C"
  hence "A" by (rule a)
  with ab have "B" by (rule mp)
  thus "C" by (rule b)
qed

text {* Equivalence *}

theorem iffI [intro!]:
  assumes ab: "A \<Longrightarrow> B" and ba: "B \<Longrightarrow> A"
  shows "A \<Leftrightarrow> B"
proof (unfold iff_def, rule)
  from ab show "A \<Rightarrow> B" ..
  from ba show "B \<Rightarrow> A" ..
qed

lemma iff_refl: "A \<Leftrightarrow> A"
by iprover

lemma meta_eq_to_iff:
  assumes mt: "A \<equiv> B" shows "A \<Leftrightarrow> B"
by (unfold mt, rule iff_refl)

lemma eqThenIff:
  assumes eq: "A = B" shows "A \<Leftrightarrow> B"
proof -
  from eq have "A \<equiv> B" by (rule eq_reflection)
  thus ?thesis by (rule meta_eq_to_iff)
qed

theorem iffD1 [elim 2]:
  assumes ab: "A \<Leftrightarrow> B" and a: "A"
  shows "B"
using ab
proof (unfold iff_def, elim conjE)
  assume "A \<Rightarrow> B"
  from this a show "B" by (rule mp)
qed

theorem iffD2 [elim 2]:
  assumes ab: "A \<Leftrightarrow> B" and b: "B"
  shows "A"
using ab
proof (unfold iff_def, elim conjE)
  assume "B \<Rightarrow> A"
  from this b show "A" by (rule mp)
qed

theorem iffE:
  assumes ab: "A \<Leftrightarrow> B" and r: "\<lbrakk> A \<Rightarrow> B; B \<Rightarrow> A \<rbrakk> \<Longrightarrow> C"
  shows C
proof (rule r)
  from ab show "A \<Rightarrow> B" by (unfold iff_def, elim conjE)
  from ab show "B \<Rightarrow> A" by (unfold iff_def, elim conjE)
qed

theorem iffCE [elim!]:
  assumes ab: "A \<Leftrightarrow> B" 
  and pos: "\<lbrakk>A; B\<rbrakk> \<Longrightarrow> C" and neg: "\<lbrakk>\<not> A; \<not> B\<rbrakk> \<Longrightarrow> C"
  shows "C"
proof (rule case_split[of A])
  assume a: A
  with ab have "B" ..
  with a show "C" by (rule pos)
next
  assume a: "\<not> A"
  have "\<not> B"
  proof
    assume "B"
    with ab have "A" ..
    with a show "FALSE" ..
  qed
  with a show "C" by (rule neg)
qed

theorem iff_trans [trans]:
  assumes ab: "A \<Leftrightarrow> B" and bc: "B \<Leftrightarrow> C"
  shows "A \<Leftrightarrow> C"
proof
  assume "A"
  with ab have "B" ..
  with bc show "C" ..
next
  assume "C"
  with bc have "B" ..
  with ab show "A" ..
qed


subsection {* Predicate Logic *}

text {*
  We take Hilbert's $\varepsilon$ as the basic binder and define the
  other quantifiers as derived connectives. Again, we make sure
  that quantified formulas evaluate to @{term TRUE} or @{term FALSE}.

  Observe that quantification is allowed at arbitrary types. Although
  \tlaplus{} formulas are purely first-order formulas, and may only
  contain quantification over values of type @{text c}, we sometimes
  need to reason about formula schemas, for example for induction,
  and automatic provers such as \texttt{blast} rely on reflection to
  the object level for reasoning about meta-connectives, which would
  not be possible with purely first-order quantification.
*}

consts
  Choice    :: "('a \<Rightarrow> c) \<Rightarrow> 'a"
  Ex        :: "('a \<Rightarrow> c) \<Rightarrow> c"
  All       :: "('a \<Rightarrow> c) \<Rightarrow> c"

text {* Concrete syntax: several variables as in @{text "\<forall>x,y : P(x,y)"}. *}

nonterminal cidts  (* comma-separated idt's *)

syntax
  ""         ::  "idt \<Rightarrow> cidts"           ("_"  [100] 100)
  "@cidts"   ::  "[idt, cidts] \<Rightarrow> cidts"  ("_,/ _" [100,100] 100)

syntax
  (* BEWARE: choosing several values in sequence is not equivalent to
     choosing a tuple of values simultaneously. To avoid confusion, we
     do not allow several variables in a CHOOSE. *)
  "@Choice" :: "[idt, c] \<Rightarrow> c"         ("(3CHOOSE _ :/ _)" [100,10] 10)
  "@Ex"     :: "[cidts, c] \<Rightarrow> c"       ("(3\\E _ :/ _)" [100,10] 10)
  "@All"    :: "[cidts, c] \<Rightarrow> c"       ("(3\\A _ :/ _)" [100,10] 10)
syntax (xsymbols)
  "@Ex"     :: "[cidts, c] \<Rightarrow> c"       ("(3\<exists>_ :/ _)" [100, 10] 10)
  "@All"    :: "[cidts, c] \<Rightarrow> c"       ("(3\<forall>_ :/ _)" [100, 10] 10)
translations
  "CHOOSE x: P"      \<rightleftharpoons>  "CONST Choice(\<lambda>x. P)"
  (* separate parse and print translations for nested quantifiers because 
     they operate in opposite directions *)
  "\<exists>x,xs : P"        \<rightharpoonup>  "CONST Ex(\<lambda>x. \<exists>xs : P)"
(** FIXME: print translation doesn't work correctly: 
    will print \<exists>x : \<forall>y: P as \<exists>x, y : P -- why ??? **)
(*  "\<exists>x,xs : P"        \<leftharpoondown>  "\<exists>x : Ex(\<lambda>xs. P)" *)
  "\<exists>x : P"           \<rightleftharpoons>  "CONST Ex(\<lambda>x. P)"
  "\<forall>x,xs : P"        \<rightharpoonup>  "CONST All(\<lambda>x. \<forall>xs : P)"
(*  "\<forall>x,xs : P"        \<leftharpoondown>  "\<forall>x : All(\<lambda>xs. P)" *)
  "\<forall>x : P"           \<rightleftharpoons>  "CONST All(\<lambda>x. P)"

(* Declare the two following axioms separately, otherwise the
   type checker infers the same type for P, and the type of P in
   the second axiom must be "c => c" whereas it can be "'a => c"
   in the first one. *)

axiomatization where
  chooseI: "P(t) \<Longrightarrow> P(CHOOSE x: P(x))"

axiomatization where
  choose_det : "(\<And>x. P(x) \<Leftrightarrow> Q(x)) \<Longrightarrow> (CHOOSE x: P(x)) = (CHOOSE x: Q(x))"

defs
  Ex_def:      "Ex(P)   \<equiv>  P(CHOOSE x : P(x) = TRUE) = TRUE"
  All_def:     "All(P)  \<equiv>  \<not>(\<exists>x : \<not> P(x))"

text {*
  We introduce two constants @{text arbitrary} and @{text default}
  that correspond to unconstrained and overconstrained choice,
  respectively.
*}

definition arbitrary::c where
  "arbitrary \<equiv> CHOOSE x : TRUE"

definition default::c where
  "default \<equiv> CHOOSE x : FALSE"

theorem exI [intro]:
  assumes hyp: "P(t)"
  shows "\<exists>x : P(x)"
proof -
  from hyp have "P(t) = TRUE" by (rule eqTrueI)
  thus ?thesis by (unfold Ex_def, rule chooseI)
qed

theorem exE [elim!]:
  assumes hyp: "\<exists>x : P(x)" and r: "\<And>x. P(x) \<Longrightarrow> Q"
  shows "Q"
proof -
  from hyp have "P(CHOOSE x : P(x) = TRUE) = TRUE" by (unfold Ex_def)
  hence "P(CHOOSE x : P(x) = TRUE)" by (rule eqTrueD)
  thus "Q" by (rule r)
qed

theorem allI [intro!]:
  assumes hyp: "\<And>x. P(x)"
  shows "\<forall>x : P(x)"
proof (unfold All_def, rule)
  assume "\<exists>x : \<not> P(x)"
  then obtain x where "\<not> P(x)" ..
  from this hyp show "FALSE" by (rule notE)
qed

theorem spec:
  assumes hyp: "\<forall>x : P(x)"
  shows "P(x)"
proof (rule contradiction)
  assume contra: "\<not> P(x)"
  hence "\<exists>x : \<not> P(x)" by (rule exI)
  with hyp show "FALSE" by (unfold All_def, elim notE)
qed

theorem allE [elim]:
  assumes hyp: "\<forall>x : P(x)" and r: "P(x) \<Longrightarrow> Q"
  shows "Q"
proof (rule r)
  from hyp show "P(x)" by (rule spec)
qed

theorem all_dupE:
  assumes hyp: "\<forall>x : P(x)" and r: "\<lbrakk> P(x); \<forall>x : P(x) \<rbrakk> \<Longrightarrow> Q"
  shows "Q"
proof (rule r)
  from hyp show "P(x)" by (rule spec)
qed (rule hyp)

lemma chooseI_ex: "\<exists>x : P(x) \<Longrightarrow> P(CHOOSE x : P(x))"
by (elim exE chooseI)

lemma chooseI2: 
  assumes p: "P(a)" and q:"\<And>x. P(x) \<Longrightarrow> Q(x)"
  shows "Q(CHOOSE x : P(x))"
proof (rule q)
  from p show "P(CHOOSE x : P(x))" by (rule chooseI)
qed

lemma chooseI2_ex: 
  assumes p: "\<exists>x : P(x)" and q:"\<And>x. P(x) \<Longrightarrow> Q(x)"
  shows "Q(CHOOSE x : P(x))"
proof (rule q)
  from p show "P(CHOOSE x : P(x))" by (rule chooseI_ex)
qed

lemma choose_equality [intro]:
  assumes "P(t)" and "\<And>x. P(x) \<Longrightarrow> x=a"
  shows "(CHOOSE x : P(x)) = a"
using assms by (rule chooseI2[where Q="\<lambda>x. x=a"])

lemmas choose_equality' = sym[OF choose_equality, standard, intro]

text {*
  Skolemization rule: note that the existential quantifier in the conclusion
  introduces an operator (of type @{text "c \<Rightarrow> c"}), not a value; second-order
  quantification is necessary here.
*}

lemma skolemI:
  assumes h: "\<forall>x : \<exists>y: P(x,y)" shows "\<exists>f : \<forall>x : P(x, f(x))"
proof -
  have "\<forall>x : P(x, CHOOSE y : P(x,y))"
  proof
    fix x
    from h[THEN spec] show "P(x, CHOOSE y: P(x,y))" by (rule chooseI_ex)
  qed
  thus ?thesis by iprover
qed

lemma skolem:
  "(\<forall>x : \<exists>y : P(x,y)) \<Leftrightarrow> (\<exists>f : \<forall>x : P(x, f(x)))"  (is "?lhs \<Leftrightarrow> ?rhs")
proof
  assume ?lhs thus ?rhs by (rule skolemI)
next
  assume ?rhs thus ?lhs by iprover
qed


subsection {* Setting up the automatic proof methods *}

subsubsection {* Reflection of meta-level to object-level *}

text {*
  Our next goal is to getting Isabelle's automated tactics to work
  for \tlaplus{}. We follow the setup chosen for Isabelle/HOL as far
  as it applies to \tlaplus{}. The following lemmas, when used as
  rewrite rules, replace meta- by object-level connectives.
*}

lemma atomize_all [atomize]: "(\<And>x. P(x)) \<equiv> Trueprop (\<forall>x : P(x))"
proof
  assume "\<And>x. P(x)" thus "\<forall>x : P(x)" ..
next
  assume "\<forall>x : P(x)" thus "\<And>x. P(x)" ..
qed

lemma atomize_imp [atomize]: "(A \<Longrightarrow> B) \<equiv> Trueprop (A \<Rightarrow> B)"
proof
  assume "A \<Longrightarrow> B" thus "A \<Rightarrow> B" ..
next
  assume "A \<Rightarrow> B" and A thus B by (rule mp)
qed

lemma atomize_not [atomize]: "(A \<Longrightarrow> FALSE) \<equiv> Trueprop(\<not>A)"
proof
  assume "A \<Longrightarrow> FALSE" thus "\<not>A" by (rule notI)
next
  assume "\<not>A" and "A" thus FALSE by (rule notE)
qed

lemma atomize_eq [atomize]: "(x \<equiv> y) \<equiv> Trueprop (x = y)"
proof
  assume 1: "x \<equiv> y"
  show "x = y" by (unfold 1, rule refl)
next
  assume "x = y"
  thus "x \<equiv> y" by (rule eq_reflection)
qed

lemma atomize_conj [atomize]: "(A &&& B) \<equiv> Trueprop (A \<and> B)"
proof
  assume conj: "A &&& B"
  show "A \<and> B"
  proof
    from conj show "A" by (rule conjunctionD1)
    from conj show "B" by (rule conjunctionD2)
  qed
next
  assume conj: "A \<and> B" 
  show "A &&& B"
  proof -
    from conj show A ..
    from conj show B ..
  qed
qed


lemmas [symmetric,rulify] = atomize_all atomize_imp
   and [symmetric,defn] = atomize_all atomize_imp atomize_eq

(** A few test cases: **

lemma tmp: "(\<And>x. P(x)) \<Longrightarrow> \<forall>x : P(x)" unfolding atomize_all .

lemma tmp2: "(\<And>P x. P(x)) \<Longrightarrow> (\<And>a::c. Q(a))" .

lemma tmp3: "\<And>a. (\<And>x. P(x)) \<Longrightarrow> P(a)" .

ML {*
  let
    val thm = @{thm tmp2}
    val rew = Object_Logic.atomize (cprop_of thm)
  in
    Raw_Simplifier.rewrite_rule [rew] thm
  end
*}

** end test cases **)

setup AtomizeElim.setup

lemma atomize_exL[atomize_elim]: "(\<And>x. P(x) \<Longrightarrow> Q) \<equiv> ((\<exists>x : P(x)) \<Longrightarrow> Q)"
by rule iprover+

lemma atomize_conjL[atomize_elim]: "(A \<Longrightarrow> B \<Longrightarrow> C) \<equiv> (A \<and> B \<Longrightarrow> C)"
by rule iprover+

lemma atomize_disjL[atomize_elim]: "((A \<Longrightarrow> C) \<Longrightarrow> (B \<Longrightarrow> C) \<Longrightarrow> C) \<equiv> ((A \<or> B \<Longrightarrow> C) \<Longrightarrow> C)"
by rule iprover+

lemma atomize_elimL[atomize_elim]: "(\<And>B. (A \<Longrightarrow> B) \<Longrightarrow> B) \<equiv> Trueprop(A)" ..


subsubsection {* Setting up the classical reasoner *}

text {*
  We now instantiate Isabelle's classical reasoner for \tlaplus{}.
  This includes methods such as \texttt{fast} and \texttt{blast}.
*}

lemma thin_refl: "\<lbrakk>x=x; PROP W\<rbrakk> \<Longrightarrow> PROP W" .

ML {*

  (* functions to take apart judgments and formulas, see
     Isabelle reference manual, section 9.3 *)
  fun dest_Trueprop (Const(@{const_name Trueprop}, _) $ P) = P
    | dest_Trueprop t = raise TERM ("dest_Trueprop", [t]);

  fun dest_eq (Const(@{const_name eq}, _) $ t $ u) = (t,u)
    | dest_eq t = raise TERM ("dest_eq", [t]);

  fun dest_imp (Const(@{const_name imp}, _) $ A $ B) = (A, B)
    | dest_imp t = raise TERM ("dest_imp", [t]);

(**
  structure Hypsubst_Data =
    struct
    structure Simplifier = Simplifier
    val dest_Trueprop = dest_Trueprop
    val dest_eq = dest_eq
    val dest_imp = dest_imp
    val eq_reflection = @{thm eq_reflection}
    val rev_eq_reflection = @{thm meta_to_obj_eq}
    val imp_intr = @{thm impI}
    val rev_mp = @{thm rev_mp}
    val subst = @{thm subst}
    val sym = @{thm sym}
    val thin_refl = @{thm thin_refl}
    val prop_subst = @{lemma "PROP P(t) ==> PROP prop (x = t ==> PROP P(x))"
                       by (unfold prop_def) (drule eq_reflection, unfold)}
    end;
  structure Hypsubst = HypsubstFun(Hypsubst_Data);
  open Hypsubst;
**)

  structure Hypsubst = Hypsubst(
    val dest_Trueprop = dest_Trueprop
    val dest_eq = dest_eq
    val dest_imp = dest_imp
    val eq_reflection = @{thm eq_reflection}
    val rev_eq_reflection = @{thm meta_to_obj_eq}
    val imp_intr = @{thm impI}
    val rev_mp = @{thm rev_mp}
    val subst = @{thm subst}
    val sym = @{thm sym}
    val thin_refl = @{thm thin_refl}
  );
  open Hypsubst;

(**
  structure Classical_Data =
    struct
    val imp_elim       = @{thm impCE'}
    val not_elim       = @{thm notE}
    val swap           = @{thm swap}
    val classical      = @{thm classical}
    val sizef          = Drule.size_of_thm
    val hyp_subst_tacs = [Hypsubst.hyp_subst_tac]
    end;
  structure Classical = ClassicalFun(Classical_Data);
**)

  structure Classical = Classical(
    val imp_elim       = @{thm impCE'}
    val not_elim       = @{thm notE}
    val swap           = @{thm swap}
    val classical      = @{thm classical}
    val sizef          = Drule.size_of_thm
    val hyp_subst_tacs = [Hypsubst.hyp_subst_tac]
  );
  structure BasicClassical : BASIC_CLASSICAL = Classical;
  open BasicClassical;

*}

setup hypsubst_setup
setup Classical.setup

declare refl [intro!]
  and trueI [intro!]
  and conjI [intro!]
  and disjI [intro!]
  and impI [intro!]
  and notI [intro!]
  and iffI [intro!]
  and cond_boolI [intro!]
  and cond_eqLI [intro!]
  and cond_eqRI [intro!]

  and conjE [elim!]
  and disjE [elim!]
  and impCE [elim!]
  and falseE [elim!]
  and iffCE [elim!]
  and cond_boolE [elim!]
  and cond_eqLE [elim!]
  and cond_eqRE [elim!]

  and allI [intro!]
  and exI [intro]
  and exE [elim!]
  and allE [elim]
  and choose_equality [intro]
  and sym[OF choose_equality, intro]

ML {*
(**
  structure Blast = Blast
  ( struct
    val thy = @{theory}
    type claset	  = Classical.claset
    val equality_name = @{const_name PredicateLogic.eq}
    val not_name = @{const_name PredicateLogic.Not}
    val notE	  = @{thm notE}
    val ccontr    = @{thm contradiction}
    val contr_tac = Classical.contr_tac
    val dup_intr  = Classical.dup_intr
    val hyp_subst_tac = Hypsubst.blast_hyp_subst_tac
    val rep_cs    = Classical.rep_cs
    val cla_modifiers = Classical.cla_modifiers;
    val cla_meth' = Classical.cla_meth'
    end );
**)

  structure Blast = Blast
  (
    structure Classical = Classical
    val Trueprop_const = dest_Const @{const Trueprop}
    val equality_name = @{const_name PredicateLogic.eq}
    val not_name = @{const_name PredicateLogic.Not}
    val notE = @{thm notE}
    val ccontr = @{thm contradiction}
    val hyp_subst_tac = Hypsubst.blast_hyp_subst_tac
  );
*}

setup Blast.setup

(*** TEST DATA ***

lemma "x = y \<Longrightarrow> y = x"
apply hypsubst
apply (rule refl)
done

lemma "!!x.[| Q(x,y,z); y=x; a=x; z=y; P(y) |] ==> P(z)"
by hypsubst

lemma "x = x"
by blast

lemma "x = y \<Rightarrow> y = z \<Rightarrow> z = x"
by blast

lemma "(\<exists>x : \<forall>y : P(x,y)) \<Rightarrow> (\<forall>y : \<exists>x : P(x,y))"
by fast

lemma "TRUE" by blast

lemma "P \<Rightarrow> P"
by blast

lemma "P \<and> Q \<Rightarrow> P"
by blast

lemma "P \<Rightarrow> P \<or> Q"
by blast

lemma "P(a) \<Rightarrow> (\<exists>x : P(x))"
by blast

lemma "(\<exists>x : \<forall>y : P(x,y)) \<Rightarrow> (\<forall>y : \<exists>x : P(x,y))"
by blast

lemma "(\<And>x. P(x) \<Longrightarrow> Q) \<Longrightarrow> (\<exists>x: P(x)) \<Longrightarrow> Q"
by blast

lemma "\<And>x. (\<And>y. P(y)) \<Longrightarrow> P(x)"
by blast

lemma "\<And>P x. (\<And>y. P(y)) \<Longrightarrow> P(x)"
by fast

lemma
  assumes ind: "\<And>Q. (\<forall>n: (\<forall>i: less(i,n) \<Rightarrow> Q(i)) \<Rightarrow> Q(n)) \<Longrightarrow> \<forall>n: Q(n)"
  and "\<forall>n: (\<forall>i: less(i,n) \<Rightarrow> Q(i)) \<Rightarrow> Q(n)"
  shows "Q(n)"
using assms by blast

lemma 
  assumes "\<And>P. P(n)"
  shows "Q(n)"
using assms by fast

lemma "(CHOOSE x: x=a) = a"
by blast

*** END TEST DATA ***)


subsubsection {* Setting up the simplifier *}

text {*
  We instantiate the simplifier, Isabelle's generic rewriting
  machinery. Equational laws for predicate logic will be proven
  below; they automate much of the purely logical reasoning.
*}

lemma if_bool_eq_conj:
  "(IF A THEN B ELSE C) \<Leftrightarrow> ((A \<Rightarrow> B) \<and> (\<not>A \<Rightarrow> C))"
by fast

text {*
  A copy of Isabelle's meta-level implication is introduced, which is used
  internally by the simplifier for fine-tuning congruence rules by simplifying
  their premises.
*}

definition simp_implies :: "[prop, prop] \<Rightarrow> prop"  (infixr "=simp=>" 1) where
  "simp_implies \<equiv> op \<Longrightarrow>"

lemma simp_impliesI:
  assumes PQ: "(PROP P ==> PROP Q)"
  shows "PROP P =simp=> PROP Q"
  unfolding simp_implies_def by (rule PQ)

lemma simp_impliesE:
  assumes PQ: "PROP P =simp=> PROP Q"
  and P: "PROP P" and QR: "PROP Q ==> PROP R"
  shows "PROP R"
proof -
  from P have "PROP Q" by (rule PQ [unfolded simp_implies_def])
  thus "PROP R" by (rule QR)
qed

lemma simp_implies_cong:
  assumes PP' :"PROP P == PROP P'"
  and P'QQ': "PROP P' ==> (PROP Q == PROP Q')"
  shows "(PROP P =simp=> PROP Q) == (PROP P' =simp=> PROP Q')"
unfolding simp_implies_def proof (rule equal_intr_rule)
  assume PQ: "PROP P ==> PROP Q" and P': "PROP P'"
  from PP' [symmetric] and P' have "PROP P"
    by (rule equal_elim_rule1)
  hence "PROP Q" by (rule PQ)
  with P'QQ' [OF P'] show "PROP Q'" by (rule equal_elim_rule1)
next
  assume P'Q': "PROP P' ==> PROP Q'" and P: "PROP P"
  from PP' and P have P': "PROP P'" by (rule equal_elim_rule1)
  hence "PROP Q'" by (rule P'Q')
  with P'QQ' [OF P', symmetric] show "PROP Q" by (rule equal_elim_rule1)
qed

use "simplifier_setup.ML"

setup {* 
  Simplifier.map_simpset_global (K Simpdata.PL_basic_ss)
  #> Simplifier.method_setup Splitter.split_modifiers
  #> Splitter.setup
  #> Simpdata.clasimp_setup
  #> EqSubst.setup
*}


(*** TEST DATA -- note: only basic simplification, no theorems set up ***

lemma "x = x"
by simp

lemma "x = y \<Longrightarrow> y = x"
by simp

lemma
  assumes "x=y" and "y=z"
  shows "x=z"
using assms by simp

lemma
  assumes "f(f(x)) = y \<and> y=x"
  shows "f(f(f(f(y)))) = x"
using assms by simp

lemma
  assumes "z=x \<Rightarrow> f(f(z)) = x" and "z=x"
  shows "f(f(f(f(z)))) = z"
using assms by simp

lemma "x=y \<and> y=z \<Rightarrow> x=z \<and> f(y) = f(x)"
by auto

lemma "x=y \<Rightarrow> y=z \<Rightarrow> x=z"
by force

lemma "(\<forall>x : P(x)) \<Rightarrow> P(a)"
by auto

lemma
  assumes ind: "P(z) \<Longrightarrow> (\<And>n. P(n) \<Longrightarrow> P(s(n))) \<Longrightarrow> (\<And>n. P(n))"
  and z: "P(z)" and s: "\<And>n. P(n) \<Longrightarrow> P(s(n))"
  shows "P(m)"
using assms by auto

lemma
  assumes "(\<And>n. (\<And>i. L(i,n) \<Longrightarrow> Q(i)) \<Longrightarrow> Q(n)) \<Longrightarrow> (\<And>n. Q(n))"
  and "\<And>n. (\<And>i. L(i,n) \<Longrightarrow> Q(i)) \<Longrightarrow> Q(n)"
  shows "Q(n)"
using assms by auto

(* without converting all connectives to meta-level (via attribute
   [rule_format]), the following loops *)
lemma
  assumes "\<And>Q. (\<forall>n: (\<forall>i: L(i,n) \<Rightarrow> Q(i)) \<Rightarrow> Q(n)) \<Longrightarrow> (\<forall>n: Q(n))"
  and "\<forall>n: (\<forall>i: L(i,n) \<Rightarrow> Q(i)) \<Rightarrow> Q(n)"
  shows "Q(n)"
using assms[rule_format] by auto

*** END TEST DATA ***)

lemma trueprop_eq_true: "Trueprop(A = TRUE) \<equiv> Trueprop(A)"
proof
  assume "A = TRUE" thus "A" by (rule eqTrueD)
next
  assume "A" thus "A = TRUE" by (rule eqTrueI)
qed

lemma trueprop_true_eq: "Trueprop(TRUE = A) \<equiv> Trueprop(A)"
proof
  assume "TRUE = A" 
  hence "A = TRUE" by (rule sym)
  thus "A" by (rule eqTrueD)
next
  assume "A"
  hence "A = TRUE" by (rule eqTrueI)
  thus "TRUE = A" by (rule sym)
qed

lemmas [simp] =
  triv_forall_equality
  TrueAssumption
  trueprop_eq_true  trueprop_true_eq
  refl[THEN eqTrueI]   -- {* @{text "(x = x) \<equiv> TRUE"} *}
  condT (*condThen*)      notTrue 
  condF (*condElse*)      notFalse
  cond_id
  false_neq_true[THEN eqBoolean]
  not_sym[OF false_neq_true, THEN eqBoolean]
  iff_refl

lemmas [cong] = simp_implies_cong


subsubsection {* Reasoning by cases *}

text {*
  The next bit of code sets up reasoning by cases as a proper Isar
  method, so we can write ``proof cases'' etc. Following the 
  development of FOL, we introduce a set of ``shadow connectives''
  that will only be used for this purpose.
*}

theorems cases = case_split [case_names True False]

definition cases_equal where "cases_equal \<equiv> eq"
definition cases_implies where "cases_implies \<equiv> imp"
definition cases_conj where "cases_conj \<equiv> conj"
definition cases_forall where "cases_forall(P) \<equiv> \<forall>x: P(x)"
definition cases_true where "cases_true \<equiv> TRUE"
definition cases_false where "cases_false \<equiv> FALSE"

lemma cases_equal_eq: "(x \<equiv> y) \<equiv> Trueprop(cases_equal(x, y))"
unfolding atomize_eq cases_equal_def .

lemma cases_implies_eq: "(A \<Longrightarrow> B) \<equiv> Trueprop (cases_implies(A,B))"
unfolding atomize_imp cases_implies_def .

lemma cases_conj_eq: "(A &&& B) \<equiv> Trueprop (cases_conj(A,B))"
unfolding atomize_conj cases_conj_def .

lemma cases_forall_eq: "(\<And>x. P(x)) \<equiv> Trueprop (cases_forall (\<lambda>x. P(x)))"
unfolding atomize_all cases_forall_def .

lemma cases_trueI: "cases_true"
unfolding cases_true_def ..

lemmas cases_atomize' = cases_implies_eq cases_conj_eq cases_forall_eq
lemmas cases_atomize  = cases_atomize' cases_equal_eq
lemmas cases_rulify' [symmetric, standard] = cases_atomize'
lemmas cases_rulify  [symmetric, standard] = cases_atomize
lemmas cases_rulify_fallback = 
  cases_equal_def cases_implies_def cases_conj_def cases_forall_def
  cases_true_def cases_false_def

lemma cases_forall_conj: "cases_forall (\<lambda>x. cases_conj(A(x), B(x))) \<Leftrightarrow>
    cases_conj(cases_forall(A), cases_forall(B))"
  by (unfold cases_forall_def cases_conj_def) iprover

lemma cases_implies_conj: "cases_implies(C, cases_conj(A, B)) \<Leftrightarrow>
    cases_conj(cases_implies(C, A), cases_implies(C, B))"
  by (unfold cases_implies_def cases_conj_def) iprover

lemma cases_conj_curry: "(cases_conj(A, B) \<Longrightarrow> PROP C) \<equiv> (A \<Longrightarrow> B \<Longrightarrow> PROP C)"
proof
  assume r: "cases_conj(A, B) ==> PROP C" and ab: "A" "B"
  from ab show "PROP C"
    by (intro r[unfolded cases_conj_def], fast)
next
  assume r: "A ==> B ==> PROP C" and ab: "cases_conj(A, B)"
  from ab[unfolded cases_conj_def] show "PROP C"
    by (intro r, fast, fast)
qed

lemmas cases_conj = cases_forall_conj cases_implies_conj cases_conj_curry

ML {*
  structure Induct = Induct
  (
    val cases_default = @{thm cases}
    val atomize = @{thms cases_atomize}
    val rulify = @{thms cases_rulify'}
    val rulify_fallback = @{thms cases_rulify_fallback}
    val equal_def = @{thm cases_equal_def}
    fun dest_def (Const (@{const_name cases_equal}, _) $ t $ u) = SOME (t, u)
      | dest_def _ = NONE
    val trivial_tac = match_tac @{thms cases_trueI}
  )
*}

setup {*
  Induct.setup #>
  Context.theory_map (Induct.map_simpset (fn ss => ss
    setmksimps (fn ss => Simpdata.mksimps Simpdata.mksimps_pairs ss #>
      map (Simplifier.rewrite_rule (map Thm.symmetric @{thms cases_rulify_fallback})))
    addsimprocs
      [Simplifier.simproc_global @{theory} "swap_cases_false"
         ["cases_false ==> PROP P ==> PROP Q"]
         (fn _ => fn _ =>
            (fn _ $ (P as _ $ @{const cases_false}) $ (_ $ Q $ _) =>
                  if P <> Q then SOME Drule.swap_prems_eq else NONE
              | _ => NONE)),
       Simplifier.simproc_global @{theory} "cases_equal_conj_curry"
         ["cases_conj(P, Q) ==> PROP R"]
         (fn _ => fn _ =>
            (fn _ $ (_ $ P) $ _ =>
                let
                  fun is_conj (@{const cases_conj} $ P $ Q) =
                        is_conj P andalso is_conj Q
                    | is_conj (Const (@{const_name cases_equal}, _) $ _ $ _) = true
                    | is_conj @{const cases_true} = true
                    | is_conj @{const cases_false} = true
                    | is_conj _ = false
                in if is_conj P then SOME @{thm cases_conj_curry} else NONE end
              | _ => NONE))]))
*}

text {* Pre-simplification of induction and cases rules *}

lemma [induct_simp]: "(\<And>x. cases_equal(x, t) \<Longrightarrow> PROP P(x)) \<equiv> PROP P(t)"
  unfolding cases_equal_def
proof
  assume R: "\<And>x. x = t \<Longrightarrow> PROP P(x)"
  show "PROP P(t)" by (rule R [OF refl])
next
  fix x assume "PROP P(t)" "x = t"
  then show "PROP P(x)" by simp
qed

lemma [induct_simp]: "(\<And>x. cases_equal(t, x) \<Longrightarrow> PROP P(x)) \<equiv> PROP P(t)"
  unfolding cases_equal_def
proof
  assume R: "\<And>x. t = x \<Longrightarrow> PROP P(x)"
  show "PROP P(t)" by (rule R [OF refl])
next
  fix x assume "PROP P(t)" "t = x"
  then show "PROP P(x)" by simp
qed

lemma [induct_simp]: "(cases_false \<Longrightarrow> P) \<equiv> Trueprop(cases_true)"
unfolding cases_false_def cases_true_def by (iprover intro: equal_intr_rule)

lemma [induct_simp]: "(cases_true \<Longrightarrow> PROP P) \<equiv> PROP P"
  unfolding cases_true_def
proof
  assume R: "TRUE \<Longrightarrow> PROP P"
  from trueI show "PROP P" by (rule R)
next
  assume "PROP P" thus "PROP P" .
qed

lemma [induct_simp]: "(PROP P \<Longrightarrow> cases_true) \<equiv> Trueprop(cases_true)"
unfolding cases_true_def by (iprover intro: equal_intr_rule)

lemma [induct_simp]: "(\<And>x. cases_true) \<equiv> Trueprop(cases_true)"
unfolding cases_true_def by (iprover intro: equal_intr_rule)

lemma [induct_simp]: "Trueprop(cases_implies(cases_true, P)) \<equiv> Trueprop(P)"
  unfolding cases_implies_def cases_true_def by (iprover intro: equal_intr_rule)

lemma [induct_simp]: "(x = x) = TRUE"
by simp

hide_const cases_forall cases_implies cases_equal cases_conj cases_true cases_false


(*** BASIC TEST DATA ***

lemma "P \<or> \<not>P"
proof (cases "P")
  case True thus ?thesis ..
next
  case False thus ?thesis ..
qed

*** END TEST DATA ***)


subsection {* Propositional simplification *}

subsubsection {* Conversion to Boolean values *}

text {*
  Because \tlaplus{} is untyped, equivalence is different from equality,
  and one has to be careful about stating the laws of propositional
  logic. For example, although the equivalence @{text "(TRUE \<and> A) \<Leftrightarrow> A"}
  is valid, we cannot state the law @{text "(TRUE \<and> A) = A"}
  because we have no way of knowing the value of, e.g., @{text "TRUE \<and> 3"}.
  These equalities are valid only if
  the connectives are applied to Boolean operands. For automatic
  reasoning, we are interested in equations that can be used by
  Isabelle's simplifier. We therefore introduce an auxiliary 
  predicate that is true precisely of Boolean arguments, and an
  operation that converts arbitrary arguments to an equivalent
  (in the sense of @{text "\<Leftrightarrow>"}) Boolean expression.

  We will prove below that propositional formulas return a Boolean
  value when applied to arbitrary arguments.
*}

definition boolify :: "c \<Rightarrow> c" where
  "boolify(x) \<equiv> IF x THEN TRUE ELSE FALSE"

definition isBool :: "c \<Rightarrow> c" where
  "isBool(x) \<equiv> boolify(x) = x"

text {*
  The formulas @{text "P"} and @{text "boolify(P)"} are inter-derivable
  (but need of course not be equal, unless @{text P} is a Boolean).
*}

lemma boolifyI [intro!]: "P \<Longrightarrow> boolify(P)"
unfolding boolify_def by fast

lemma boolifyE [elim!]:
  "\<lbrakk> boolify(P); P \<Longrightarrow> Q \<rbrakk> \<Longrightarrow> Q"
unfolding boolify_def by fast

lemma TruepropBoolify [simp]: "Trueprop(boolify(A)) \<equiv> Trueprop(A)"
by (rule, fast+)

lemma boolify_cases:  (** too general to be used as a default rule **)
  assumes "P(TRUE)" and "P(FALSE)"
  shows "P(boolify(x))"
unfolding boolify_def using assms by (fast intro: condI)

text {*
  @{text boolify} can be defined as @{text "x = TRUE"}. For
  automatic reasoning, we rewrite the latter to the former, and
  derive calculational rules for @{text boolify}.
*}

lemma [simp]: "(x = TRUE) = boolify(x)"
proof (cases "x")
  case True thus ?thesis by (simp add: boolify_def)
next
  case False
  hence "x \<noteq> TRUE" by fast
  thus ?thesis by (auto simp add: boolify_def)
qed

lemma [simp]: "(TRUE = x) = boolify(x)"
proof (cases "x")
  case True thus ?thesis by (simp add: boolify_def)
next
  case False
  hence "TRUE \<noteq> x" by fast
  thus ?thesis by (auto simp add: boolify_def)
qed

lemma boolifyTrue [simp]: "boolify(TRUE) = TRUE"
by (simp add: boolify_def)

lemma trueIsBool [intro!,simp]: "isBool(TRUE)"
by (unfold isBool_def, rule boolifyTrue)

lemma boolifyTrueI [intro]: "A \<Longrightarrow> boolify(A) = TRUE"
by (simp add: boolify_def)

lemma boolifyFalse [simp]: "boolify(FALSE) = FALSE"
by (auto simp add: boolify_def)

lemma falseIsBool [intro!,simp]: "isBool(FALSE)"
by (unfold isBool_def, rule boolifyFalse)

text {*
  The following lemma is used to turn hypotheses @{text "\<not>A"} into
  rewrite rules @{text "A = FALSE"}.
*}
lemma boolifyFalseI [intro]: "\<not> A \<Longrightarrow> boolify(A) = FALSE"
by (auto simp add: boolify_def)

text {* idempotence of @{text boolify} *}
lemma boolifyBoolify [simp]: "boolify(boolify(x)) = boolify(x)"
by (auto simp add: boolify_def)

lemma boolifyIsBool [intro!,simp]: "isBool(boolify(x))"
by (unfold isBool_def, rule boolifyBoolify)

lemma boolifyEquivalent: "boolify(x) \<Leftrightarrow> x"
by (auto simp add: boolify_def)

lemma boolifyTrueFalse: "(boolify(x) = TRUE) \<or> (boolify(x) = FALSE)"
by (auto simp add: boolify_def)

lemma isBoolTrueFalse:
  assumes hyp: "isBool(x)"
  shows "(x = TRUE) \<or> (x = FALSE)"
proof -
  from hyp have "boolify(x) = x" by (unfold isBool_def)
  hence bx: "boolify(x) \<equiv> x" by (rule eq_reflection)
  from boolifyTrueFalse[of x] 
  show ?thesis by (unfold bx)
qed

lemmas isBoolE [elim!] = isBoolTrueFalse[THEN disjE, standard]

lemma boolifyEq [simp]: "boolify(t=u) = (t=u)" (* first use of axiom eqBoolean *)
proof (cases "t=u")
  case True
  hence "(t=u) = TRUE" by (rule eqTrueI)
  hence tu: "(t=u) \<equiv> TRUE" by (rule eq_reflection)
  show ?thesis by (unfold tu, rule boolifyTrue)
next
  case False
  hence "(t=u) = FALSE" by (rule eqBoolean)
  hence tu: "(t=u) \<equiv> FALSE" by (rule eq_reflection)
  show "boolify(t=u) = (t=u)" by (unfold tu, rule boolifyFalse)
qed

lemma eqIsBool [intro!,simp]: "isBool(t=u)"
unfolding isBool_def by (rule boolifyEq)

lemma boolifyCond [simp]:
  "boolify(IF A THEN t ELSE u) = (IF A THEN boolify(t) ELSE boolify(u))"
by (auto simp add: boolify_def)

lemma isBoolCond[intro!,simp]:
  "\<lbrakk> isBool(t); isBool(e) \<rbrakk> \<Longrightarrow> isBool(IF A THEN t ELSE e)"
by (simp add: isBool_def)

lemma boolifyNot [simp]: "boolify(\<not> A) = (\<not> A)"
by (simp add: not_def)

lemma notIsBool [intro!,simp]: "isBool(\<not> A)"
unfolding isBool_def by (rule boolifyNot)

lemma notBoolIsFalse:
  assumes "isBool(A)"
  shows "(\<not>A) = (A = FALSE)"
using assms by auto

lemma boolifyAnd [simp]: "boolify(A \<and> B) = (A \<and> B)"
by (simp add: conj_def)

lemma andIsBool [intro!,simp]: "isBool(A \<and> B)"
unfolding isBool_def by (rule boolifyAnd)

lemma boolifyOr [simp]: "boolify(A \<or> B) = (A \<or> B)"
by (simp add: disj_def)

lemma orIsBool [intro!,simp]: "isBool(A \<or> B)"
unfolding isBool_def by (rule boolifyOr)

lemma boolifyImp [simp]: "boolify(A \<Rightarrow> B) = (A \<Rightarrow> B)"
by (simp add: imp_def)

lemma impIsBool [intro!,simp]: "isBool(A \<Rightarrow> B)"
unfolding isBool_def by (rule boolifyImp)

lemma boolifyIff [simp]: "boolify(A \<Leftrightarrow> B) = (A \<Leftrightarrow> B)"
by (simp add: iff_def)

lemma iffIsBool [intro!,simp]: "isBool(A \<Leftrightarrow> B)"
unfolding isBool_def by (rule boolifyIff)

text {* 
  We can now rewrite equivalences to equations between ``boolified''
  arguments, and this gives rise to a technique for proving equations
  between formulas.
*}

lemma boolEqual:
  assumes "P \<Leftrightarrow> Q" and "isBool(P)" and "isBool(Q)"
  shows "P = Q"
using assms by auto

text {*
  The following variant converts equivalences to equations. It might
  be useful as a (non-conditional) simplification rule, but I suspect
  that for goals it is more useful to use the standard introduction
  rule reducing an equivalence to two implications.

  For assumptions we can use lemma @{text boolEqual} for turning
  equivalences into conditional rewrites.
*}

lemma iffIsBoolifyEqual: "(A \<Leftrightarrow> B) = (boolify(A) = boolify(B))"
proof (rule boolEqual)
  show "(A \<Leftrightarrow> B) \<Leftrightarrow> (boolify(A) = boolify(B))" by (auto simp: boolifyFalseI)
qed (simp_all)

lemma iffThenBoolifyEqual:
  assumes "A \<Leftrightarrow> B" shows "boolify(A) = boolify(B)"
using assms by (simp add: iffIsBoolifyEqual)

(* Don't add the following to the simpset: it would be tried on all
   equations! Instead, we'll add derived introduction rules for all
   Boolean connectives below.
*)
lemma boolEqualIff:
  assumes "isBool(P)" and "isBool(Q)"
  shows "(P = Q) = (P \<Leftrightarrow> Q)"
using assms by (auto intro: boolEqual)

ML {*
  structure Simpdata =
  struct
    open Simpdata;
    val mksimps_pairs = [(@{const_name Not}, (@{thms boolifyFalseI}, true)),
                         (@{const_name iff}, (@{thms iffThenBoolifyEqual}, true))] 
                        @ mksimps_pairs;
  end;

  open Simpdata;
*}

declaration {* fn _ =>
  Simplifier.map_ss (fn ss => ss setmksimps (mksimps mksimps_pairs))
*}

(** TEST DATA **

lemma
  assumes "x=y \<Leftrightarrow> u=v" and "u=v"
  shows "x=y"
using assms by simp

lemma
  assumes "\<not>(A \<Rightarrow> B)" and "A \<Rightarrow> B"
  shows "FALSE"
using assms by simp

** END TEST DATA **)

text {* 
  The following code rewrites @{text "x = y"} to @{text "FALSE"} in the
  presence of a premise @{text "y \<noteq> x"} or @{text "(y = x) = FALSE"}. 
  The simplifier is set up so that @{text "y = x"} is already simplified 
  to @{text "FALSE"}, this code adds symmetry of disequality to simplification.
*}

lemma symEqLeft: "(x = y) = b \<Longrightarrow> (y = x) = b"
by (auto simp: boolEqualIff)

simproc_setup neq ("x = y") = {* fn _ =>
let
  val neq_to_EQ_False = @{thm not_sym} RS @{thm eqBoolean} RS @{thm eq_reflection};
  val symEqLeft_to_symEQLeft = @{thm symEqLeft} RS @{thm eq_reflection};
  fun is_neq lhs rhs thm =
    (case Thm.prop_of thm of
      _ $ (Not' $ (eq' $ l' $ r')) =>
        Not' = @{const "Not"} andalso eq' = @{const "eq"} andalso
        r' aconv lhs andalso l' aconv rhs
    | _ $ (eq' $ (eq'' $ l' $ r') $ f') => 
        eq' = @{const "eq"} andalso eq'' = @{const "eq"} andalso
        f' = @{const "FALSE"} andalso r' aconv lhs andalso l' aconv rhs
    | _ => false);
  fun proc ss ct =
    (case Thm.term_of ct of
      eq $ lhs $ rhs =>
        (case find_first (is_neq lhs rhs) (Simplifier.prems_of ss) of
          SOME thm => SOME ((thm RS symEqLeft_to_symEQLeft)
                            handle _ => thm RS neq_to_EQ_False)
        | NONE => NONE)
     | _ => NONE);
in proc end;
*}

(*** TEST ***
lemma "a \<noteq> b \<Longrightarrow> (IF b = a THEN t ELSE u) = u"
by simp

lemma "(a = b) = FALSE \<Longrightarrow> (IF b = a THEN t ELSE u) = u"
by simp

***)

lemma boolifyEx [simp]: "boolify(Ex(P)) = Ex(P)"
by (simp add: Ex_def)

lemma exIsBool [intro!,simp]: "isBool(Ex(P))"
unfolding isBool_def by (rule boolifyEx)

lemma boolifyAll [simp]: "boolify(All(P)) = All(P)"
by (simp add: All_def)

lemma allIsBool [intro!,simp]: "isBool(All(P))"
unfolding isBool_def by (rule boolifyAll)

lemma [intro!]:
  "\<lbrakk>isBool(P); Q \<Leftrightarrow> P\<rbrakk> \<Longrightarrow> boolify(Q) = P"
  "\<lbrakk>isBool(P); P \<Leftrightarrow> Q\<rbrakk> \<Longrightarrow> P = boolify(Q)"
  "P \<Longrightarrow> TRUE = P"
  "P \<Longrightarrow> P = TRUE"
  "\<lbrakk>isBool(P); P \<Longrightarrow> FALSE\<rbrakk> \<Longrightarrow> FALSE = P"
  "\<lbrakk>isBool(P); P \<Longrightarrow> FALSE\<rbrakk> \<Longrightarrow> P = FALSE"
  "\<lbrakk>isBool(P); t=u \<Leftrightarrow> P\<rbrakk> \<Longrightarrow> (t=u) = P"
  "\<lbrakk>isBool(P); P \<Leftrightarrow> t=u\<rbrakk> \<Longrightarrow> P = (t=u)"
  "\<lbrakk>isBool(P); \<not>Q \<Leftrightarrow> P\<rbrakk> \<Longrightarrow> (\<not>Q) = P"
  "\<lbrakk>isBool(P); P \<Leftrightarrow> \<not>Q\<rbrakk> \<Longrightarrow> P = (\<not>Q)"
  "\<lbrakk>isBool(P); P \<Leftrightarrow> (Q \<and> R)\<rbrakk> \<Longrightarrow> P = (Q \<and> R)"
  "\<lbrakk>isBool(P); (Q \<and> R) \<Leftrightarrow> P\<rbrakk> \<Longrightarrow> (Q \<and> R) = P"
  "\<lbrakk>isBool(P); P \<Leftrightarrow> (Q \<or> R)\<rbrakk> \<Longrightarrow> P = (Q \<or> R)"
  "\<lbrakk>isBool(P); (Q \<or> R) \<Leftrightarrow> P\<rbrakk> \<Longrightarrow> (Q \<or> R) = P"
  "\<lbrakk>isBool(P); P \<Leftrightarrow> (Q \<Rightarrow> R)\<rbrakk> \<Longrightarrow> P = (Q \<Rightarrow> R)"
  "\<lbrakk>isBool(P); (Q \<Rightarrow> R) \<Leftrightarrow> P\<rbrakk> \<Longrightarrow> (Q \<Rightarrow> R) = P"
  "\<lbrakk>isBool(P); P \<Leftrightarrow> (Q \<Leftrightarrow> R)\<rbrakk> \<Longrightarrow> P = (Q \<Leftrightarrow> R)"
  "\<lbrakk>isBool(P); (Q \<Leftrightarrow> R) \<Leftrightarrow> P\<rbrakk> \<Longrightarrow> (Q \<Leftrightarrow> R) = P"
  "\<lbrakk>isBool(P); All(A) \<Leftrightarrow> P\<rbrakk> \<Longrightarrow> All(A) = P"
  "\<lbrakk>isBool(P); P \<Leftrightarrow> All(A)\<rbrakk> \<Longrightarrow> P = All(A)"
  "\<lbrakk>isBool(P); Ex(A) \<Leftrightarrow> P\<rbrakk> \<Longrightarrow> Ex(A) = P"
  "\<lbrakk>isBool(P); P \<Leftrightarrow> Ex(A)\<rbrakk> \<Longrightarrow> P = Ex(A)"
by (auto simp: boolEqualIff)

lemma notBoolifyFalse [simp]: "(\<not>A) = (boolify(A) = FALSE)"
by auto

(*** TODO: set up simprocs for one-point rules.
  Check what needs to be done to derive the necessary chains of
  equivalences.
****

text {*
  The following lemmas are used by the simplifier to rearrange quantifiers.
*}

lemma uncurry:
  assumes "P \<Rightarrow> Q \<Rightarrow> R"
  shows "P \<and> Q \<Rightarrow> R"
  using assms by blast

lemma iff_allI:
  assumes "\<And>x. P(x) = Q(x)"
  shows "(\<forall>x : P(x)) = (\<forall>x : Q(x))"
  using assms by blast

lemma iff_exI:
  assumes "!!x. P x = Q x"
  shows "(\<exists>x. P x) = (\<exists>x. Q x)"
  using assms by blast

lemma all_comm:
  "(\<forall>x y. P x y) = (\<forall>y x. P x y)"
  by blast

lemma ex_comm:
  "(\<exists>x y. P x y) = (\<exists>y x. P x y)"
  by blast

ML {*
  use "~~/src/Provers/quantifier1.ML";
  local
    val uncurry =
      prove_goal (the_context()) "P => Q => R ==> P & Q => R"
                 (fn prems => [cut_facts_tac prems 1, Blast_tac 1]);
    val iff_allI =
      prove_goal (the_context()) "(!!x. P(x) <=> Q(x)) ==> (ALL x. P(x)) = (ALL x. Q(x))"
                 (fn prems => [cut_facts_tac prems 1, 
                               auto_tac (claset() addIs [boolEqual], simpset())]);
    val iff_exI =
      prove_goal (the_context()) "(!!x. P(x) <=> Q(x)) ==> (EX x. P(x)) = (EX x. Q(x))"
                 (fn prems => [cut_facts_tac prems 1,
                               auto_tac (claset() addIs [boolEqual], simpset())]);
    val all_comm =
      prove_goal (the_context()) "(ALL x y. P(x,y)) = (ALL y x. P(x,y))"
                 (fn _ => [auto_tac (claset() addIs [boolEqual], simpset())]);
    val ex_comm =
      prove_goal (the_context()) "(EX x y. P(x,y)) = (EX y x. P(x,y))"
                 (fn _ => [auto_tac (claset() addIs [boolEqual], simpset())]);
    val c_type = Type("c", []);
    structure Quantifier1 = Quantifier1Fun(
      struct
        (* syntax *)
        fun dest_eq((c as Const("eq",_)) $ s $ t) = SOME(c,s,t)
          | dest_eq _ = NONE;
        fun dest_conj((c as Const("conj",_)) $ s $ t) = SOME(c,s,t)
          | dest_conj _ = NONE;
        fun dest_imp((c as Const("imp",_)) $ s $ t) = SOME(c,s,t)
          | dest_imp _ = NONE;
        val conj = @{term conj};
        val imp = @{term imp};
        (* rules *)
        val iff_reflection = thm "eq_reflection";
        val iffI = @{thm iffI};
        val iff_trans = @{thm trans};
      end);
  in

*}
***)

text {*
  Orient equations with Boolean constants such that the constant appears
  on the right-hand side.
*}

lemma boolConstEqual [simp]:
  "(TRUE = P) = (P = TRUE)"
  "(FALSE = P) = (P = FALSE)"
by blast+


subsubsection {* Simplification laws for conditionals *}

lemma splitCond [split]:
  assumes q: "\<And>x. isBool(Q(x))"
  shows "Q(IF P THEN t ELSE e) = ((P \<Rightarrow> Q(t)) \<and> (\<not>P \<Rightarrow> Q(e)))"
proof (cases "P")
  case True thus ?thesis by (auto intro: q)
next
  case False
  hence "(IF P THEN t ELSE e) = e" by (rule condElse)
  thus ?thesis by (auto intro: q)
qed

lemma splitCondAsm: -- {* useful with conditionals in hypotheses *}
  assumes "\<And>x. isBool(Q(x))"
  shows "Q(IF P THEN t ELSE e) = (\<not>((P \<and> \<not>Q(t)) \<or> (\<not>P \<and> \<not>Q(e))))"
using assms by (simp only: splitCond, blast)

lemma condCong (*[cong]*):  (* strangely, seems to simplify less when active ?! *)
  "P = Q \<Longrightarrow> (IF P THEN t ELSE e) = (IF Q THEN t ELSE e)"
by simp

lemma condFullCong: -- {* not active by default, because too expensive *}
  "\<lbrakk>P = Q; Q \<Longrightarrow> t=t'; \<not>Q \<Longrightarrow> e=e'\<rbrakk> \<Longrightarrow> (IF P THEN t ELSE e) = (IF Q THEN t' ELSE e')"
by auto

lemma substCond [intro]:
  assumes "A \<Leftrightarrow> B"
  and "\<lbrakk> A;B \<rbrakk> \<Longrightarrow> t=v" and "\<lbrakk> \<not>A; \<not>B \<rbrakk> \<Longrightarrow> e=f"
  shows "(IF A THEN t ELSE e) = (IF B THEN v ELSE f)"
using assms by auto

lemma cond_simps [simp]:
  "(IF x = y THEN y ELSE x) = x"
  "(IF (IF A THEN B ELSE C) THEN t ELSE e) =
   (IF (A \<and> B) \<or> (\<not>A \<and> C) THEN t ELSE e)"
  "(IF A THEN (IF B THEN t ELSE u) ELSE v) =
   (IF A \<and> B THEN t ELSE IF A \<and> \<not>B THEN u ELSE v)"
by auto


subsubsection {* Simplification laws for conjunction *}

lemma conj_simps [simp]:
  "(P \<and> TRUE) = boolify(P)"
  "(TRUE \<and> P) = boolify(P)"
  "(P \<and> FALSE) = FALSE"
  "(FALSE \<and> P) = FALSE"
(*** too costly to have by default
  "\<not>P \<Longrightarrow> (P \<and> Q) = FALSE"
  "\<not>P \<Longrightarrow> (Q \<and> P) = FALSE"
***)
  "(P \<and> P) = boolify(P)"
  "(P \<and> P \<and> Q) = (P \<and> Q)"
  "((P \<and> Q) \<and> R) = (P \<and> Q \<and> R)"
by auto

text {* 
  The congruence rule for conjunction is occasionally useful, but not
  active by default.
*}

lemma conj_cong:
  assumes "P = P'" and "P' \<Longrightarrow> Q = Q'"
  shows "(P \<and> Q) = (P' \<and> Q')"
using assms by auto

text {* Commutativity laws are not active by default *}

lemma conj_comms: 
  "(P \<and> Q) = (Q \<and> P)"
  "(P \<and> Q \<and> R) = (Q \<and> P \<and> R)"
by auto


subsubsection {* Simplification laws for disjunction *}

lemma disj_simps [simp]:
  "(P \<or> TRUE) = TRUE"
  "(TRUE \<or> P) = TRUE"
  "(P \<or> FALSE) = boolify(P)"
  "(FALSE \<or> P) = boolify(P)"
(*** too costly to have by default
  "\<not>P \<Longrightarrow> (P \<or> Q) = boolify(Q)"
  "\<not>P \<Longrightarrow> (Q \<or> P) = boolify(Q)"
***)
  "(P \<or> P) = boolify(P)"
  "(P \<or> P \<or> Q) = (P \<or> Q)"
  "((P \<or> Q) \<or> R) = (P \<or> Q \<or> R)"
by auto

text {* Congruence rule, not active by default *}

lemma disj_cong:
  assumes "P = P'" and "\<not>P' \<Longrightarrow> Q = Q'"
  shows "(P \<or> Q) = (P' \<or> Q')"
using assms by auto

text {* Commutativity laws are not active by default *}

lemma disj_comms: 
  "(P \<or> Q) = (Q \<or> P)"
  "(P \<or> Q \<or> R) = (Q \<or> P \<or> R)"
by auto


subsubsection {* Simplification laws for negation *}

text {*
  Negated formulas create simplifications of the form
  @{text "A = FALSE"}, we therefore prove two versions of the
  following lemmas to complete critical pairs.
*}

lemma not_simps [simp]:
  "(\<not>(P \<or> Q)) = (\<not>P \<and> \<not>Q)"
  "(\<not>(P \<and> Q)) = (\<not>P \<or> \<not>Q)"
  "(\<not>(P \<Rightarrow> Q)) = (P \<and> \<not>Q)"
  "(\<not>(P \<Leftrightarrow> Q)) = (P \<Leftrightarrow> \<not>Q)"
  "(\<not>P \<Leftrightarrow> \<not>Q) = (P \<Leftrightarrow> Q)"
  "(\<not>\<not>P) = boolify(P)"
  "(x \<noteq> x) = FALSE"
  "\<And>P. (\<not>(\<forall>x : P(x))) = (\<exists>x : \<not>P(x))"
  "\<And>P. (\<not>(\<exists>x : P(x))) = (\<forall>x : \<not>P(x))"
by (auto simp del: notBoolifyFalse)

declare not_simps [simplified,simp]

lemma eqFalse_eqFalse [simp]: "isBool(P) \<Longrightarrow> ((P = FALSE) = FALSE) = P"
by auto

subsubsection {* Simplification laws for implication *}

lemma imp_simps [simp]:
  "(P \<Rightarrow> FALSE) = (\<not>P)"
  "(P \<Rightarrow> TRUE) = TRUE"
  "(FALSE \<Rightarrow> P) = TRUE"
  "(TRUE \<Rightarrow> P) = boolify(P)"
  "(P \<Rightarrow> P) = TRUE"
  "(P \<Rightarrow> \<not>P) = (\<not>P)"
by auto

lemma imp_cong [cong]: 
  "(P = P') \<Longrightarrow> (P' \<Longrightarrow> (Q = Q')) \<Longrightarrow> ((P \<Rightarrow> Q) = (P' \<Rightarrow> Q'))"
by auto


subsubsection {* Simplification laws for equivalence *}

lemma iff_simps [simp]:
  "(TRUE \<Leftrightarrow> P) = boolify(P)"
  "(P \<Leftrightarrow> TRUE) = boolify(P)"
  "(P \<Leftrightarrow> P) = TRUE"
  "(FALSE \<Leftrightarrow> P) = (\<not>P)"
  "(P \<Leftrightarrow> FALSE) = (\<not>P)"
by auto

lemma iff_cong [cong]:
  "P = P' \<Longrightarrow> Q = Q' \<Longrightarrow> (P \<Leftrightarrow> Q) = (P' \<Leftrightarrow> Q')"
by auto


subsubsection {* Simplification laws for quantifiers *}

(*** subsumed by following simplifications
lemma [simp]: "\<exists>x : TRUE"
by auto
***)

lemma quant_simps [simp]:
  "\<And> P. (\<exists>x : P) = boolify(P)"
  "\<And> P. (\<forall>x : P) = boolify(P)"
  "\<exists>x : x=t"
  "\<exists>x : t=x"
  "\<And> P. (\<exists>x : x=t \<and> P(x)) = boolify(P(t))"
  "\<And> P. (\<exists>x : t=x \<and> P(x)) = boolify(P(t))"
  "\<And> P. (\<forall>x : x=t \<Rightarrow> P(x)) = boolify(P(t))"
  "\<And> P. (\<forall>x : t=x \<Rightarrow> P(x)) = boolify(P(t))"
by auto


text {* Miniscoping of quantifiers. *}

lemma miniscope_ex [simp]:
  "\<And>P Q. (\<exists>x : P(x) \<and> Q) = ((\<exists>x : P(x)) \<and> Q)"
  "\<And>P Q. (\<exists>x : P \<and> Q(x)) = (P \<and> (\<exists>x : Q(x)))"
  "\<And>P Q. (\<exists>x : P(x) \<or> Q) = ((\<exists>x : P(x)) \<or> Q)"
  "\<And>P Q. (\<exists>x : P \<or> Q(x)) = (P \<or> (\<exists>x : Q(x)))"
  "\<And>P Q. (\<exists>x : P(x) \<Rightarrow> Q) = ((\<forall>x : P(x)) \<Rightarrow> Q)"
  "\<And>P Q. (\<exists>x : P \<Rightarrow> Q(x)) = (P \<Rightarrow> (\<exists>x : Q(x)))"
by auto

lemma miniscope_all [simp]:
  "\<And>P Q. (\<forall>x : P(x) \<and> Q) = ((\<forall>x : P(x)) \<and> Q)"
  "\<And>P Q. (\<forall>x : P \<and> Q(x)) = (P \<and> (\<forall>x : Q(x)))"
  "\<And>P Q. (\<forall>x : P(x) \<or> Q) = ((\<forall>x : P(x)) \<or> Q)"
  "\<And>P Q. (\<forall>x : P \<or> Q(x)) = (P \<or> (\<forall>x : Q(x)))"
  "\<And>P Q. (\<forall>x : P(x) \<Rightarrow> Q) = ((\<exists>x : P(x)) \<Rightarrow> Q)"
  "\<And>P Q. (\<forall>x : P \<Rightarrow> Q(x)) = (P \<Rightarrow> (\<forall>x : Q(x)))"
by auto

lemma choose_trivial [simp]: "(CHOOSE x : x = t) = t"
by (rule chooseI, rule refl)

declare choose_det [cong]

text {*
  A @{text CHOOSE} expression evaluates to @{text default} if the only
  possible value satisfying the predicate equals @{text default}. Note
  that the reverse implication is not necessarily true: there could be
  several values satisfying @{text "P(x)"}, including @{text default},
  and @{text CHOOSE} may return @{text default}. This rule can be useful
  for reasoning about \textsc{case} expressions where none of the guards
  is true.
*}

lemma equal_default [intro!]:
  assumes p: "\<forall>x : P(x) \<Rightarrow> x = default"
  shows "(CHOOSE x : P(x)) = default"
proof (cases "\<exists>x : P(x)")
  case True
  then obtain a where a: "P(a)" ..
  thus ?thesis proof (rule chooseI2[where P=P])
    fix x
    assume "P(x)"
    with p show "x = default" by blast
  qed
next
  case False thus ?thesis
    unfolding default_def by (blast intro: choose_det)
qed

lemmas [intro!] = sym[OF equal_default, standard]

text {*
  Similar lemma for @{text arbitrary}.
*}

lemma equal_arbitrary:
  assumes p: "\<forall>x : P(x)"
  shows "(CHOOSE x : P(x)) = arbitrary"
unfolding arbitrary_def proof (rule choose_det)
  fix x
  from p show "P(x) \<Leftrightarrow> TRUE" by blast
qed


subsubsection {* Distributive laws *}

text {* Not active by default. *}

lemma prop_distrib:
  "(P \<and> (Q \<or> R)) = ((P \<and> Q) \<or> (P \<and> R))"
  "((Q \<or> R) \<and> P) = ((Q \<and> P) \<or> (R \<and> P))"
  "(P \<or> (Q \<and> R)) = ((P \<or> Q) \<and> (P \<or> R))"
  "((Q \<and> R) \<or> P) = ((Q \<or> P) \<and> (R \<or> P))"
  "(P \<Rightarrow> (Q \<and> R)) = ((P \<Rightarrow> Q) \<and> (P \<Rightarrow> R))"
  "((P \<and> Q) \<Rightarrow> R) = (P \<Rightarrow> (Q \<Rightarrow> R))"
  "((P \<or> Q) \<Rightarrow> R) = ((P \<Rightarrow> R) \<and> (Q \<Rightarrow> R))"
by auto

lemma quant_distrib:
  "\<And> P Q. (\<exists>x : P(x) \<or> Q(x)) = ((\<exists>x : P(x)) \<or> (\<exists>x : Q(x)))"
  "\<And> P Q. (\<forall>x : P(x) \<and> Q(x)) = ((\<forall>x : P(x)) \<and> (\<forall>x : Q(x)))"
by auto


subsubsection {* Further calculational laws *}

lemma cases_simp (*[simp]*): "((P \<Rightarrow> Q) \<and> (\<not>P \<Rightarrow> Q)) = boolify(Q)"
by auto

end
