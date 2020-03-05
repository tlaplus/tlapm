(*  Title:      TLA+/Tuples.thy
    Author:     Stephan Merz, LORIA
    Copyright (C) 2008-2011  INRIA and Microsoft Corporation
    License:    BSD
    Version:    Isabelle2011-1
    Time-stamp: <2011-10-11 17:39:46 merz>
*)

header {* Tuples and Relations in \tlaplus{} *}

theory Tuples
imports NatOrderings
begin

text {*
  We develop a theory of tuples and relations in \tlaplus{}. Tuples are
  functions whose domains are intervals of the form $1 .. n$, for some
  natural number $n$, and relations are sets of tuples. In particular,
  \tlaplus{} distinguishes between a function and its graph, and we have
  functions to convert between the two. (This is useful, for example,
  when defining functions recursively, as we have a fixed point theorem
  on sets but not on functions.) We also introduce standard notions for
  binary relations, such as orderings, equivalence relations and so on.
*}

subsection {* Sequences and Tuples *}

text {*
  Tuples and sequences are the same mathematical objects in \tlaplus{}, so
  we give elementary definitions for sequences here. Further operations
  on sequences require arithmetic and will be introduced in a separate theory.
*}

definition Seq  -- {* set of finite sequences with elements from $S$ *}
where "Seq(S) \<equiv> UNION { [ 1 .. n \<rightarrow> S] : n \<in> Nat }"

definition isASeq  -- {* characteristic predicate for sequences or tuples *}
where "isASeq(s) \<equiv> isAFcn(s) \<and> (\<exists>n \<in> Nat : DOMAIN s = 1 .. n)"

definition Len  -- {* length of a sequence *}
where "Len(s) \<equiv> CHOOSE n \<in> Nat : DOMAIN s = 1 .. n"

lemma isASeqIsBool [intro!,simp]:
  "isBool(isASeq(s))"
by (simp add: isASeq_def)

lemma boolifyIsASeq [simp]:
  "boolify(isASeq(s)) = isASeq(s)"
by auto

lemma isASeqI [intro (*,simp*)]:
  assumes "isAFcn(s)" and "n \<in> Nat" and "DOMAIN s = 1 .. n"
  shows "isASeq(s)"
using assms by (auto simp: isASeq_def)

lemma SeqIsASeq [elim!]:
  assumes "s \<in> Seq(S)"
  shows "isASeq(s)"
using assms by (auto simp: Seq_def)

lemma LenI [intro]:
  assumes "DOMAIN s = 1 .. n" and "n \<in> Nat"
  shows "Len(s) = n"
proof (unfold Len_def, rule bChooseI2)
  from assms show "\<exists>x \<in> Nat : DOMAIN s = 1 .. x" by blast
next
  fix m
  assume "m \<in> Nat" and "DOMAIN s = 1 .. m"
  with assms show "m = n" by auto
qed

lemma isASeqE [elim]:
  assumes "isASeq(s)"
  and "\<lbrakk>isAFcn(s); DOMAIN s = 1 .. Len(s); Len(s) \<in> Nat\<rbrakk> \<Longrightarrow> P"
  shows "P"
using assms by (auto simp: isASeq_def dest: LenI)

lemma SeqIsAFcn (*[elim!]*):
  assumes "isASeq(s)"
  shows "isAFcn(s)"
using assms by auto

-- {* @{text "s \<in> Seq(S) \<Longrightarrow> isAFcn(s)"} *}
lemmas SeqIsAFcn' (*[elim!]*) = SeqIsASeq[THEN SeqIsAFcn, standard]

lemma LenInNat [simp]:
  assumes "isASeq(s)"
  shows "Len(s) \<in> Nat"
using assms by auto

-- {* @{text "s \<in> Seq(S) \<Longrightarrow> Len(s) \<in> Nat"} *}
lemmas LenInNat' [simp] = SeqIsASeq[THEN LenInNat, standard]

lemma DomainSeqLen [simp]:
  assumes "isASeq(s)"
  shows "DOMAIN s = 1 .. Len(s)"
using assms by auto

-- {* @{text "s \<in> Seq(S) \<Longrightarrow> DOMAIN s = 1 .. Len(s)"} *}
lemmas DomainSeqLen' (*[simp,elim!]*) = SeqIsASeq[THEN DomainSeqLen, standard]

lemma seqEqualI:
  assumes "isASeq(s)" and "isASeq(t)" 
      and "Len(s) = Len(t)" and "\<forall>k \<in> 1 .. Len(t) : s[k] = t[k]"
  shows "s = t"
using assms by (intro fcnEqual[of s t], auto)

lemma seqEqualE:
  assumes "isASeq(s)" and "isASeq(t)" and "s=t"
      and "\<lbrakk> Len(s) = Len(t); \<forall>k \<in> 1 .. Len(t) : s[k] = t[k] \<rbrakk> \<Longrightarrow> P"
  shows "P"
using assms by auto

lemma seqEqualIff:
  assumes "isASeq(s)" and "isASeq(t)"
  shows "(s = t) = (Len(s) = Len(t) \<and> (\<forall>k \<in> 1 .. Len(t) : s[k] = t[k]))"
by (auto elim: seqEqualI[OF assms] seqEqualE[OF assms])

lemma SeqI [intro!]:
  assumes "isASeq(s)" and "\<And>k. k \<in> 1 .. Len(s) \<Longrightarrow> s[k] \<in> S"
  shows "s \<in> Seq(S)"
using assms by (auto simp: Seq_def)

lemma SeqI':  -- {* closer to the definition but probably less useful *}
  assumes "s \<in> [1 .. n \<rightarrow> S]" and "n \<in> Nat"
  shows "s \<in> Seq(S)"
using assms by (auto simp: Seq_def)

lemma SeqE [elim]:
  assumes s: "s \<in> Seq(S)"
  and p: "\<lbrakk>s \<in> [1 .. Len(s) \<rightarrow> S]; Len(s) \<in> Nat\<rbrakk> \<Longrightarrow> P"
  shows "P"
proof (rule p)
  from s show "Len(s) \<in> Nat" by (rule LenInNat')
next
  from s obtain n where "n \<in> Nat" and "s \<in> [1 .. n \<rightarrow> S]"
    by (auto simp: Seq_def)
  with DomainSeqLen'[OF s] show "s \<in> [1 .. Len(s) \<rightarrow> S]" by auto
qed

lemma seqFuncSet:
  assumes "s \<in> Seq(S)"
  shows "s \<in> [1 .. Len(s) \<rightarrow> S]"
using assms by auto

lemma seqElt [elim!]:
  assumes "s \<in> Seq(S)" and "n \<in> Nat" and "1 \<le> n" and "n \<le> Len(s)"
  shows "s[n] \<in> S"
using assms by auto

lemma seqInSeqRange:
  assumes "isASeq(s)"
  shows "s \<in> Seq(Range(s))"
using assms by auto

lemma isASeqInSeq: "isASeq(s) = (\<exists>S: s \<in> Seq(S))"
by (auto elim: seqInSeqRange)


subsection {* Sequences via @{text emptySeq} and @{text Append} *}

text {*
  Sequences can be built from the constructors @{text emptySeq} 
  (written @{text "\<langle>\<rangle>"}) and Append.
*}

definition emptySeq ("(<< >>)")
where "<< >> \<equiv> [x \<in> 1 .. 0 \<mapsto> {}]"

notation (xsymbols)
  emptySeq   ("(\<langle>\<rangle>)")

notation (HTML output)
  emptySeq   ("(\<langle>\<rangle>)")

definition Append :: "[c,c] \<Rightarrow> c"
where "Append(s,e) \<equiv> [k \<in> 1 .. Succ[Len(s)] \<mapsto> IF k = Succ[Len(s)] THEN e ELSE s[k]]"

lemma emptySeqIsASeq [simp,intro!]: "isASeq(\<langle>\<rangle>)"
by (auto simp: emptySeq_def isASeq_def)

-- {* @{text "isAFcn(\<langle>\<rangle>)"} *}
lemmas emptySeqIsAFcn [simp,intro!] = emptySeqIsASeq[THEN SeqIsAFcn]

lemma lenEmptySeq [simp]: "Len(\<langle>\<rangle>) = 0"
by (auto simp: emptySeq_def)

lemma emptySeqInSeq (*[simp,intro!]*): "\<langle>\<rangle> \<in> Seq(S)"
by auto

lemma SeqNotEmpty [simp]:
  "(Seq(S) = {}) = FALSE"
  "({} = Seq(S)) = FALSE"
by auto

lemma appendIsASeq [simp,intro!]:
  assumes s: "isASeq(s)"
  shows "isASeq(Append(s,e))"
using s unfolding Append_def
by (rule isASeqE, intro isASeqI, auto simp del: natIntervalSucc)

-- {* @{text "isASeq(s) \<Longrightarrow> isAFcn(Append(s,e))"}  *}
lemmas appendIsAFcn [simp,intro!] = appendIsASeq[THEN SeqIsAFcn, standard]

lemma domainEmptySeq [simp]: "DOMAIN \<langle>\<rangle> = {}"
by (simp add: emptySeq_def)

lemma domainAppend [simp]: "DOMAIN Append(s,e) = 1 .. Succ[Len(s)]"
by (simp add: Append_def)

lemma isEmptySeq [intro!]:
  "\<lbrakk>isAFcn(f); DOMAIN f = {}\<rbrakk> \<Longrightarrow> f = \<langle>\<rangle>"
  "\<lbrakk>isAFcn(f); DOMAIN f = {}\<rbrakk> \<Longrightarrow> \<langle>\<rangle> = f"
by auto

-- {* immediate consequence of @{text isEmptySeq} *}
lemma emptySeqEmptyFcn: "\<langle>\<rangle> = [x \<in> {} \<mapsto> y]"
by auto

-- {* Symmetric equation could be a useful rewrite rule (it is applied by TLC) *}
lemmas emptyFcnEmptySeq = sym[OF emptySeqEmptyFcn, standard]

lemma emptyDomainIsEmptySeq [simp]: "(f \<in> [{} \<rightarrow> S]) = (f = \<langle>\<rangle>)"
by auto

lemma seqLenZeroIsEmpty (*used to be [simp], but emptySeqIff seems more useful*):
  assumes "isASeq(s)"
  shows "(Len(s) = 0) = (s = \<langle>\<rangle>)"
using assms by auto

lemma emptySeqIff [simp]:
  assumes "isAFcn(s)"
  shows "(s = \<langle>\<rangle>) = (DOMAIN s = {} \<and> Len(s) = 0)"
using assms by auto

lemma emptySeqIff' [simp]:
  assumes "isAFcn(s)"
  shows "(\<langle>\<rangle> = s) = (DOMAIN s = {} \<and> Len(s) = 0)"
using assms by auto

lemma lenAppend [simp]:
  assumes "isASeq(s)"
  shows "Len(Append(s,e)) = Succ[Len(s)]"
using assms by (intro LenI, auto simp: Append_def)

-- {* @{text "s \<in> Seq(S) \<Longrightarrow> Len(Append(s,e)) = Succ[Len(s)]"} *}
lemmas lenAppend' [simp] = SeqIsASeq[THEN lenAppend, standard]

lemma appendElt [simp]:
  assumes "isASeq(s)" and "k \<in> Nat" and "0 < k" and "k \<le> Succ[Len(s)]"
  shows "Append(s,e)[k] = (IF k = Succ[Len(s)] THEN e ELSE s[k])"
using assms by (auto simp: Append_def)

lemmas appendElt' [simp] = SeqIsASeq[THEN appendElt, standard]

lemma appendElt1 (*[simp]*):
  assumes "isASeq(s)" and "k \<in> Nat" and "0 < k" and "k \<le> Len(s)"
  shows "Append(s,e)[k] = s[k]"
using assms by (auto simp: Append_def)

lemmas appendElt1' (*[simp]*) = SeqIsASeq[THEN appendElt1, standard]

lemma appendElt2 (*[simp]*):
  assumes "isASeq(s)"
  shows "Append(s,e)[Succ[Len(s)]] = e"
using assms by (auto simp: Append_def)
  
lemmas appendElt2' (*[simp]*) = SeqIsASeq[THEN appendElt2, standard]

lemma isAppend [intro!]:
  assumes f: "isAFcn(f)" and dom: "DOMAIN f = 1 .. Succ[Len(s)]" and s: "isASeq(s)"
  and elt1: "\<forall>n \<in> 1 .. Len(s) : f[n] = s[n]" and elt2: "f[Succ[Len(s)]] = e"
  shows "f = Append(s,e)"
proof (rule fcnEqual[OF f])
  from s show "isAFcn(Append(s,e))" by simp
next
  from dom show "DOMAIN f = DOMAIN Append(s,e)" by simp
next
  from s elt1 elt2 show "\<forall>x \<in> DOMAIN Append(s, e) : f[x] = Append(s, e)[x]"
    by (auto simp: Append_def)
qed

lemmas isAppend' [intro!] = isAppend[symmetric, standard]

lemma appendInSeq [simp]:
  assumes s: "s \<in> Seq(S)" and e: "e \<in> S"
  shows "Append(s,e) \<in> Seq(S)"
using assms by (force simp: nat_leq_Succ)

lemma appendD1:
  assumes s: "isASeq(s)" and t: "isASeq(t)" and app: "Append(s,e) = Append(t,f)"
  shows "s = t"
proof -
  let ?s1 = "Append(s,e)"
  let ?t1 = "Append(t,f)"
  from s have 1: "isASeq(?s1)" by simp
  from t have 2: "isASeq(?t1)" by simp
  from 1 2 app have len: "Len(?s1) = Len(?t1)" and elt: "\<forall>k \<in> 1 .. Len(?t1) : ?s1[k] = ?t1[k]"
    by (blast elim: seqEqualE)+
  from s t len have ls: "Len(s) = Len(t)" by simp
  thus ?thesis
  proof (rule seqEqualI[OF s t], auto)
    fix k
    assume k: "k \<in> 1 .. Len(t)"
    with s ls have "s[k] = ?s1[k]" by (intro sym[OF appendElt1], auto)
    also from k elt t have "... = ?t1[k]" by auto
    also from t k have "... = t[k]" by (intro appendElt1, auto)
    finally show "s[k] = t[k]" .
  qed
qed

lemma appendD2:
  assumes s: "isASeq(s)" and t: "isASeq(t)" and app: "Append(s,e) = Append(t,f)"
  shows "e = f"
proof -
  let ?s1 = "Append(s,e)"
  let ?t1 = "Append(t,f)"
  from s have 1: "isASeq(?s1)" by simp
  from t have 2: "isASeq(?t1)" by simp
  from 1 2 app have "Len(?s1) = Len(?t1)" and "\<forall>k \<in> 1 .. Len(?t1) : ?s1[k] = ?t1[k]"
    by (blast elim: seqEqualE)+
  with s t have "?s1[Len(?s1)] = ?t1[Len(?t1)]" by auto
  with s t show ?thesis by simp
qed

lemma appendEqualIff [simp]:
  assumes s: "isASeq(s)" and t: "isASeq(t)"
  shows "(Append(s,e) = Append(t,f)) = (s = t \<and> e = f)"
using appendD1[OF s t] appendD2[OF s t] by auto

text {*
  The following lemma gives a possible alternative definition of
  @{text Append}.
*}

lemma appendExtend:
  assumes "isASeq(s)"
  shows "Append(s,e) = s @@ (Succ[Len(s)] :> e)"
using assms by force

lemma imageEmptySeq [simp]: "Image(\<langle>\<rangle>, A) = {}"
by (simp add: emptySeq_def)

lemma imageAppend [simp]:
  assumes s: "isASeq(s)"
  shows "Image(Append(s,e), A) = 
         (IF Succ[Len(s)] \<in> A THEN addElt(e, Image(s,A)) ELSE Image(s,A))"
unfolding appendExtend[OF s]
using assms by (auto elim!: inNatIntervalE, force+)

text {*
  Inductive reasoning about sequences, based on @{term "\<langle>\<rangle>"} and
  @{text Append}.
*}

lemma seqInduct [case_names empty append, induct set: Seq]:
  assumes s: "s \<in> Seq(S)"
  and base: "P(\<langle>\<rangle>)"
  and step: "\<And>s e. \<lbrakk>s \<in> Seq(S); e \<in> S; P(s)\<rbrakk> \<Longrightarrow> P(Append(s,e))"
  shows "P(s)"
proof -
  have "\<forall>n \<in> Nat : \<forall>s \<in> [1 .. n \<rightarrow> S] : P(s)" (is "\<forall>n \<in> Nat : ?A(n)")
  proof (rule natInduct)
    from base show "?A(0)" by (auto del: funcSetE')
  next
    fix n
    assume n: "n \<in> Nat" and ih: "?A(n)"
    show "?A(Succ[n])"
    proof
      fix sn
      assume sn: "sn \<in> [1 .. Succ[n] \<rightarrow> S]"
      def so \<equiv> "[k \<in> 1 .. n \<mapsto> sn[k]]"
      def lst \<equiv> "sn[Succ[n]]"
      have 1: "sn = Append(so, lst)"
      proof
	from sn show "isAFcn(sn)" by simp
      next
	from sn n show "DOMAIN sn = 1 .. Succ[Len(so)]"
	  by (simp add: so_def LenI)
      next
	from n show "isASeq(so)" by (force simp: so_def)
      next
        from n show "\<forall>k \<in> 1 .. Len(so) : sn[k] = so[k]"
          by (auto simp: so_def LenI)
      next
	from n show "sn[Succ[Len(so)]] = lst"
	  by (simp add: so_def lst_def LenI)
      qed
      from sn n have 2: "so \<in> [1 .. n \<rightarrow> S]"
	by (force simp: so_def)
      with ih have 3: "P(so)" ..
      from 2 n have 4: "so \<in> Seq(S)"
        unfolding Seq_def by auto
      from sn n have "lst \<in> S" by (auto simp: lst_def)
      with 1 3 4 show "P(sn)" by (auto intro: step)
    qed
  qed
  with s show ?thesis unfolding Seq_def by auto
qed

-- {* example of an inductive proof about sequences *}
lemma seqEmptyOrAppend:
  assumes "s \<in> Seq(S)"
  shows "s = \<langle>\<rangle> \<or> (\<exists>s' \<in> Seq(S): \<exists>e \<in> S : s = Append(s',e))"
using assms by (induct s, auto)

lemma seqCases [case_names Empty Append, cases set: Seq]:
  assumes "s \<in> Seq(S)"
  and "s = \<langle>\<rangle> \<Longrightarrow> P" and "\<And>t e. \<lbrakk>t \<in> Seq(S); e \<in> S; s = Append(t,e)\<rbrakk> \<Longrightarrow> P"
  shows "P"
using assms by (auto dest: seqEmptyOrAppend)


subsection {* Enumerated sequences *}

text {*
  We introduce the conventional syntax @{text "\<langle>a,b,c\<rangle>"} for tuples
  and enumerated sequences, based on the above constructors.
*}

nonterminal tpl

syntax
  ""         ::  "c \<Rightarrow> tpl"          ("_")
  "@app"     ::  "[tpl, c] \<Rightarrow> tpl"   ("_,/ _")
  "@tuple"   ::  "tpl \<Rightarrow> c"          ("<<(_)>>")

syntax (xsymbols)
  "@tuple"   ::  "tpl \<Rightarrow> c"          ("\<langle>(_)\<rangle>")

syntax (HTML output)
  "@tuple"   ::  "tpl \<Rightarrow> c"          ("\<langle>(_)\<rangle>")

translations
  "\<langle> tp, x \<rangle>" \<rightleftharpoons>  "CONST Append(\<langle>tp\<rangle>, x)"
  "\<langle> x \<rangle>"     \<rightleftharpoons>  "CONST Append(\<langle>\<rangle>, x)"


(*** examples ***
lemma "Len(\<langle>a,b,c\<rangle>) = 3" by simp

lemma "Append(\<langle>a,b\<rangle>, c) = \<langle>a,b,c\<rangle>" ..

lemma "\<langle>a,b,c\<rangle>[1] = a" by simp
lemma "\<langle>a,b,c\<rangle>[2] = b" by simp
lemma "\<langle>a,b,c\<rangle>[3] = c" by simp
lemma "\<langle>0,1\<rangle> \<noteq> \<langle>\<rangle>" by simp
lemma "\<langle>0,1\<rangle> \<noteq> \<langle>1\<rangle>" by simp
lemma "\<langle>0,1\<rangle> \<noteq> \<langle>1,2\<rangle>" by simp
lemma "\<langle>0,1\<rangle> \<noteq> \<langle>1,2,3\<rangle>" by simp
lemma "(\<langle>a,b\<rangle> = \<langle>c,d\<rangle>) = (a=c \<and> b=d)" by simp
***)

text {* 
  \tlaplus{} has a form of quantification over tuples written
  $\exists \langle x,y,z \rangle \in S: P(x,y,z)$. We cannot give a generic
  definition of this form for arbitrary tuples, but introduce input syntax
  for tuples of length up to $5$.
*}

syntax
  "@bEx2"  ::  "[idt,idt,c,c] \<Rightarrow> c"  ("(3EX <<_,_>> in _ :/ _)" [100,100,0,0] 10)
  "@bEx3"  ::  "[idt,idt,idt,c,c] \<Rightarrow> c"  ("(3EX <<_,_,_>> in _ :/ _)" [100,100,100,0,0] 10)
  "@bEx4"  ::  "[idt,idt,idt,idt,c,c] \<Rightarrow> c"  ("(3EX <<_,_,_,_>> in _ :/ _)" [100,100,100,100,0,0] 10)
  "@bEx5"  ::  "[idt,idt,idt,idt,idt,c,c] \<Rightarrow> c"  ("(3EX <<_,_,_,_,_>> in _ :/ _)" [100,100,100,100,100,0,0] 10)
  "@bAll2" ::  "[idt,idt,c,c] \<Rightarrow> c"  ("(3ALL <<_,_>> in _ :/ _)" [100,100,0,0] 10)
  "@bAll3" ::  "[idt,idt,idt,c,c] \<Rightarrow> c"  ("(3ALL <<_,_,_>> in _ :/ _)" [100,100,100,0,0] 10)
  "@bAll4" ::  "[idt,idt,idt,idt,c,c] \<Rightarrow> c"  ("(3ALL <<_,_,_,_>> in _ :/ _)" [100,100,100,100,0,0] 10)
  "@bAll5" ::  "[idt,idt,idt,idt,idt,c,c] \<Rightarrow> c"  ("(3ALL <<_,_,_,_,_>> in _ :/ _)" [100,100,100,100,100,0,0] 10)

syntax (xsymbols)
  "@bEx2"  :: "[idt,idt,c,c] \<Rightarrow> c"   ("(3\<exists>\<langle>_,_\<rangle> \<in> _ :/ _)" [100,100,0,0] 10)
  "@bEx3"  :: "[idt,idt,idt,c,c] \<Rightarrow> c"   ("(3\<exists>\<langle>_,_,_\<rangle> \<in> _ :/ _)" [100,100,100,0,0] 10)
  "@bEx4"  :: "[idt,idt,idt,idt,c,c] \<Rightarrow> c"   ("(3\<exists>\<langle>_,_,_,_\<rangle> \<in> _ :/ _)" [100,100,100,100,0,0] 10)
  "@bEx5"  :: "[idt,idt,idt,idt,idt,c,c] \<Rightarrow> c"   ("(3\<exists>\<langle>_,_,_,_,_\<rangle> \<in> _ :/ _)" [100,100,100,100,100,0,0] 10)
  "@bAll2" :: "[idt,idt,c,c] \<Rightarrow> c"   ("(3\<forall>\<langle>_,_\<rangle> \<in> _ :/ _)" [100,100,0,0] 10)
  "@bAll3" :: "[idt,idt,idt,c,c] \<Rightarrow> c"   ("(3\<forall>\<langle>_,_,_\<rangle> \<in> _ :/ _)" [100,100,100,0,0] 10)
  "@bAll4" :: "[idt,idt,idt,idt,c,c] \<Rightarrow> c"   ("(3\<forall>\<langle>_,_,_,_\<rangle> \<in> _ :/ _)" [100,100,100,100,0,0] 10)
  "@bAll5" :: "[idt,idt,idt,idt,idt,c,c] \<Rightarrow> c"   ("(3\<forall>\<langle>_,_,_,_,_\<rangle> \<in> _ :/ _)" [100,100,100,100,100,0,0] 10)

translations
  "\<exists>\<langle>x,y\<rangle> \<in> S : P"        \<rightharpoonup>  "\<exists>x,y : \<langle>x,y\<rangle> \<in> S \<and> P"
  "\<exists>\<langle>x,y,z\<rangle> \<in> S : P"      \<rightharpoonup>  "\<exists>x,y,z : \<langle>x,y,z\<rangle> \<in> S \<and> P"
  "\<exists>\<langle>x,y,z,u\<rangle> \<in> S : P"    \<rightharpoonup>  "\<exists>x,y,z,u : \<langle>x,y,z,u\<rangle> \<in> S \<and> P"
  "\<exists>\<langle>x,y,z,u,v\<rangle> \<in> S : P"  \<rightharpoonup>  "\<exists>x,y,z,u,v : \<langle>x,y,z,u,v\<rangle> \<in> S \<and> P"
  "\<forall>\<langle>x,y\<rangle> \<in> S : P"        \<rightharpoonup>  "\<forall>x,y : \<langle>x,y\<rangle> \<in> S \<Rightarrow> P"
  "\<forall>\<langle>x,y,z\<rangle> \<in> S : P"      \<rightharpoonup>  "\<forall>x,y,z : \<langle>x,y,z\<rangle> \<in> S \<Rightarrow> P"
  "\<forall>\<langle>x,y,z,u\<rangle> \<in> S : P"    \<rightharpoonup>  "\<forall>x,y,z,u : \<langle>x,y,z,u\<rangle> \<in> S \<Rightarrow> P"
  "\<forall>\<langle>x,y,z,u,v\<rangle> \<in> S : P"  \<rightharpoonup>  "\<forall>x,y,z,u,v : \<langle>x,y,z,u,v\<rangle> \<in> S \<Rightarrow> P"

subsection {* Sets of finite functions *}

text {*
  We introduce notation such as @{text "[x: S, y: T]"} to designate the
  set of finite functions @{text f} with domain @{text "{x,y}"} (for constants
  @{text x}, @{text y}) such that @{text "f[x] \<in> S"} and @{text "f[y] \<in> T"}.
  Typically, elements of such a function set will be constructed as
  @{text "(x :> s)@@(y :> t)"}.
  This notation for sets of finite functions generalizes similar 
  \tlaplus{} notation for records.

  Internally, the set is represented as @{text "EnumFuncSet(\<langle>x,y\<rangle>, \<langle>S,T\<rangle>)"},
  using appropriate translation functions between the internal and external
  representations.
*}

definition EnumFuncSet :: "c \<Rightarrow> c \<Rightarrow> c"
where "EnumFuncSet(doms, rngs) \<equiv> { f \<in> [Range(doms) \<rightarrow> UNION Range(rngs)] :
                                     \<forall>i \<in> DOMAIN doms : f[doms[i]] \<in> rngs[i] }"

lemmas -- {* establish set equality for sets of enumerated functions *}
  setEqualI [where A = "EnumFuncSet(doms, rngs)", standard, intro!]
  setEqualI [where B = "EnumFuncSet(doms, rngs)", standard, intro!]

lemma EnumFuncSetI [intro!,simp]:
  assumes 1: "isAFcn(f)" and 2: "DOMAIN f = Range(doms)"
      and 3: "DOMAIN rngs = DOMAIN doms"
      and 4: "\<forall>i \<in> DOMAIN doms: f[doms[i]] \<in> rngs[i]"
  shows "f \<in> EnumFuncSet(doms, rngs)"
(** using assms by (force simp: EnumFuncSet_def) -- works, slow **)
proof -
  from 1 2 have "f \<in> [Range(doms) \<rightarrow> UNION Range(rngs)]"
  proof
    from 3 4 show "\<forall>x \<in> Range(doms) : f[x] \<in> UNION Range(rngs)" by force
  qed
  with 4 show ?thesis by (simp add: EnumFuncSet_def)
qed

lemma EnumFuncSetE [elim!]:
  assumes "f \<in> EnumFuncSet(doms, rngs)"
      and "\<lbrakk>f \<in> [Range(doms) \<rightarrow> UNION Range(rngs)]; 
              \<forall>i \<in> DOMAIN doms : f[doms[i]] \<in> rngs[i] \<rbrakk> \<Longrightarrow> P"
  shows "P"
using assms by (auto simp: EnumFuncSet_def)

nonterminal domrng and domrngs

syntax
  "@domrng"     :: "[c, c] \<Rightarrow> domrng"             ("(2_ :/ _)" 10)
  ""            :: "domrng \<Rightarrow> domrngs"            ("_")
  "@domrngs"    :: "[domrng, domrngs] \<Rightarrow> domrngs" ("_,/ _")
  "@EnumFuncSet":: "domrngs \<Rightarrow> c"                 ("[_]")

parse_ast_translation {*
  let
    (* make_tuple converts a list of ASTs to a tuple formed from these ASTs.
       The order of elements is reversed. *)
    fun make_tuple [] = Ast.Constant "emptySeq"
      | make_tuple (t :: ts) = Ast.Appl[Ast.Constant "Append", make_tuple ts, t]
    (* get_doms_ranges extracts the lists of arguments and ranges
       from the arms of a "domrngs" expression.
       The order of the ASTs is reversed. *)
    fun get_doms_ranges (Ast.Appl[Ast.Constant "@domrng", d, r]) = 
            (* base case: one domain, one range *)
            ([d], [r])
      | get_doms_ranges (Ast.Appl[Ast.Constant "@domrngs", 
                                    Ast.Appl[Ast.Constant "@domrng", d, r], 
                                    pairs]) =
            (* one domrng, followed by remaining doms and ranges *)
            let val (ds, rs) = get_doms_ranges pairs
            in  (ds @ [d], rs @ [r])
            end
    fun enum_funcset_tr [pairs] =
        let val (doms, rngs) = get_doms_ranges pairs
            val dTuple = make_tuple doms
            val rTuple = make_tuple rngs
        in
          Ast.Appl[Ast.Constant "EnumFuncSet", dTuple, rTuple]
        end
      | enum_funcset_tr _ = raise Match;
  in
    [("@EnumFuncSet", enum_funcset_tr)]
  end
*}

print_ast_translation {*
  let
    fun list_from_tuple (Ast.Constant @{const_syntax "emptySeq"}) = []
      | list_from_tuple (Ast.Appl[Ast.Constant "@tuple", tp]) =
        let fun list_from_tp (Ast.Appl[Ast.Constant "@app", tp, t]) =
                     (list_from_tp tp) @ [t]
              | list_from_tp t = [t]
        in  list_from_tp tp
        end
    (* make_domrngs constructs an AST representing the domain/range pairs.
       The result is an AST of "type" domrngs.
       The lists of domains and ranges must be of equal length and non-empty. *)
    fun make_domrngs [d] [r] = Ast.Appl[Ast.Constant @{syntax_const "@domrng"}, d, r]
      | make_domrngs (d::ds) (r::rs) =
            Ast.Appl[Ast.Constant @{syntax_const "@domrngs"},
                 Ast.Appl[Ast.Constant @{syntax_const "@domrng"}, d, r],
                 make_domrngs ds rs]
    fun enum_funcset_tr' [dTuple, rTuple] =
        let val doms = list_from_tuple dTuple
            val rngs = list_from_tuple rTuple
        in  (* make sure that lists are of equal length, otherwise give up *)
            if length doms = length rngs
            then Ast.Appl[Ast.Constant @{syntax_const "@EnumFuncSet"}, make_domrngs doms rngs]
            else raise Match
        end
      | enum_funcset_tr' _ = raise Match
  in
    [(@{const_syntax "EnumFuncSet"}, enum_funcset_tr')]
  end
*}

(*** Examples ***

lemma "(1 :> TRUE) \<in> [1 : BOOLEAN]"
by auto

lemma "(1 :> TRUE) @@ (5 :> 2) \<in> [1 : BOOLEAN, 5 : Nat]"
by auto

lemma "(1 :> TRUE @@ 5 :> 2) = (5 :> 2 @@ 1 :> TRUE)"
by auto

lemma "(1 :> TRUE) @@ (5 :> 2) @@ (2 :> {}) \<in> [1 : BOOLEAN, 2: SUBSET Nat, 5 : Nat]"
by auto

lemma "[((1 :> TRUE) @@ (5 :> 2)) EXCEPT ![1] = FALSE] \<in> [1 : BOOLEAN, 5 : Nat]"
by auto

lemma "[((1 :> TRUE) @@ (5 :> 2)) EXCEPT ![5] = {}] \<in> [1 : BOOLEAN, 5 : SUBSET Nat]"
by auto

lemma "(1 :> TRUE) @@ (5 :> 2) @@ (1 :> {}) \<in> [1 : BOOLEAN, 5 : Nat]"
by auto

lemma "[1 : BOOLEAN, 5 : Nat] = [5 : Nat, 1 : BOOLEAN]"
by auto

lemma "\<lbrakk>f \<in> [1 : BOOLEAN, 2: Nat]; g \<in> [2: Nat, 1: BOOLEAN]; f[1] = g[1]; f[2] = g[2]\<rbrakk> \<Longrightarrow> f = g"
by auto

***)

subsection {* Set product *}

text {*
  The cartesian product of two sets $A$ and $B$ is the set of pairs
  whose first component is in $A$ and whose second component is in $B$.
  We generalize the definition of products to an arbitrary number of sets:
  $Product(\langle A_1,\ldots,A_n \rangle) = A_1 \times\cdots\times A_n$.
*}

definition Product
where "Product(s) \<equiv> { f \<in> [1 .. Len(s) \<rightarrow> UNION Range(s)] : 
                      \<forall>i \<in> 1 .. Len(s) : f[i] \<in> s[i] }"

lemma inProductI [intro!]:
  assumes "isASeq(p)" and "isASeq(s)" and "Len(p) = Len(s)"
  and "\<forall>k \<in> 1 .. Len(s) : p[k] \<in> s[k]"
  shows "p \<in> Product(s)"
using assms by (auto simp add: Product_def)

lemma inProductIsASeq:
  assumes "p \<in> Product(s)" and "isASeq(s)"
  shows "isASeq(p)"
using assms by (auto simp add: Product_def)

lemma inProductLen:
  assumes "p \<in> Product(s)" and "isASeq(s)"
  shows "Len(p) = Len(s)"
using assms by (auto simp add: Product_def)

lemma inProductE [elim!]:
  assumes "p \<in> Product(s)" and "isASeq(s)"
  and "\<lbrakk>isASeq(p); Len(p) = Len(s); p \<in> [1 .. Len(s) \<rightarrow> UNION Range(s)]; 
        \<forall>k \<in> 1 .. Len(s) : p[k] \<in> s[k] \<rbrakk> \<Longrightarrow> P"
  shows "P"
using assms by (auto simp add: Product_def)

(*** examples ***
lemma "Product(\<langle>\<rangle>) = { \<langle>\<rangle> }" by auto

lemma "\<langle>2,1\<rangle> \<in> Product(\<langle>Nat, Nat\<rangle>)" by auto

lemma
  assumes "x \<in> X" and "y \<in> Y" and "z \<in> Z"
  shows "\<langle>x,y,z\<rangle> \<in> Product(\<langle>X,Y,Z\<rangle>)"
using assms by auto

lemma
  assumes "\<langle>x,y,z\<rangle> \<in> Product(\<langle>X,Y,Z\<rangle>)"
  shows "y \<in> Y"
using assms by auto

lemma
  "\<langle>a,b\<rangle> \<in> Product(\<langle>A,B\<rangle>) \<Leftrightarrow> (a \<in> A \<and> b \<in> B)"
by auto

lemma
  assumes "f \<in> Product(\<langle>A,B\<rangle>)"
  shows "f[1] \<in> A"
using assms by auto

lemma
  fixes N
fixes f
assumes "f \<in> Product(<<N, N>>)"
shows "{f[1], f[2]} \<in> { {m[1], m[2]} : m \<in> Product(\<langle>N,N\<rangle>) }"
using assms by auto

lemma "\<langle>\<rangle> \<notin> Product(\<langle>A,B\<rangle>)" by auto
lemma "\<langle>a\<rangle> \<notin> Product(\<langle>A,B\<rangle>)" by auto

***)

text {* Special case: binary product *}

definition
  prod :: "c \<Rightarrow> c \<Rightarrow> c"     (infixr "\\X" 100) where
  "A \\X B \<equiv> Product(\<langle>A,B\<rangle>)"
notation (xsymbols)
  prod                     (infixr "\<times>" 100)
notation (HTML output)
  prod                     (infixr "\<times>" 100)

lemma inProd [simp]:
  "(\<langle>a,b\<rangle> \<in> A \<times> B) = (a \<in> A \<and> b \<in> B)"
by (auto simp add: prod_def)

lemma prodProj:
  assumes p: "p \<in> A \<times> B"
  shows "p = \<langle>p[1], p[2]\<rangle>"
using assms by (auto simp add: prod_def)

lemma inProd':
  "(p \<in> A \<times> B) = (\<exists>a \<in> A : \<exists> b \<in> B : p = \<langle>a,b\<rangle>)"
proof (auto)
  assume p: "p \<in> A \<times> B"
  hence 1: "p = \<langle>p[1], p[2]\<rangle>" by (rule prodProj)
  with p have "\<langle>p[1], p[2]\<rangle> \<in> A \<times> B" by simp
  hence "p[1] \<in> A" "p[2] \<in> B" by auto
  with 1 show "\<exists>a \<in> A : \<exists>b \<in> B : p = \<langle>a, b\<rangle>" by auto
qed

lemma inProdI [intro]:
  assumes a: "a \<in> A" and b: "b \<in> B" and p: "P(\<langle>a,b\<rangle>)"
  shows "\<exists>p \<in> A \<times> B : P(p)"
using assms by (intro bExI[of "\<langle>a,b\<rangle>"], simp+)

lemma inProdI':
  assumes a: "a \<in> A" and b: "b \<in> B"
  obtains p where "p \<in> A \<times> B" and "p[1] = a" and "p[2] = b"
proof
  from a b show "\<langle>a,b\<rangle> \<in> A \<times> B" by simp
next
  show "\<langle>a,b\<rangle>[1] = a" by simp
next
  show "\<langle>a,b\<rangle>[2] = b" by simp
qed

lemma inProdE [elim]:
  assumes "p \<in> A \<times> B"
  and "\<And>a b. \<lbrakk>a \<in> A; b \<in> B; p = \<langle>a,b\<rangle>\<rbrakk> \<Longrightarrow> P"
  shows "P"
using assms by (auto simp add: inProd')

(*** examples ***
lemma "\<langle>2,1\<rangle> \<in> Nat \<times> Nat" by simp
***)

lemma prodEmptyIff [simp]:
  "(A \<times> B = {}) = ((A = {}) \<or> (B = {}))"
proof auto
  fix a b
  assume a: "a \<in> A" and b: "b \<in> B" and prod: "A \<times> B = {}"
  from a b have "\<langle>a,b\<rangle> \<in> A \<times> B" by simp
  with prod show "FALSE" by blast
qed

lemma prodEmptyIff' [simp]:
  "({} = A \<times> B) = ((A = {}) \<or> (B = {}))"
proof auto
  fix a b
  assume a: "a \<in> A" and b: "b \<in> B" and prod: "{} = A \<times> B"
  from a b have "\<langle>a,b\<rangle> \<in> A \<times> B" by simp
  with prod show "FALSE" by blast
qed

lemma pairProj_in_rel (*[simp]*):
  assumes r: "r \<subseteq> A \<times> B" and p: "p \<in> r"
  shows "\<langle>p[1],p[2]\<rangle> \<in> r"
using p prodProj[OF rev_subsetD[OF p r], symmetric] by simp

lemma pairProj_in_prod (*[simp]*):
  assumes r: "r \<subseteq> A \<times> B" and p: "p \<in> r"
  shows "\<langle>p[1],p[2]\<rangle> \<in> A \<times> B"
using subsetD[OF r p] prodProj[OF rev_subsetD[OF p r], symmetric] by simp

lemma relProj1 [elim]:  (** consider [elim!] ?? **)
  assumes "\<langle>a,b\<rangle> \<in> r" and "r \<subseteq> A \<times> B"
  shows "a \<in> A"
using assms by (auto dest: pairProj_in_prod)

lemma relProj2 [elim]:  (** consider [elim!] ?? **)
  assumes "\<langle>a,b\<rangle> \<in> r" and "r \<subseteq> A \<times> B"
  shows "b \<in> B"
using assms by (auto dest: pairProj_in_prod)

lemma setOfAllPairs_eq_r (*[simp]*):
  assumes r: "r \<subseteq> A \<times> B"
  shows "{\<langle>p[1], p[2]\<rangle> : p \<in> r} = r"
apply auto
using subsetD[OF r, THEN prodProj[of _ A B]] by simp_all

lemma subsetsInProd:
  assumes "A' \<subseteq> A" and "B' \<subseteq> B"
  shows "A' \<times> B' \<subseteq> A \<times> B"
unfolding prod_def Product_def
using assms by auto


subsection {* Syntax for setOfPairs: @{text "{e : \<langle>x,y\<rangle> \<in> R}"} *}

definition setOfPairs :: "[c, [c,c]\<Rightarrow>c] \<Rightarrow> c"
where "setOfPairs(R, f) \<equiv> { f(p[1], p[2]) : p \<in> R }"

syntax
  "@setOfPairs" :: "[c, idt, idt, c] \<Rightarrow> c"         ("(1{_ : <<_,_>> \\in _})")
syntax (xsymbols)
  "@setOfPairs" :: "[c, idt, idt, c] \<Rightarrow> c"         ("(1{_ : \<langle>_,_\<rangle> \<in> _})")
translations
  "{e : \<langle>x,y\<rangle> \<in> R}" \<rightleftharpoons>  "CONST setOfPairs(R, \<lambda>x y. e)"

lemma inSetOfPairsI_ex:
  assumes "\<exists>\<langle>x,y\<rangle> \<in> R : a = e(x,y)"
  shows "a \<in> { e(x,y) : \<langle>x,y\<rangle> \<in> R }"
using assms by (auto simp: setOfPairs_def)

lemma inSetOfPairsI [intro]:
  assumes "a = e(x,y)" and "\<langle>x,y\<rangle> \<in> R"
  shows "a \<in> setOfPairs(R, e)"
using assms by (auto simp: setOfPairs_def)

lemma inSetOfPairsE [elim!]: -- {* converse true only if $R$ is a relation *}
  assumes 1: "z \<in> setOfPairs(R, e)" 
      and 2: "R \<subseteq> A \<times> B" and 3: "\<And>x y. \<lbrakk> \<langle>x,y\<rangle> \<in> R; z = e(x,y) \<rbrakk> \<Longrightarrow> P"
  shows "P"
proof -
  from 1 obtain p where pR: "p \<in> R" and pz: "z = e(p[1],p[2])"
    by (auto simp: setOfPairs_def)
  from pR 2 have "p = \<langle>p[1], p[2]\<rangle>" by (intro prodProj, auto)
  with pR pz show "P" by (intro 3, auto)
qed

lemmas setOfPairsEqualI = 
  setEqualI [where A = "setOfPairs(R,f)", standard,intro!]
  setEqualI [where B = "setOfPairs(R,f)", standard,intro!]

lemma setOfPairs_triv [simp]: 
  assumes s: "R \<subseteq> A \<times> B" 
  shows "{ \<langle>x,y\<rangle> : \<langle>x,y\<rangle> \<in> R } = R"
using assms by auto

lemma setOfPairs_cong (*[cong]*):
  assumes 1: "R = S" and 2: "S \<subseteq> A \<times> B" and 3: "\<And>x y. \<langle>x,y\<rangle> \<in> S \<Longrightarrow> e(x,y) = f(x,y)"
  shows "{ e(x,y) : \<langle>x,y\<rangle> \<in> R } = { f(u,v) : \<langle>u,v\<rangle> \<in> S }"
using assms proof (auto)
  fix u v
  let ?p = "\<langle>u,v\<rangle>"
  assume uv: "?p \<in> S"
  with 3 have "f(u,v) = e(?p[1], ?p[2])" by simp
  with uv show "f(u,v) \<in> setOfPairs(S, e)" by auto
qed

lemma setOfPairsEqual:
  assumes 1: "\<And>x y. \<langle>x,y\<rangle> \<in> S \<Longrightarrow> \<exists>\<langle>x',y'\<rangle> \<in> T : e(x,y) = f(x',y')"
  and 2: "\<And>x' y'. \<langle>x',y'\<rangle> \<in> T \<Longrightarrow> \<exists>\<langle>x,y\<rangle>\<in>S : f(x',y') = e(x,y)"
  and 3: "S \<subseteq> A \<times> B" and 4: "T \<subseteq> C \<times> D"
  shows "{ e(x,y) : \<langle>x,y\<rangle> \<in> S } = { f(x,y) : \<langle>x,y\<rangle> \<in> T }"
using assms by (auto, blast+)


subsection {* Basic notions about binary relations *}

definition rel_domain :: "c => c"
where "rel_domain(r) \<equiv> { p[1] : p \<in> r }"

definition rel_range :: "c => c"
where "rel_range(r) \<equiv> { p[2] : p \<in> r }"

definition converse :: "c => c" ("(_^-1)" [1000] 999)
where "r^-1 \<equiv> { \<langle>p[2],p[1]\<rangle> : p \<in> r}"

definition rel_comp :: "[c,c] => c" (infixr "\<circ>" 75) -- {* binary relation composition *}
where "r \<circ> s \<equiv> { p \<in> rel_domain(s) \<times> rel_range(r) : 
                 \<exists>x,z : p = \<langle>x,z\<rangle> \<and> (\<exists>y: \<langle>x,y\<rangle> \<in> s \<and> \<langle>y,z\<rangle> \<in> r) }"

definition rel_image :: "[c,c] => c" (infixl "``" 90)
where "r `` A  \<equiv> {y \<in> rel_range(r) : \<exists>x \<in> A: \<langle>x,y\<rangle> \<in> r}"

definition Id :: "c \<Rightarrow> c"    -- {* diagonal: identity over a set *}
where "Id(A) \<equiv> { \<langle>x,x\<rangle> : x \<in> A }"


text {* Properties of relations *}

definition reflexive   -- {* reflexivity over a set *}
where "reflexive(A,r) \<equiv> \<forall>x \<in> A: \<langle>x,x\<rangle> \<in> r"

lemma boolifyReflexive [simp]: "boolify(reflexive(A,r)) = reflexive(A,r)"
unfolding reflexive_def by simp

lemma reflexiveIsBool[intro!,simp]: "isBool(reflexive(A,r))"
unfolding isBool_def by (rule boolifyReflexive)

definition symmetric   -- {* symmetric relation *}
where "symmetric(r) \<equiv> \<forall>x,y: \<langle>x,y\<rangle> \<in> r \<Rightarrow> \<langle>y,x\<rangle> \<in> r"

lemma boolifySymmetric [simp]: "boolify(symmetric(r)) = symmetric(r)"
unfolding symmetric_def by simp

lemma symmetricIsBool[intro!,simp]: "isBool(symmetric(r))"
unfolding isBool_def by (rule boolifySymmetric)

definition antisymmetric   -- {* antisymmetric relation *}
where "antisymmetric(r) \<equiv> \<forall>x,y: \<langle>x,y\<rangle> \<in> r \<and> \<langle>y,x\<rangle> \<in> r \<Rightarrow> x = y"

lemma boolifyAntisymmetric [simp]: "boolify(antisymmetric(r)) = antisymmetric(r)"
unfolding antisymmetric_def by simp

lemma antisymmetricIsBool[intro!,simp]: "isBool(antisymmetric(r))"
unfolding isBool_def by (rule boolifyAntisymmetric)

definition transitive   -- {* transitivity predicate *}
where "transitive(r) \<equiv> \<forall>x,y,z: \<langle>x,y\<rangle> \<in> r \<and> \<langle>y,z\<rangle> \<in> r \<Rightarrow> \<langle>x,z\<rangle> \<in> r"

lemma boolifyTransitive [simp]: "boolify(transitive(r)) = transitive(r)"
unfolding transitive_def by simp

lemma transitiveIsBool[intro!,simp]: "isBool(transitive(r))"
unfolding isBool_def by (rule boolifyTransitive)

definition irreflexive   -- {* irreflexivity predicate *}
where "irreflexive(A,r) \<equiv> \<forall>x \<in> A: \<langle>x,x\<rangle> \<notin> r"

lemma boolifyIrreflexive [simp]: "boolify(irreflexive(A,r)) = irreflexive(A,r)"
unfolding irreflexive_def by simp

lemma irreflexiveIsBool[intro!,simp]: "isBool(irreflexive(A,r))"
unfolding isBool_def by (rule boolifyIrreflexive)

definition equivalence  :: "[c,c] \<Rightarrow> c"   -- {* (partial) equivalence relation *}
where "equivalence(A,r) \<equiv> reflexive(A,r) \<and> symmetric(r) \<and> transitive(r)"

lemma boolifyEquivalence [simp]: "boolify(equivalence(A,r)) = equivalence(A,r)"
unfolding equivalence_def by simp

lemma equivalenceIsBool[intro!,simp]: "isBool(equivalence(A,r))"
unfolding isBool_def by (rule boolifyEquivalence)


subsubsection {* Domain and Range *}

lemma prod_in_dom_x_ran:
  assumes "r \<subseteq> A \<times> B" and "p \<in> r"
  shows "\<langle>p[1],p[2]\<rangle> \<in> rel_domain(r) \<times> rel_range(r)"
unfolding inProd rel_domain_def rel_range_def
using assms by auto

lemma in_rel_domainI [iff]:
  assumes "\<langle>x,y\<rangle> \<in> r"
  shows "x \<in> rel_domain(r)"
unfolding rel_domain_def using assms by auto

lemma in_rel_domainE [elim]:
  assumes x: "x \<in> rel_domain(r)" and r: "r \<subseteq> A \<times> B" and p: "\<And>y. \<langle>x,y\<rangle> \<in> r \<Longrightarrow> P"
  shows "P"
proof -
  from x obtain p where 1: "p \<in> r" and 2: "p[1] = x"
    by (auto simp add: rel_domain_def)
  from 1 r have "p = \<langle>p[1],p[2]\<rangle>" by (intro prodProj, auto)
  with 1 2 show "P" by (intro p[where y="p[2]"], simp)
qed

lemma rel_domain (*[simp]*): "r \<subseteq> A \<times> B \<Longrightarrow> rel_domain(r) \<subseteq> A"
unfolding rel_domain_def using pairProj_in_prod by auto

lemma rel_range (*[simp]*): "r \<subseteq> A \<times> B \<Longrightarrow> rel_range(r) \<subseteq> B"
unfolding rel_range_def using pairProj_in_prod by auto

lemma in_rel_rangeI [iff]:
  assumes "\<langle>x,y\<rangle> \<in> r"
  shows "y \<in> rel_range(r)"
unfolding rel_range_def using assms by auto

lemma in_rel_rangeE [elim]:
  assumes y: "y \<in> rel_range(r)" and r: "r \<subseteq> A \<times> B" and p: "\<And>x. \<langle>x,y\<rangle> \<in> r \<Longrightarrow> P"
  shows "P"
proof -
  from y obtain p where 1: "p \<in> r" and 2: "p[2] = y"
    by (auto simp add: rel_range_def)
  from 1 r have "p = \<langle>p[1],p[2]\<rangle>" by (intro prodProj, auto)
  with 1 2 show "P" by (intro p[where x="p[1]"], simp)
qed

lemma dom_in_A (*[simp]*): "rel_domain ({ p \<in> A \<times> B : P(p) }) \<subseteq> A"
by auto

lemma ran_in_B (*[simp]*): "rel_range ({ p \<in> A \<times> B : P(p) }) \<subseteq> B"
by auto

lemma subrel_dom: "r' \<subseteq> r \<Longrightarrow> x \<in> rel_domain(r') \<Longrightarrow> x \<in> rel_domain(r)"
unfolding rel_domain_def by auto

lemma subrel_ran: "r' \<subseteq> r \<Longrightarrow> x \<in> rel_range(r') \<Longrightarrow> x \<in> rel_range(r)"
unfolding rel_range_def by auto

lemma in_dom_imp_in_A: "r \<subseteq> A \<times> B \<Longrightarrow> x \<in> rel_domain(r) \<Longrightarrow> x \<in> A"
by force

lemma in_ran_imp_in_B: "r \<subseteq> A \<times> B \<Longrightarrow> p \<in> rel_range(r) \<Longrightarrow> p \<in> B"
by force


subsubsection {* Converse relation *}

lemmas converseEqualI = 
  setEqualI [where A = "r^-1", standard, intro!]
  setEqualI [where B = "r^-1", standard, intro!]

lemma converse_iff [iff]: 
  assumes r: "r \<subseteq> A \<times> B"
  shows "(\<langle>a,b\<rangle> \<in> r^-1) = (\<langle>b,a\<rangle> \<in> r)"
using r prodProj by (auto simp: converse_def)

lemma converseI [intro!]: 
  shows "\<langle>a,b\<rangle> \<in> r \<Longrightarrow> \<langle>b,a\<rangle> \<in> r^-1"
unfolding converse_def by auto

lemma converseD [sym]: 
  assumes r: "r \<subseteq> A \<times> B"
  shows "\<langle>a,b\<rangle> \<in> r^-1 \<Longrightarrow> \<langle>b,a\<rangle> \<in> r"
using converse_iff[OF r] by simp

lemma converseSubset: "r \<subseteq> A \<times> B \<Longrightarrow> r^-1 \<subseteq> B \<times> A"
unfolding converse_def using pairProj_in_prod by auto

lemma converseE [elim]:  (** consider [elim!] ?? **)
  assumes yx: "yx \<in> r^-1" and r: "r \<subseteq> A \<times> B"
      and p: "\<And>x y. yx = \<langle>y,x\<rangle> \<Longrightarrow> \<langle>x,y\<rangle> \<in> r \<Longrightarrow> P"
  shows "P"
    -- {* More general than @{text converseD}, as it ``splits'' the member of the relation. *}
proof -
  from prodProj[OF subsetD[OF converseSubset[OF r] yx]] have 2: "yx = \<langle>yx[1], yx[2]\<rangle>" .
  with yx have 3: "\<langle>yx[2], yx[1]\<rangle> \<in> r"
    unfolding converse_def apply auto
    using r prodProj by auto
  from p[of "yx[1]" "yx[2]"] 2 3
  show P by simp
qed

lemma converse_converse [simp]: 
  assumes r: "r \<subseteq> A \<times> B"
  shows "(r^-1)^-1 = r"
using assms prodProj by (auto elim!: converseE)

lemma converse_prod [simp]: "(A \<times> B)^-1 = B \<times> A"
using prodProj by auto

lemma converse_empty [simp]: "converse({}) = {}"
by auto

lemma converse_mono_1:
  assumes r: "r \<subseteq> A \<times> B" and s: "s \<subseteq> A \<times> B" and sub: "r^-1 \<subseteq> s^-1"
  shows "r \<subseteq> s"
proof
  fix p
  assume p: "p \<in> r"
  with r have 1: "p = \<langle>p[1],p[2]\<rangle>" by (intro prodProj, auto)
  with p have "\<langle>p[2],p[1]\<rangle> \<in> r^-1" by auto
  with sub s 1 show "p \<in> s" by auto
qed

lemma converse_mono_2:
  assumes "r \<subseteq> A \<times> B" and "s \<subseteq> A \<times> B" and "r \<subseteq> s"
  shows "r^-1 \<subseteq> s^-1"
using assms prodProj by auto

lemma converse_mono:
  assumes r:"r \<subseteq> A \<times> B" and s:"s \<subseteq> A \<times> B" 
  shows "r^-1 \<subseteq> s^-1 = (r \<subseteq> s)"
using converse_mono_1[OF r s] converse_mono_2[OF r s]
by blast

(* from HOL *)

lemma reflexive_converse [simp]: 
  "r \<subseteq> A \<times> B \<Longrightarrow> reflexive(A, r^-1) = reflexive(A,r)"
  unfolding reflexive_def by auto

lemma symmetric_converse [simp]: 
  "r \<subseteq> A \<times> B \<Longrightarrow> symmetric(r^-1) = symmetric(r)"
  unfolding symmetric_def by auto

lemma antisymmetric_converse [simp]:
  "r \<subseteq> A \<times> B \<Longrightarrow> antisymmetric(r^-1) = antisymmetric(r)"
  unfolding antisymmetric_def by auto

lemma transitive_converse [simp]: 
  "r \<subseteq> A \<times> B \<Longrightarrow> transitive(r^-1) = transitive(r)"
  unfolding transitive_def by auto

lemma symmetric_iff_converse_eq: 
  assumes r:"r \<subseteq> A \<times> B"
  shows "symmetric(r) = (r^-1 = r)"
proof auto
  fix p
  assume "symmetric(r)" and "p \<in> r^-1"
  with r show "p \<in> r" by (auto elim!: converseE simp add: symmetric_def)
next
  fix p
  assume 1: "symmetric(r)" and 2: "p \<in> r"
  from r 2 have 3: "p = \<langle>p[1],p[2]\<rangle>" by (intro prodProj, auto)
  with 1 2 have "\<langle>p[2],p[1]\<rangle> \<in> r" by (force simp add: symmetric_def)
  with 3 show "p \<in> r^-1" by (auto dest: converseI)
next
  assume "r^-1 = r" thus "symmetric(r)"
    by (auto simp add: symmetric_def)
qed


subsubsection {* Identity relation over a set *}

lemmas idEqualI = 
  setEqualI [where A = "Id(S)", standard, intro!]
  setEqualI [where B = "Id(S)", standard, intro!]

lemma IdI [iff]: "x \<in> S \<Longrightarrow> \<langle>x,x\<rangle> \<in> Id(S)"
unfolding Id_def by auto

lemma IdI' [intro]: "x \<in> S \<Longrightarrow> p = \<langle>x,x\<rangle> \<Longrightarrow> p \<in> Id(S)"
unfolding Id_def by auto

lemma IdE [elim!]:
  "p \<in> Id(S) \<Longrightarrow> (\<And>x. x \<in> S \<and> p = \<langle>x,x\<rangle> \<Longrightarrow> P) \<Longrightarrow> P"
unfolding Id_def by auto

lemma Id_iff: "(\<langle>a,b\<rangle> \<in> Id(S)) = (a = b \<and> a \<in> S)"
by auto

lemma Id_subset_Prod [simp]: "Id(S) \<subseteq> S \<times> S"
unfolding Id_def by auto

lemma reflexive_Id: "reflexive(S,Id(S))"
unfolding reflexive_def by auto

lemma antisymmetric_Id [simp]: "antisymmetric(Id(S))"
unfolding antisymmetric_def by auto

lemma symmetric_Id [simp]: "symmetric(Id(S))"
unfolding symmetric_def by auto

lemma transitive_Id [simp]: "transitive(Id(S))"
unfolding transitive_def by auto

lemma Id_empty [simp]: "Id({}) = {}"
unfolding Id_def by simp

lemma Id_eqI: "a = b \<Longrightarrow> a \<in> A \<Longrightarrow> \<langle>a,b\<rangle> \<in> Id(A)"
by simp

lemma converse_Id [simp]: "Id(A)^-1 = Id(A)"
by auto

lemma dom_Id [simp]: "rel_domain(Id(A)) = A"
unfolding rel_domain_def Id_def by auto

lemma ran_Id [simp]: "rel_range(Id(A)) = A"
unfolding rel_range_def Id_def by auto


subsubsection {* Composition of relations *}

lemmas compEqualI = 
  setEqualI [where A = "r \<circ> s", standard, intro!]
  setEqualI [where B = "r \<circ> s", standard, intro!]

lemma compI [intro]: 
  assumes r: "r \<subseteq> B \<times> C" and s: "s \<subseteq> A \<times> B"
  shows "\<lbrakk> \<langle>a,b\<rangle> \<in> s; \<langle>b,c\<rangle> \<in> r \<rbrakk> \<Longrightarrow> \<langle>a,c\<rangle> \<in> r \<circ> s"
using assms unfolding rel_comp_def by auto

lemma compE [elim!]:
  assumes "xz \<in> r \<circ> s" and "r \<subseteq> B \<times> C" and "s \<subseteq> A \<times> B"
  shows "(\<And>x y z. xz = \<langle>x,z\<rangle> \<Longrightarrow> \<langle>x,y\<rangle> \<in> s \<Longrightarrow> \<langle>y,z\<rangle> \<in> r \<Longrightarrow> P) \<Longrightarrow> P"
using assms unfolding rel_comp_def by auto

lemma compEpair: 
  assumes "\<langle>a,c\<rangle> \<in> r \<circ> s" and "r \<subseteq> B \<times> C" and s: "s \<subseteq> A \<times> B"
  shows "\<lbrakk>\<And>b. \<lbrakk> \<langle>a,b\<rangle> \<in> s; \<langle>b,c\<rangle> \<in> r \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
using assms by auto

lemma rel_comp_in_prod [iff]:
  assumes s: "s \<subseteq> A \<times> B" and r: "r \<subseteq> B \<times> C"
  shows "r \<circ> s \<subseteq> A \<times> C"
using assms by force

lemma rel_comp_in_prodE (*[elim]*):
  assumes "p \<in> r \<circ> s" and "s \<subseteq> A \<times> B" and r: "r \<subseteq> B \<times> C"
  shows "p \<in> A \<times> C"
using assms by force

lemma converse_comp: 
  assumes r: "r \<subseteq> B \<times> C" and s: "s \<subseteq> A \<times> B"
  shows "((r \<circ> s)^-1) = (s^-1 \<circ> r^-1)"  (is "?lhs = ?rhs")
proof
  fix x
  assume x: "x \<in> ?lhs"
  from s r have "r \<circ> s \<subseteq> A \<times> C" by (rule rel_comp_in_prod)
  with x show "x \<in> ?rhs"
  proof
    fix u w
    assume 1: "x = \<langle>w,u\<rangle>" and 2: "\<langle>u,w\<rangle> \<in> r \<circ> s"
    from 2 r s obtain v where 3: "\<langle>u,v\<rangle> \<in> s" and 4: "\<langle>v,w\<rangle> \<in> r"
      by auto
    with converseSubset[OF r] converseSubset[OF s] have "\<langle>w,u\<rangle> \<in> ?rhs"
      by auto
    with 1 show "x \<in> ?rhs" by simp
  qed
next
  fix x
  assume "x \<in> ?rhs"
  with r s show "x \<in> ?lhs" by (auto dest: converseSubset)
qed

lemma R_comp_Id [simp]: 
  assumes r: "R \<subseteq> B \<times> C"
  shows "R \<circ> Id(B) = R"
using r proof auto
  fix p
  assume p: "p \<in> R"
  with r have 1: "p = \<langle>p[1], p[2]\<rangle>" (is "p = ?pp") by (intro prodProj, auto)
  from p r have "p[1] \<in> B" by (auto dest: pairProj_in_prod)
  with 1 p r have "?pp \<in> R \<circ> Id(B)" by (intro compI, auto)
  with 1 show "p \<in> R \<circ> Id(B)" by simp
qed

lemma Id_comp_R [simp]: 
  assumes r: "R \<subseteq> A \<times> B"
  shows "Id(B) \<circ> R = R"
using r proof auto
  fix p
  assume p: "p \<in> R"
  with r have 1: "p = \<langle>p[1], p[2]\<rangle>" (is "p = ?pp") by (intro prodProj, auto)
  from p r have "p[2] \<in> B" by (auto dest: pairProj_in_prod)
  with 1 p r have "?pp \<in> Id(B) \<circ> R" by (intro compI, auto)
  with 1 show "p \<in> Id(B) \<circ> R" by simp
qed

lemma rel_comp_empty1 [simp]: "{} \<circ> R = {}"
unfolding rel_comp_def by auto

lemma rel_comp_empty2 [simp]: "R \<circ> {} = {}"
unfolding rel_comp_def by auto

lemma comp_assoc: 
  assumes t: "T \<subseteq> A \<times> B" and s: "S \<subseteq> B \<times> C" and r: "R \<subseteq> C \<times> D"
  shows "(R \<circ> S) \<circ> T = R \<circ> (S \<circ> T)"
proof
  fix p
  assume p: "p \<in> (R \<circ> S) \<circ> T"
  from r s have "R \<circ> S \<subseteq> B \<times> D" by simp
  from p this t show "p \<in> R \<circ> (S \<circ> T)"
  proof
    fix x y z
    assume 1: "p = \<langle>x,z\<rangle>" and 2: "\<langle>x, y\<rangle> \<in> T" and 3: "\<langle>y, z\<rangle> \<in> R \<circ> S"
    from 3 r s show ?thesis
    proof (rule compEpair)
      fix u
      assume "\<langle>y,u\<rangle> \<in> S" and "\<langle>u,z\<rangle> \<in> R"
      with r s t 2 have "\<langle>x,z\<rangle> \<in> R \<circ> (S \<circ> T)"
        by (intro compI, auto elim!: relProj1 relProj2)
      with 1 show ?thesis by simp
    qed
  qed
next
  fix p
  assume p: "p \<in> R \<circ> (S \<circ> T)"
  from s t have "S \<circ> T \<subseteq> A \<times> C" by simp
  from p r this show "p \<in> (R \<circ> S) \<circ> T"
  proof
    fix x y z
    assume 1: "p = \<langle>x,z\<rangle>" and 2: "\<langle>x, y\<rangle> \<in> S \<circ> T" and 3: "\<langle>y, z\<rangle> \<in> R"
    from 2 s t show ?thesis
    proof (rule compEpair)
      fix u
      assume "\<langle>x,u\<rangle> \<in> T" and "\<langle>u,y\<rangle> \<in> S"
      with r s t 3 have "\<langle>x,z\<rangle> \<in> (R \<circ> S) \<circ> T"
        by (intro compI, auto elim!: relProj1 relProj2)
      with 1 show ?thesis by simp
    qed
  qed
qed

lemma rel_comp_mono: 
  assumes hr': "r' \<subseteq> r" and hs': "s' \<subseteq> s"
  shows "(r' \<circ> s') \<subseteq> (r \<circ> s)"
unfolding rel_comp_def using subrel_dom[OF hs'] subrel_ran[OF hr']
proof auto
  fix x y z
  assume xy': "\<langle>x, y\<rangle> \<in> s'" and yz': "\<langle>y, z\<rangle> \<in> r'"
  from hs' xy' have xy: "\<langle>x,y\<rangle> \<in> s" by auto
  from hr' yz' have yz: "\<langle>y,z\<rangle> \<in> r" by auto
  show "\<exists>y : \<langle>x, y\<rangle> \<in> s \<and> \<langle>y, z\<rangle> \<in> r"
    using xy yz by auto
qed

lemma rel_comp_distrib [simp]: "R \<circ> (S \<union> T) = (R \<circ> S) \<union> (R \<circ> T)"
unfolding rel_comp_def proof auto
  (** FIXME: why don't auto or force find the following trivial contradiction? **)
  fix x y z
  assume xy: "\<langle>x,y\<rangle> \<in> T" and yz: "\<langle>y,z\<rangle> \<in> R"
     and 1: "\<forall>yy : \<langle>x, yy\<rangle> \<in> T = FALSE \<or> \<langle>yy, z\<rangle> \<in> R = FALSE"
  from 1 have "\<langle>x, y\<rangle> \<in> T = FALSE \<or> \<langle>y, z\<rangle> \<in> R = FALSE" ..
  with xy yz show "\<exists>y : \<langle>x,y\<rangle> \<in> S \<and> \<langle>y,z\<rangle> \<in> R" by simp
qed

lemma rel_comp_distrib2 [simp]: "(S \<union> T) \<circ> R = (S \<circ> R) \<union> (T \<circ> R)"
unfolding rel_comp_def proof auto
  (** FIXME: why don't auto or force find the following trivial contradiction? **)
  fix x y z
  assume xy: "\<langle>x,y\<rangle> \<in> R" and yz: "\<langle>y,z\<rangle> \<in> T"
     and 1: "\<forall>yy : \<langle>x, yy\<rangle> \<in> R = FALSE \<or> \<langle>yy, z\<rangle> \<in> T = FALSE"
  from 1 have "\<langle>x, y\<rangle> \<in> R = FALSE \<or> \<langle>y, z\<rangle> \<in> T = FALSE" ..
  with xy yz show "\<exists>y : \<langle>x,y\<rangle> \<in> R \<and> \<langle>y,z\<rangle> \<in> S" by simp
qed


subsubsection {* Properties of relations *}

text {* Reflexivity *}

lemma reflI [intro]: "(\<And>x. x \<in> A \<Longrightarrow> \<langle>x,x\<rangle> \<in> r) \<Longrightarrow> reflexive(A,r)"
unfolding reflexive_def by blast

lemma reflexiveD [elim!]: "reflexive(A,r) \<Longrightarrow> a \<in> A \<Longrightarrow> \<langle>a,a\<rangle> \<in> r"
unfolding reflexive_def by blast

lemma reflexive_empty (*[simp]*): "reflexive({}, {})"
by auto


text {* Symmetry *}

lemma symmetricI: "\<lbrakk> \<And>x y. \<langle>x,y\<rangle> \<in> r \<Longrightarrow> \<langle>y,x\<rangle> \<in> r \<rbrakk> \<Longrightarrow> symmetric(r)"
unfolding symmetric_def by blast

lemma symmetricE: "\<lbrakk> symmetric(r); \<langle>x,y\<rangle> \<in> r \<rbrakk> \<Longrightarrow> \<langle>y,x\<rangle> \<in> r"
unfolding symmetric_def by blast

lemma symmetric_Int: "\<lbrakk> symmetric(r); symmetric(s) \<rbrakk> \<Longrightarrow> symmetric(r \<inter> s)"
by (blast intro: symmetricI dest: symmetricE)


text {* Antisymmetry *}

lemma antisymmetricI [intro]: 
  "\<lbrakk> \<And>x y. \<lbrakk> \<langle>x,y\<rangle> \<in> r; \<langle>y,x\<rangle> \<in> r \<rbrakk> \<Longrightarrow> x = y \<rbrakk> \<Longrightarrow> antisymmetric(r)"
unfolding antisymmetric_def by blast

lemma antisymmetricE [elim]: "\<lbrakk> antisymmetric(r); \<langle>x,y\<rangle> \<in> r; \<langle>y,x\<rangle> \<in> r \<rbrakk> \<Longrightarrow> x = y"
unfolding antisymmetric_def by blast

lemma antisymmetricSubset: "r \<subseteq> s \<Longrightarrow> antisymmetric(s) \<Longrightarrow> antisymmetric(r)"
unfolding antisymmetric_def by blast

lemma antisym_empty (*[simp]*): "antisymmetric({})"
by blast


text {* Transitivity *}

lemma transitiveI [intro]:
  "(\<And>x y z. \<langle>x,y\<rangle> \<in> r \<Longrightarrow> \<langle>y,z\<rangle> \<in> r \<Longrightarrow> \<langle>x,z\<rangle> \<in> r) \<Longrightarrow> transitive(r)"
unfolding transitive_def by blast

lemma transD [elim]: "\<lbrakk> transitive(r);  \<langle>x,y\<rangle> \<in> r; \<langle>y,z\<rangle> \<in> r \<rbrakk> \<Longrightarrow> \<langle>x,z\<rangle> \<in> r"
unfolding transitive_def by blast

lemma trans_Int: "transitive(r) \<Longrightarrow> transitive(s) \<Longrightarrow> transitive(r \<inter> s)"
by fast

lemma transitive_iff_comp_subset: "transitive(r) = (r \<circ> r \<subseteq> r)"
unfolding transitive_def rel_comp_def by (auto elim!: subsetD)


text {* Irreflexivity *}

lemma irreflexiveI [intro]: "\<lbrakk> \<And>x. x \<in> A \<Longrightarrow> \<langle>x,x\<rangle> \<notin> r \<rbrakk> \<Longrightarrow> irreflexive(A,r)"
unfolding irreflexive_def by blast

lemma irreflexiveE [dest]: "\<lbrakk> irreflexive(A,r); x \<in> A \<rbrakk> \<Longrightarrow>  \<langle>x,x\<rangle> \<notin> r"
unfolding irreflexive_def by blast


subsubsection {* Equivalence Relations *}

(**************** NOT USED ANYWHERE ************************************
definition
  quotient   :: "[c,c] \<Rightarrow> c"    (infixl "'/'/" 90)  (*set of equiv classes*)  where
      "A//r \<equiv> {r``{x} : x \<in> A}"

definition
  congruent  :: "[c, c \<Rightarrow> c] \<Rightarrow> c"  where
      "congruent(r,b) \<equiv> \<forall>\<langle>x,y\<rangle> \<in> r: b(x) = b(y)"

definition
  congruent2 :: "[c, c, [c,c] \<Rightarrow> c] \<Rightarrow> c"  where
      "congruent2(r1,r2,b) \<equiv> \<forall>\<langle>y1,z1\<rangle> \<in> r1: \<forall>\<langle>y2,z2\<rangle> \<in> r2 : b(y1,y2) = b(z1,z2)"

abbreviation
  RESPECTS ::"[c \<Rightarrow> c, c] \<Rightarrow> c"  (infixr "respects" 80) where
  "f respects r \<equiv> congruent(r,f)"

abbreviation
  RESPECTS2 ::"[c \<Rightarrow> c \<Rightarrow> c, c] \<Rightarrow> c"  (infixr "respects2 " 80) where
  "f respects2 r \<equiv> congruent2(r,r,f)"
  --{* Abbreviation for the common case where the relations are identical *}
***************************************************************************)

text{* @{term r} is an equivalence relation iff @{term "converse(r) \<circ> r = r"} *}

(* from Suppes, Theorem 70 *)

text {* First half: ``only if'' part *}

lemma sym_trans_comp_subset:
  assumes "r \<subseteq> A \<times> A" and "symmetric(r)" and "transitive(r)"
  shows "r^-1 \<circ> r \<subseteq> r"
using assms by (simp add: symmetric_iff_converse_eq transitive_iff_comp_subset)

lemma refl_comp_subset:
  assumes r: "r \<subseteq> A \<times> A" and refl: "reflexive(A,r)"
  shows "r \<subseteq> r^-1 \<circ> r"
proof
  fix p
  assume p: "p \<in> r"
  with r obtain x z where 1: "p = \<langle>x,z\<rangle>" by (blast dest: prodProj)
  with p r have "z \<in> A" by auto
  with refl have "\<langle>z,z\<rangle> \<in> r" by auto
  moreover
  from 1 p have "\<langle>z,x\<rangle> \<in> r^-1" by auto
  moreover
  from r have "r^-1 \<subseteq> A \<times> A" by (rule converseSubset)
  moreover
  note r
  ultimately
  have "\<langle>x,z\<rangle> \<in> r^-1 \<circ> r" by (intro compI, auto)
  with 1 show "p \<in> r^-1 \<circ> r" by simp
qed

lemma equiv_comp_eq:
  assumes r: "r \<subseteq> A \<times> A" and eq: "equivalence(A,r)"
  shows "r^-1 \<circ> r = r"
using eq sym_trans_comp_subset[OF r] refl_comp_subset[OF r]
unfolding equivalence_def
by (intro setEqual, simp+)

text {* Second half: ``if'' part, needs totality of relation $r$ *}

lemma comp_equivI:
  assumes dom: "rel_domain(r) = A" and r: "r \<subseteq> A \<times> A" and comp: "r^-1 \<circ> r = r"
  shows "equivalence(A,r)"
proof -
  from r have r1: "r^-1 \<subseteq> A \<times> A" by (rule converseSubset)
  have refl: "reflexive(A,r)"
  proof
    fix a
    assume a: "a \<in> A"
    with dom r obtain b where b: "\<langle>a,b\<rangle> \<in> r" by auto
    hence "\<langle>b,a\<rangle> \<in> r^-1" ..
    with b r r1 have "\<langle>a,a\<rangle> \<in> r^-1 \<circ> r" by (intro compI, auto)
    with comp show "\<langle>a,a\<rangle> \<in> r" by simp
  qed
  have sym: "symmetric(r)"
  proof -
    from comp have "r^-1 = (r^-1 \<circ> r)^-1" by simp
    also from r r1 have "... = r^-1 \<circ> r" by (simp add: converse_comp)
    finally have "r^-1 = r" by (simp add: comp)
    with r show ?thesis by (simp add: symmetric_iff_converse_eq)
  qed
  have trans: "transitive(r)"
  proof -
    from r sym have "r \<circ> r = r^-1 \<circ> r" by (simp add: symmetric_iff_converse_eq)
    with comp have "r \<circ> r = r" by simp
    thus ?thesis by (simp add: transitive_iff_comp_subset)
  qed
  from refl sym trans show ?thesis
    unfolding equivalence_def by simp
qed

end
