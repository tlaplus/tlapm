(* Zenon.thy --- Support lemmas for Zenon proofs
 * Author: Damien Doligez <damien.doligez@inria.fr>
 * Copyright (C) 2008-2011  INRIA and Microsoft Corporation
 * Version:    Isabelle2011-1
 * Time-stamp: <2011-10-11 17:41:20 merz>
 *)

(* isabelle usedir -b Pure TLA+ *)

theory Zenon
imports Constant
begin

text \<open> The following lemmas make a cleaner meta-object reification \<close>
lemma atomize_meta_bAll [atomize]:
  "(\<And>x. (x \<in> S \<Longrightarrow> P(x)))
              \<equiv> Trueprop (\<forall> x \<in> S : P(x))"
proof
  assume "(\<And>x. (x \<in> S \<Longrightarrow> P(x)))"
  thus "\<forall> x \<in> S : P(x)" ..
next
  assume "\<forall> x \<in> S : P(x)"
  thus "(\<And>x. (x \<in> S \<Longrightarrow> P(x)))" ..
qed

lemma atomize_object_bAll [atomize]:
  "Trueprop (\<forall>x : (x \<in> S) \<Rightarrow> P(x))
   \<equiv> Trueprop (\<forall>x \<in> S : P(x))"
proof
  assume "\<forall>x : x \<in> S \<Rightarrow> P(x)"
  thus "\<forall>x \<in> S : P(x)" by fast
next
  assume "\<forall>x \<in> S : P(x)"
  thus "\<forall>x : x \<in> S \<Rightarrow> P(x)" by fast
qed


lemma zenon_nnpp: "(~P ==> FALSE) ==> P"
by blast

lemma zenon_em: "(P ==> FALSE) ==> (~P ==> FALSE) ==> FALSE"
by blast

lemma zenon_eqrefl: "t = t"
by simp

lemma zenon_nottrue: "~TRUE ==> FALSE"
by blast

lemma zenon_noteq: "~x=x ==> FALSE"
by blast

lemma zenon_eqsym : "a = b ==> b ~= a ==> FALSE"
using not_sym by blast

lemma zenon_FALSE_neq_TRUE: "FALSE ~= TRUE"
by (rule false_neq_true)

lemma zenon_and: "P & Q ==> (P ==> Q ==> FALSE) ==> FALSE"
by blast

lemma zenon_and_0: "P & Q ==> P"
by blast

lemma zenon_and_1: "P & Q ==> Q"
by blast

lemma zenon_or: "P | Q ==> (P ==> FALSE) ==> (Q ==> FALSE) ==> FALSE"
by blast

lemma zenon_imply: "P => Q ==> (~P ==> FALSE) ==> (Q ==> FALSE) ==> FALSE"
by blast

lemma zenon_equiv:
  "P <=> Q ==> (~P ==> ~Q ==> FALSE) ==> (P ==> Q ==> FALSE) ==> FALSE"
by blast

lemma zenon_notnot: "~~P ==> (P ==> FALSE) ==> FALSE"
by blast

lemma zenon_notnot_0: "~~P ==> P"
by blast

lemma zenon_notand: "~(P & Q) ==> (~P ==> FALSE) ==> (~Q ==> FALSE) ==> FALSE"
by blast

lemma zenon_notor: "~(P | Q) ==> (~P ==> ~Q ==> FALSE) ==> FALSE"
by blast

lemma zenon_notor_0: "~(P | Q) ==> ~P"
by blast

lemma zenon_notor_1: "~(P | Q) ==> ~Q"
by blast

lemma zenon_notimply: "~(A=>B) ==> (A ==> ~B ==> FALSE) ==> FALSE"
by blast

lemma zenon_notimply_0: "~(A=>B) ==> A"
by blast

lemma zenon_notimply_1: "~(A=>B) ==> ~B"
by blast

lemma zenon_notequiv:
  "~(P <=> Q) ==> (~P ==> Q ==> FALSE) ==> (P ==> ~Q ==> FALSE) ==> FALSE"
by blast

lemma zenon_ex: "\\E x : P (x) ==> (!!x. P (x) ==> FALSE) ==> FALSE"
by blast

lemma zenon_ex_choose:
  "\\E x : P (x) ==> (P (CHOOSE x : P (x)) ==> FALSE) ==> FALSE"
proof -
  assume goal: "\\E x : P(x)"
  and sub: "P (CHOOSE x : P(x)) ==> FALSE"
  show FALSE
  proof (rule sub)
    from goal show "P (CHOOSE x : P(x))"
    by (rule chooseI_ex)
  qed
qed

lemma zenon_ex_choose_0: "\\E x : P (x) ==> P (CHOOSE x : P (x))"
proof (rule zenon_nnpp)
  assume goal: "\\E x : P(x)"
  assume nh: "~ P (CHOOSE x : P(x))"
  show FALSE
  proof (rule zenon_ex_choose)
    assume h: "P (CHOOSE x : P(x))"
    show FALSE
    by (rule notE [OF nh h])
  next
    show "\\E x : P(x)"
    by fact
  qed
qed

lemma zenon_all: "\\A x : P (x) ==> (P (t) ==> FALSE) ==> FALSE"
by blast

lemma zenon_all_0: "\\A x : P (x) ==> P (t)"
by blast

lemma zenon_notex: "~(\\E x : P (x)) ==> (~P (t) ==> FALSE) ==> FALSE"
by blast

lemma zenon_notex_0: "~(\\E x : P (x)) ==> ~P (t)"
by blast

lemma zenon_notall: "~(\\A x : P (x)) ==> (!!x. ~P (x) ==> FALSE) ==> FALSE"
by blast

lemma zenon_notallex: "~(\\A x : P (x)) ==> (\\E x : ~P(x) ==> FALSE) ==> FALSE"
by blast

lemma zenon_notallex_0: "~(\\A x : P (x)) ==> \\E x : ~P(x)"
by blast

lemma zenon_notall_choose:
  "~(\\A x : P (x)) ==> (~P (CHOOSE x : ~P (x)) ==> FALSE) ==> FALSE"
proof -
  assume goal: "~(\\A x : P (x))"
  and sub: "~P (CHOOSE x : ~P (x)) ==> FALSE"
  show FALSE
  proof (rule notE [OF goal])
    have pch: "P(CHOOSE x : ~P(x))" by (rule contradiction [OF sub])
    have univ: "!!x . P(x)"
    proof -
      fix x
      show "P(x)"
      proof (rule contradiction)
        assume npx: "~P(x)"
        show FALSE
        proof (rule notE [OF _ pch])
          from npx show "~P (CHOOSE x : ~P(x))"
          by (rule chooseI [of "\<lambda> v . ~P(v)" x])
        qed
      qed
    qed
    show "\\A x : P(x)" by (rule allI [OF univ])
  qed
qed

lemma zenon_notall_choose_0:
  "~(\\A x : P (x)) ==> ~P (CHOOSE x : ~P (x))"
proof (rule zenon_nnpp)
  assume goal: "~(\\A x : P(x))"
  assume nnh: "~~P(CHOOSE x : ~P(x))"
  show FALSE
  proof (rule zenon_notall_choose)
    show "~(\\A x : P(x))" by fact
  next
    assume nh: "~P(CHOOSE x : ~P(x))"
    show FALSE
    by (rule notE [OF nnh nh])
  qed
qed

lemma zenon_choose_diff_choose:
  "(CHOOSE x : P(x)) ~= (CHOOSE x : Q (x)) ==>
   ((\\E x : ~(P(x) <=> Q(x))) ==> FALSE) ==> FALSE"
proof -
  assume h1: "(CHOOSE x : P(x)) ~= (CHOOSE x : Q (x))"
  assume h2: "((\\E x : ~(P(x) <=> Q(x))) ==> FALSE)"
  show FALSE
  proof (rule notE [OF h1])
    show "(CHOOSE x : P(x)) = (CHOOSE x : Q (x))"
    proof (rule choose_det)
      fix x
      show "P(x) <=> Q(x)"
      using h2 by blast
    qed
  qed
qed

lemma zenon_choose_diff_choose_0:
  "(CHOOSE x : P(x)) ~= (CHOOSE x : Q (x)) ==> \\E x : ~(P(x) <=> Q(x))"
proof -
  assume h1: "(CHOOSE x : P(x)) ~= (CHOOSE x : Q (x))"
  show "\\E x : ~(P(x) <=> Q(x))"
  proof (rule zenon_nnpp)
    assume h2: "~(\\E x : ~(P(x) <=> Q(x)))"
    show FALSE
    proof (rule zenon_choose_diff_choose [OF h1])
      assume h3: "\\E x : ~(P(x) <=> Q(x))"
      with h2 show FALSE ..
    qed
  qed
qed

lemma zenon_notequalchoose:
  "((\\E x : P(x)) ==> FALSE) ==>
   ((~(\\E x : P(x))) ==> ~P(e) ==> FALSE) ==>
   FALSE"
by blast

lemma zenon_p_eq_l:
  "e ==> e1 = e2 ==>
   (e ~= e1 ==> FALSE) ==>
   (e2 ==> FALSE) ==>
   FALSE"
by blast

lemma zenon_p_eq_r:
  "e ==> e1 = e2 ==>
   (e ~= e2 ==> FALSE) ==>
   (e1 ==> FALSE) ==>
   FALSE"
by blast

lemma zenon_np_eq_l:
  "~e ==> e1 = e2 ==>
   (e ~= e1 ==> FALSE) ==>
   (~e2 ==> FALSE) ==>
   FALSE"
by blast

lemma zenon_np_eq_r:
  "~e ==> e1 = e2 ==>
   (e ~= e2 ==> FALSE) ==>
   (~e1 ==> FALSE) ==>
   FALSE"
by blast

(* ------------- Proof rules for set theory ------------- *)

lemma zenon_in_emptyset : "x \\in {} ==> FALSE"
by blast

lemma zenon_in_upair :
  "x \\in upair (y, z) ==> (x = y ==> FALSE) ==> (x = z ==> FALSE) ==> FALSE"
using upairE by blast

lemma zenon_notin_upair :
  "x \\notin upair (y, z) ==> (x ~= y ==> x ~= z ==> FALSE) ==> FALSE"
using upairI1 upairI2 by blast

lemma zenon_notin_upair_0 :
  "x \\notin upair (y, z) ==> x ~= y"
using upairI1 by blast

lemma zenon_notin_upair_1 :
  "x \\notin upair (y, z) ==> x ~= z"
using upairI2 by blast

lemma zenon_in_addElt :
  "x \\in addElt (a, A) ==> (x = a ==> FALSE) ==> (x \\in A ==> FALSE) ==> FALSE"
by blast

lemma zenon_notin_addElt :
  "x \\notin addElt (a, A) ==> (x ~= a ==> x \\notin A ==> FALSE) ==> FALSE"
by blast

lemma zenon_notin_addElt_0 :
  "x \\notin addElt (a, A) ==> x ~= a"
by blast

lemma zenon_notin_addElt_1 :
  "x \\notin addElt (a, A) ==> x \\notin A"
by blast

(* infinity -- needed ? *)

lemma zenon_in_SUBSET :
  "A \\in SUBSET (S) ==> (A \\subseteq S ==> FALSE) ==> FALSE"
by blast

lemma zenon_in_SUBSET_0 :
  "A \\in SUBSET (S) ==> A \\subseteq S"
by blast

lemma zenon_notin_SUBSET :
  "A \\notin SUBSET (S) ==> (~A \\subseteq S ==> FALSE) ==> FALSE"
by blast

lemma zenon_notin_SUBSET_0 :
  "A \\notin SUBSET (S) ==> ~A \\subseteq S"
by blast

lemma zenon_in_UNION :
  "x \\in UNION s ==> (\\E b : b \\in s & x \\in b ==> FALSE) ==> FALSE"
by blast

lemma zenon_in_UNION_0 :
  "x \\in UNION s ==> \\E b : b \\in s & x \\in b"
by blast

lemma zenon_notin_UNION :
  "x \\notin UNION s ==> (~(\\E b : b \\in s & x \\in b) ==> FALSE) ==> FALSE"
by blast

lemma zenon_notin_UNION_0 :
  "x \\notin UNION s ==> ~(\\E b : b \\in s & x \\in b)"
by blast

(* INTER -- needed ? *)

abbreviation
    cup :: "[c, c] \<Rightarrow> c" (infixl "\\cup" 65)
    where "a \\cup b \<equiv> a \<union> b"

abbreviation
    cap :: "[c, c] \<Rightarrow> c" (infixl "\\cap" 70)
    where "a \\cap b \<equiv> a \<inter> b"

lemma zenon_in_cup :
  "x \\in A \\cup B ==> (x \\in A ==> FALSE) ==> (x \\in B ==> FALSE) ==> FALSE"
by blast

lemma zenon_notin_cup :
  "x \\notin A \\cup B ==> (x \\notin A ==> x \\notin B ==> FALSE) ==> FALSE"
by blast

lemma zenon_notin_cup_0 :
  "x \\notin A \\cup B ==> x \\notin A"
by blast

lemma zenon_notin_cup_1 :
  "x \\notin A \\cup B ==> x \\notin B"
by blast

lemma zenon_in_cap :
  "x \\in A \\cap B ==> (x \\in A ==> x \\in B ==> FALSE) ==> FALSE"
by blast

lemma zenon_in_cap_0 :
  "x \\in A \\cap B ==> x \\in A"
by blast

lemma zenon_in_cap_1 :
  "x \\in A \\cap B ==> x \\in B"
by blast

lemma zenon_notin_cap :
  "x \\notin A \\cap B ==> (x \\notin A ==> FALSE) ==> (x \\notin B ==> FALSE)
   ==> FALSE"
by blast

lemma zenon_in_setminus :
  "x \\in A \\ B ==> (x \\in A ==> x \\notin B ==> FALSE) ==> FALSE"
by blast

lemma zenon_in_setminus_0 :
  "x \\in A \\ B ==> x \\in A"
by blast

lemma zenon_in_setminus_1 :
  "x \\in A \\ B ==> x \\notin B"
by blast

lemma zenon_notin_setminus :
  "x \\notin A \\ B ==> (x \\notin A ==> FALSE) ==> (x \\in B ==> FALSE)
   ==> FALSE"
by blast

lemma zenon_in_subsetof :
  "x \\in subsetOf (S, P) ==> (x \\in S ==> P(x) ==> FALSE) ==> FALSE"
by blast

lemma zenon_in_subsetof_0 :
  "x \\in subsetOf (S, P) ==> x \\in S"
by blast

lemma zenon_in_subsetof_1 :
  "x \\in subsetOf (S, P) ==> P(x)"
by blast

lemma zenon_notin_subsetof :
  "~(t \\in subsetOf (S, P)) ==> (~t \\in S ==> FALSE) ==> (~P(t) ==> FALSE)
   ==> FALSE"
by blast

lemma zenon_in_setofall :
  "x \\in setOfAll (S, e) ==> (\\E y : y \\in S & x = e(y) ==> FALSE) ==> FALSE"
by blast

lemma zenon_in_setofall_0 :
  "x \\in setOfAll (S, e) ==> \\E y : y \\in S & x = e(y)"
by blast

lemma zenon_notin_setofall :
  "~(x \\in setOfAll (S, e)) ==> (~ (\\E y : y \\in S & x = e(y)) ==> FALSE)
   ==> FALSE"
by blast

lemma zenon_notin_setofall_0 :
  "~(x \\in setOfAll (S, e)) ==> ~ (\\E y : y \\in S & x = e(y))"
by blast

(* for heuristic instantiation of bounded quantifiers *)

lemma zenon_all_in_0 :
  "\<forall> x \<in> S : P (x) ==> a \\in S ==> P (a)"
by blast

lemma zenon_notex_in_0 :
  "~(\<exists> x \<in> S : P (x)) ==> a \\in S ==> ~P (a)"
by blast

(* shortcuts for \subseteq *)

lemma zenon_cup_subseteq :
  "A \\cup B \\subseteq C ==>
   (A \\subseteq C ==> B \\subseteq C ==> FALSE) ==>
   FALSE"
by blast

lemma zenon_cup_subseteq_0 :
  "A \\cup B \\subseteq C ==> A \\subseteq C"
by blast

lemma zenon_cup_subseteq_1 :
  "A \\cup B \\subseteq C ==> B \\subseteq C"
by blast

lemma zenon_not_cup_subseteq :
  "~ A \\cup B \\subseteq C ==>
   (~A \\subseteq C ==> FALSE) ==>
   (~B \\subseteq C ==> FALSE) ==>
   FALSE"
by blast

lemma zenon_subseteq_cap :
  "A \\subseteq B \\cap C ==>
   (A \\subseteq B ==> A \\subseteq C ==> FALSE) ==>
   FALSE"
by blast

lemma zenon_subseteq_cap_0 :
  "A \\subseteq B \\cap C ==> A \\subseteq B"
by blast

lemma zenon_subseteq_cap_1 :
  "A \\subseteq B \\cap C ==> A \\subseteq C"
by blast

lemma zenon_not_subseteq_cap :
  "~ A \\subseteq B \\cap C ==>
   (~A \\subseteq B ==> FALSE) ==>
   (~A \\subseteq C ==> FALSE) ==>
   FALSE"
by blast

lemma zenon_nouniverse : "~ (\\E x : x \\notin S) ==> FALSE"
proof -
  assume h0: "~ (\\E x : x \\notin S)"
  let ?w = "{x \\in S : x \\notin x}"
  have h4: "?w \\in ?w \<or> ?w \\notin ?w" by (rule excluded_middle)
  have h6: "?w \\in S" using h0 by auto
  show FALSE
  proof (rule disjE [OF h4])
    assume h5: "?w \\in ?w"
    have h7: "?w \\notin ?w" using h5 h6 by blast
    show FALSE using h5 h7 by blast
  next
    assume h5: "?w \\notin ?w"
    have h7: "?w \\in ?w" using h5 h6 by blast
    show FALSE using h5 h7 by blast
  qed
qed

(* ------------- Proof rules for functions ------------- *)

lemma zenon_in_funcset :
  "f \\in FuncSet (A, B) ==>
    (isAFcn(f) ==> DOMAIN f = A ==> \\A x : x \\in A => f[x] \\in B ==> FALSE)
   ==> FALSE"
using FuncSet by blast

lemma zenon_in_funcset_0 :
  "f \\in FuncSet (A, B) ==> isAFcn(f)"
using FuncSet by blast

lemma zenon_in_funcset_1 :
  "f \\in FuncSet (A, B) ==> DOMAIN f = A"
using FuncSet by blast

lemma zenon_in_funcset_2 :
  "f \\in FuncSet (A, B) ==> (\\A x : x \\in A => f[x] \\in B)"
using FuncSet by blast

lemma zenon_notin_funcset :
  "f \\notin FuncSet (A, B) ==>
    (~isAFcn(f) ==> FALSE) ==>
    (DOMAIN f ~= A ==> FALSE) ==>
    (~(\\A x : x \\in A => f[x] \\in B) ==> FALSE)
   ==> FALSE"
using FuncSet by blast

lemma zenon_except_notin_funcset :
  "except (f, v, e) \\notin FuncSet (A, B) ==>
    (f \\notin FuncSet (A, B) ==> FALSE) ==>
    (e \\notin B ==> FALSE)
   ==> FALSE"
proof -
  assume h1: "except (f, v, e) \\notin FuncSet (A, B)"
  assume h2: "f \\notin FuncSet (A, B) ==> FALSE"
  assume h3: "e \\notin B ==> FALSE"
  have h4: "f \\in FuncSet (A, B)" using h2 by blast
  have h5: "e \\in B" using h3 by blast
  show FALSE
  proof (rule notE [OF h1])
    have h6: "isAFcn (except (f, v, e))" by auto
    have h7: "DOMAIN (except (f, v, e)) = A" using h4 by auto
    have h8: "\<forall> x \<in> A : except (f, v, e)[x] \\in B"
    proof
      fix x
      assume h9: "x \\in A"
      have h10: "x = v | x ~= v" by (rule excluded_middle)
      show "except (f, v, e)[x] \\in B"
      using h4 h9 h5 except_def by auto
    qed
    show "except (f, v, e) \\in FuncSet (A, B)"
    using h6 h7 h8 FuncSet by blast
  qed
qed

lemma zenon_setequal :
  "A = B ==> (\\A x : x \\in A <=> x \\in B ==> FALSE) ==> FALSE"
by blast

lemma zenon_setequal_0 :
  "A = B ==> \\A x : x \\in A <=> x \\in B"
by blast

lemma zenon_setequalempty :
  "A = {} ==> (\\A x : ~x \\in A ==> FALSE) ==> FALSE"
by blast

lemma zenon_setequalempty_0 :
  "A = {} ==> \\A x : ~x \\in A"
by blast

lemma zenon_notsetequal :
  "A ~= B ==> (~(\\A x : x \\in A <=> x \\in B) ==> FALSE) ==> FALSE"
using extension by blast

lemma zenon_notsetequal_0 :
  "A ~= B ==> ~(\\A x : x \\in A <=> x \\in B)"
using extension by blast

lemma zenon_funequal :
  "f = g ==> (((isAFcn(f) <=> isAFcn(g))
               & DOMAIN f = DOMAIN g)
              & (\\A x : f[x] = g[x])
              ==> FALSE)
   ==> FALSE"
by blast

lemma zenon_funequal_0 :
  "f = g ==> ((isAFcn(f) <=> isAFcn(g))
              & DOMAIN f = DOMAIN g)
             & (\\A x : f[x] = g[x])"
by blast

lemma zenon_notfunequal :
  "f ~= g ==> (~(((isAFcn(f)
                   & isAFcn(g))
                  & DOMAIN f = DOMAIN g)
                 & (\\A x : x \\in DOMAIN g => f[x] = g[x]))
               ==> FALSE)
   ==> FALSE"
proof -
  have h1: "f ~= g ==>
            isAFcn(f) ==>
            isAFcn(g) ==>
            DOMAIN f = DOMAIN g ==>
            (\\A x : x \\in DOMAIN g => f[x] = g[x]) ==>
            FALSE"
  proof -
    assume main: "~ (f = g)"
    assume h1: "isAFcn (f)"
    assume h2: "isAFcn (g)"
    assume h3: "DOMAIN f = DOMAIN g"
    assume h4: "\\A x : x \\in DOMAIN g => f[x] = g[x]"
    have h5: "f = g ==> FALSE" using main by blast
    have h6: "\<forall> x \<in> DOMAIN g : f[x] = g[x]" using h4 by blast
    show FALSE
    proof (rule h5)
      have h7: "DOMAIN f = DOMAIN g & (\<forall>x \<in> DOMAIN g : f[x] = g[x])"
               (is "?cond")
      using h3 h6 by blast
      have h8: "?cond = (f = g)"
      proof (rule sym)
        show "(f = g) = ?cond"
        by (rule fcnEqualIff [OF h1 h2])
      qed
      show "f = g" by (rule subst [OF h8], fact h7)
    qed
  qed
  thus "f ~= g ==> (~(((isAFcn(f)
                        & isAFcn(g))
                       & DOMAIN f = DOMAIN g)
                      & (\\A x : x \\in DOMAIN g => f[x] = g[x]))
               ==> FALSE)
   ==> FALSE"
  by blast
qed

lemma zenon_notfunequal_0 :
  "f ~= g ==> ~(((isAFcn(f)
                  & isAFcn(g))
                 & DOMAIN f = DOMAIN g)
                & (\\A x : x \\in DOMAIN g => f[x] = g[x]))"
using zenon_notfunequal by blast

lemma zenon_fapplyfcn :
  "P(Fcn(S,e)[x]) ==> (x \\notin S ==> FALSE) ==> (P(e(x)) ==> FALSE) ==> FALSE"
proof -
  assume main: "P(Fcn(S,e)[x])"
  assume h1: "x \\notin S ==> FALSE"
  have h1x: "x \\in S" using h1 by blast
  assume h2: "P(e(x)) ==> FALSE"
  show FALSE
  proof (rule h2)
    have h3: "Fcn(S,e)[x] = e(x)"
    using h1x by (rule fapply)
    show "P(e(x))"
    using main by (rule subst [OF h3])
  qed
qed

lemma zenon_fapplyexcept :
  "P(except(f,v,e)[w]) ==>
   (w \\in DOMAIN f ==> v = w ==> P(e) ==> FALSE) ==>
   (w \\in DOMAIN f ==> v ~= w ==> P(f[w]) ==> FALSE) ==>
   (~ w \\in DOMAIN f ==> FALSE) ==>
   FALSE"
proof -
  assume main: "P(except(f,v,e)[w])"
  assume h1: "w \\in DOMAIN f ==> v = w ==> P(e) ==> FALSE"
  assume h2: "w \\in DOMAIN f ==> v ~= w ==> P(f[w]) ==> FALSE"
  assume h3: "~ w \\in DOMAIN f ==> FALSE"
  show FALSE
  proof (rule disjE [of "w \\in DOMAIN f" "~ w \\in DOMAIN f"])
    show "w \\in DOMAIN f | ~ w \\in DOMAIN f" by (rule excluded_middle)
  next
    assume h5: "w \\in DOMAIN f"
    show FALSE
    proof (cases "w = v")
      assume h6: "w = v"
      show FALSE
      proof (rule h1)
        have h7: "P(IF w = v THEN e ELSE f[w])"
        proof (rule subst [of "[f EXCEPT ![v] = e][w]" _ P])
          show "[f EXCEPT ![v] = e][w] = (IF w = v THEN e ELSE f[w])"
          by (rule applyExcept [OF h5])
        next
          show "P([f EXCEPT ![v] = e][w])"
          by (rule main)
        qed
        have h8: "P(IF TRUE THEN e ELSE f[w])"
        proof (rule subst [of "w = v" TRUE])
          show "w = v = TRUE" by (rule eqTrueI [OF h6])
        next
          show "P(IF w = v THEN e ELSE f[w])" by (rule h7)
        qed
        have h9: "P(e)"
        proof (rule subst [of "IF TRUE THEN e ELSE f[w]" _ P])
          show "(IF TRUE THEN e ELSE f[w]) = e" by blast
        next
          show "P(IF TRUE THEN e ELSE f[w])" by (rule h8)
        qed
        show "P(e)" by (rule h9)
      next
        show "w \\in DOMAIN f" by (rule h5)
      next
        show "v = w" by (rule sym[OF h6])
      qed
    next
      assume h10: "w ~= v"
      show FALSE
      proof (rule h2)
        have h12: "P(f[w])"
        proof (rule subst [of "IF FALSE THEN e ELSE f[w]" _ P])
          show "(IF FALSE THEN e ELSE f[w]) = f[w]" by blast
        next
          show "P(IF FALSE THEN e ELSE f[w])"
          proof (rule subst [of "IF w=v THEN e ELSE f[w]" _ P])
            show "(IF w = v THEN e ELSE f[w]) = (IF FALSE THEN e ELSE f[w])"
            using h10 by blast
          next
            show "P(IF w = v THEN e ELSE f[w])"
            proof (rule subst [of "[f EXCEPT ![v] = e][w]" _ P])
              show "[f EXCEPT ![v] = e][w] = (IF w = v THEN e ELSE f[w])"
              by (rule applyExcept, fact)
            next
              show "P([f EXCEPT ![v] = e][w])" by (rule main)
            qed
          qed
        qed
        show "P(f[w])" by (rule h12)
      next
        show "w \\in DOMAIN f" by (rule h5)
      next
        show "v ~= w" by (rule not_sym[OF h10])
      qed
    qed
  next
    show "~ w \\in DOMAIN f ==> FALSE" by (rule h3)
  qed
qed

lemma zenon_boolcase :
  "X = TRUE | X = FALSE ==>
   P(X) ==>
   (X = TRUE ==> P(TRUE) ==> FALSE) ==>
   (X = FALSE ==> P(FALSE) ==> FALSE) ==>
   FALSE"
proof -
  assume isbool: "X = TRUE | X = FALSE"
  assume main: "P(X)"
  assume h1: "X = TRUE ==> P(TRUE) ==> FALSE"
  assume h2: "X = FALSE ==> P(FALSE) ==> FALSE"
  show FALSE
  proof -
    have h3: "X = TRUE ==> FALSE"
    proof -
      assume h4: "X = TRUE"
      show FALSE
      proof (rule h1 [OF h4])
        show "P(TRUE)" by (rule subst [of X TRUE P, OF h4 main])
      qed
    qed
    have h5: "X = FALSE ==> FALSE"
    proof -
      assume h6: "X = FALSE"
      show FALSE
      proof (rule h2 [OF h6])
        show "P(FALSE)" by (rule subst [of X FALSE P, OF h6 main])
      qed
    qed
    show FALSE using isbool h3 h5 by blast
  qed
qed

lemma zenon_boolcase_not :
  "P(~A) ==>
   ((~A) = TRUE ==> P(TRUE) ==> FALSE) ==>
   ((~A) = FALSE ==> P(FALSE) ==> FALSE) ==>
   FALSE"
proof -
  have h0: "(~A) = TRUE | (~A) = FALSE"
  by blast
  show
    "P(~A) ==>
     ((~A) = TRUE ==> P(TRUE) ==> FALSE) ==>
     ((~A) = FALSE ==> P(FALSE) ==> FALSE) ==>
     FALSE"
  by (rule zenon_boolcase [OF h0])
qed

lemma zenon_boolcase_and :
  "P(A & B) ==>
   ((A & B) = TRUE ==> P(TRUE) ==> FALSE) ==>
   ((A & B) = FALSE ==> P(FALSE) ==> FALSE) ==>
   FALSE"
proof -
  have h0: "(A & B) = TRUE | (A & B) = FALSE"
  by blast
  show
    "P(A & B) ==>
     ((A & B) = TRUE ==> P(TRUE) ==> FALSE) ==>
     ((A & B) = FALSE ==> P(FALSE) ==> FALSE) ==>
     FALSE"
  by (rule zenon_boolcase [OF h0])
qed

lemma zenon_boolcase_or :
  "P(A | B) ==>
   ((A | B) = TRUE ==> P(TRUE) ==> FALSE) ==>
   ((A | B) = FALSE ==> P(FALSE) ==> FALSE) ==>
   FALSE"
proof -
  have h0: "(A | B) = TRUE | (A | B) = FALSE"
  by blast
  show
    "P(A | B) ==>
     ((A | B) = TRUE ==> P(TRUE) ==> FALSE) ==>
     ((A | B) = FALSE ==> P(FALSE) ==> FALSE) ==>
     FALSE"
  by (rule zenon_boolcase [OF h0])
qed

lemma zenon_boolcase_imply :
  "P(A => B) ==>
   ((A => B) = TRUE ==> P(TRUE) ==> FALSE) ==>
   ((A => B) = FALSE ==> P(FALSE) ==> FALSE) ==>
   FALSE"
proof -
  have h0: "(A => B) = TRUE | (A => B) = FALSE"
  by blast
  show
    "P(A => B) ==>
     ((A => B) = TRUE ==> P(TRUE) ==> FALSE) ==>
     ((A => B) = FALSE ==> P(FALSE) ==> FALSE) ==>
     FALSE"
  by (rule zenon_boolcase [OF h0])
qed

lemma zenon_boolcase_equiv :
  "P(A <=> B) ==>
   ((A <=> B) = TRUE ==> P(TRUE) ==> FALSE) ==>
   ((A <=> B) = FALSE ==> P(FALSE) ==> FALSE) ==>
   FALSE"
proof -
  have h0: "(A <=> B) = TRUE | (A <=> B) = FALSE"
  by blast
  show
    "P(A <=> B) ==>
     ((A <=> B) = TRUE ==> P(TRUE) ==> FALSE) ==>
     ((A <=> B) = FALSE ==> P(FALSE) ==> FALSE) ==>
     FALSE"
  by (rule zenon_boolcase [OF h0])
qed

lemma zenon_boolcase_all :
  "P(All (Q)) ==>
   (All (Q) = TRUE ==> P(TRUE) ==> FALSE) ==>
   (All (Q) = FALSE ==> P(FALSE) ==> FALSE) ==>
   FALSE"
proof -
  have h0: "All (Q) = TRUE | All (Q) = FALSE"
  by blast
  show
    "P(All (Q)) ==>
     ((All (Q)) = TRUE ==> P(TRUE) ==> FALSE) ==>
     ((All (Q)) = FALSE ==> P(FALSE) ==> FALSE) ==>
     FALSE"
  by (rule zenon_boolcase [OF h0])
qed

lemma zenon_boolcase_ex :
  "P(Ex (Q)) ==>
   (Ex (Q) = TRUE ==> P(TRUE) ==> FALSE) ==>
   (Ex (Q) = FALSE ==> P(FALSE) ==> FALSE) ==>
   FALSE"
proof -
  have h0: "Ex (Q) = TRUE | Ex (Q) = FALSE"
  by blast
  show
    "P(Ex (Q)) ==>
     ((Ex (Q)) = TRUE ==> P(TRUE) ==> FALSE) ==>
     ((Ex (Q)) = FALSE ==> P(FALSE) ==> FALSE) ==>
     FALSE"
  by (rule zenon_boolcase [OF h0])
qed

lemma zenon_boolcase_equal :
  "P(A = B) ==>
   ((A = B) = TRUE ==> P(TRUE) ==> FALSE) ==>
   ((A = B) = FALSE ==> P(FALSE) ==> FALSE) ==>
   FALSE"
proof -
  have h0: "(A = B) = TRUE | (A = B) = FALSE"
  by blast
  show
    "P(A = B) ==>
     ((A = B) = TRUE ==> P(TRUE) ==> FALSE) ==>
     ((A = B) = FALSE ==> P(FALSE) ==> FALSE) ==>
     FALSE"
  by (rule zenon_boolcase [OF h0])
qed

lemma zenon_boolcase_in :
  "P(A \\in B) ==>
   ((A \\in B) = TRUE ==> P(TRUE) ==> FALSE) ==>
   ((A \\in B) = FALSE ==> P(FALSE) ==> FALSE) ==>
   FALSE"
proof -
  have h0: "(A \\in B) = TRUE | (A \\in B) = FALSE"
  by blast
  show
    "P(A \\in B) ==>
     ((A \\in B) = TRUE ==> P(TRUE) ==> FALSE) ==>
     ((A \\in B) = FALSE ==> P(FALSE) ==> FALSE) ==>
     FALSE"
  by (rule zenon_boolcase [OF h0])
qed

lemma zenon_iftrue : "P (IF TRUE THEN a ELSE b) ==> (P (a) ==> FALSE) ==> FALSE"
by auto

lemma zenon_iftrue_0 : "P (IF TRUE THEN a ELSE b) ==> P (a)"
using zenon_iftrue by auto

lemma zenon_iffalse :
  "P (IF FALSE THEN a ELSE b) ==> (P (b) ==> FALSE) ==> FALSE"
by auto

lemma zenon_iffalse_0 : "P (IF FALSE THEN a ELSE b) ==> P (b)"
using zenon_iffalse by auto

lemma zenon_ifthenelse :
  "P (IF c THEN a ELSE b) ==>
   (c ==> P (a) ==> FALSE) ==>
   (~c ==> P (b) ==> FALSE) ==>
     FALSE"
proof -
  assume main: "P (IF c THEN a ELSE b)"
  assume h1: "c ==> P(a) ==> FALSE"
  have h1x: "c ==> ~P(a)" using h1 by auto
  assume h2: "~c ==> P(b) ==> FALSE"
  have h2x: "~c ==> ~P(b)" using h2 by auto
  have h3: "~P (IF c THEN a ELSE b)"
  by (rule condI [of c "\<lambda> x . ~P (x)", OF h1x h2x])
  show FALSE
  by (rule notE [OF h3 main])
qed

lemma zenon_trueistrue : "P (A) ==> A ==> (P (TRUE) ==> FALSE) ==> FALSE"
by auto

lemma zenon_trueistrue_0 : "P (A) ==> A ==> P (TRUE)"
by auto

lemma zenon_eq_x_true : "x = TRUE ==> (x ==> FALSE) ==> FALSE"
by blast

lemma zenon_eq_x_true_0 : "x = TRUE ==> x"
by blast

lemma zenon_eq_true_x : "TRUE = x ==> (x ==> FALSE) ==> FALSE"
by blast

lemma zenon_eq_true_x_0 : "TRUE = x ==> x"
by blast

lemma zenon_noteq_x_true : "x ~= TRUE ==> (~x ==> FALSE) ==> FALSE"
using eqTrueI by auto

lemma zenon_noteq_x_true_0 : "x ~= TRUE ==> ~x"
using zenon_noteq_x_true by blast

lemma zenon_noteq_true_x : "TRUE ~= x ==> (~x ==> FALSE) ==> FALSE"
using eqTrueI by auto

lemma zenon_noteq_true_x_0 : "TRUE ~= x ==> ~x"
using zenon_noteq_x_true by blast

lemma zenon_eq_x_false : "x = FALSE ==> (~x ==> FALSE) ==> FALSE"
by blast

lemma zenon_eq_x_false_0 : "x = FALSE ==> ~x"
by blast

lemma zenon_eq_false_x : "FALSE = x ==> (~x ==> FALSE) ==> FALSE"
by blast

lemma zenon_eq_false_x_0 : "FALSE = x ==> ~x"
by blast

lemma zenon_notisafcn_fcn : "~isAFcn (Fcn (s,l)) ==> FALSE"
by blast

lemma zenon_notisafcn_except : "~isAFcn (except (f,v,e)) ==> FALSE"
by blast

lemma zenon_notisafcn_onearg : "~isAFcn (oneArg (e1,e2)) ==> FALSE"
by blast

lemma zenon_notisafcn_extend : "~isAFcn (extend (f,g)) ==> FALSE"
by blast

lemma zenon_domain_except :
  "P (DOMAIN (except (f, v, e))) ==>
   (P (DOMAIN f) ==> FALSE) ==>
   FALSE"
proof -
  assume main: "P (DOMAIN (except (f, v, e)))"
  assume h1: "P (DOMAIN f) ==> FALSE"
  show FALSE
  proof (rule h1)
    show "P (DOMAIN f)"
    using main domainExcept by auto
  qed
qed

lemma zenon_domain_except_0 : "P (DOMAIN (except (f, v, e))) ==> P (DOMAIN f)"
proof -
  assume main: "P (DOMAIN (except (f, v, e)))"
  show "P (DOMAIN f)"
  proof (rule zenon_nnpp)
    assume h1: "~ (P (DOMAIN f))"
    show FALSE
    proof (rule zenon_domain_except)
      show "P (DOMAIN (except (f, v, e)))" by (rule main)
    next
      show "P (DOMAIN f) ==> FALSE" using h1 by blast
    qed
  qed
qed

lemma zenon_domain_fcn_0 : "P (DOMAIN (Fcn (S, l))) ==> P (S)"
using DOMAIN by auto

(* ------------- Proof rules for tuples ------------- *)

lemma zenon_in_product_i :
  assumes a: "p \\in Product (s)"
  and b: "isASeq(s)"
  and c: "i \\in 1 .. Len (s)"
  shows "p[i] \\in s[i]"
proof (rule inProductE [OF a b])
  assume h1: "isASeq(p)"
  assume h2: "Len(p) = Len(s)"
  assume h3: "p \\in [1 .. Len (s) -> UNION Range (s)]"
  assume h4: "ALL k in 1 .. Len (s) : p[k] \\in s[k]"
  show "p[i] \\in s[i]" (is "?c")
  proof (rule bAllE [where x = i, OF h4])
    assume h5: "i \\notin 1 .. Len(s)"
    show "?c"
    using c h5 by blast
  next
    assume h5: "?c"
    show "?c"
    by (rule h5)
  qed
qed

(* ------------- Proof rules for strings ------------- *)

lemma zenon_stringdiffll : "s ~= t ==> e = s ==> f = t ==> e ~= f"
by auto

lemma zenon_stringdifflr : "s ~= t ==> e = s ==> t = f ==> e ~= f"
by auto

lemma zenon_stringdiffrl : "s ~= t ==> s = e ==> f = t ==> e ~= f"
by auto

lemma zenon_stringdiffrr : "s ~= t ==> s = e ==> t = f ==> e ~= f"
by auto

definition zenon_sa :: "[c, c] \<Rightarrow> c"
where "zenon_sa (s, e) \<equiv> IF isASeq (s) THEN Append (s, e) ELSE <<e>>"

lemma zenon_sa_seq: "isASeq (zenon_sa (s, e))"
  by (simp add: zenon_sa_def, rule disjE [of "isASeq(s)" "~isASeq(s)"],
      rule excluded_middle, simp+)

lemma zenon_sa_1 : "Append (<<>>, e) = zenon_sa (<<>>, e)"
by (auto simp add: zenon_sa_def)

lemma zenon_sa_2 :
  "Append (zenon_sa (s, e1), e2) = zenon_sa (zenon_sa (s, e1), e2)"
using zenon_sa_seq by (auto simp add: zenon_sa_def)

lemma zenon_sa_diff_0a :
  "zenon_sa (zenon_sa (s1, e1), e2) ~= zenon_sa (<<>>, f2)"
using zenon_sa_def zenon_sa_seq by auto

lemma zenon_sa_diff_0b :
  "zenon_sa (<<>>, f2) ~= zenon_sa (zenon_sa (s1, e1), e2)"
using zenon_sa_def zenon_sa_seq by auto

lemma zenon_sa_diff_1 :
  assumes h0: "e ~= f"
  shows "zenon_sa (<<>>, e) ~= zenon_sa (<<>>, f)"
using zenon_sa_def h0 by auto

lemma zenon_sa_diff_2 :
  assumes h0: "zenon_sa (e, s1) ~= zenon_sa (f, t1)"
  shows "zenon_sa (zenon_sa (e, s1), s2) ~= zenon_sa (zenon_sa (f, t1), s2)"
using zenon_sa_def zenon_sa_seq h0 by auto

lemma zenon_sa_diff_3 :
  assumes h0: "s2 ~= t2"
  shows "zenon_sa (zenon_sa (e, s1), s2) ~= zenon_sa (zenon_sa (f, t1), t2)"
using zenon_sa_def zenon_sa_seq h0 by auto

(* ------------- Proof rules for arithmetic --------- *)

lemma zenon_in_nat_0 : "~(0 \\in Nat) ==> FALSE"
by blast

lemma zenon_in_nat_1 : "~(1 \\in Nat) ==> FALSE"
by blast

lemma zenon_in_nat_2 : "~(2 \\in Nat) ==> FALSE"
by blast

lemma zenon_in_nat_succ :
  "~(Succ[x] \\in Nat) ==> (~(x \\in Nat) ==> FALSE) ==> FALSE"
by blast

lemma zenon_in_nat_succ_0 : "~(Succ[x] \\in Nat) ==> ~(x \\in Nat)"
by blast

(* ------------- Proof rules for records ------------- *)

lemma zenon_in_recordset_field :
  assumes a: "r \\in EnumFuncSet (doms, rngs)"
  and b: "i \\in DOMAIN (doms)"
  shows "r[doms[i]] \\in rngs[i]"
proof (rule EnumFuncSetE [OF a])
  assume h1: "r \\in [Range(doms) -> UNION Range(rngs)]"
  assume h2: "ALL i in DOMAIN doms : r[doms[i]] \\in rngs[i]"
  show "r[doms[i]] \\in rngs[i]" (is "?c")
  proof (rule bAllE [where x = i, OF h2])
    assume h3: "i \\notin DOMAIN doms"
    show "?c"
    using b h3 by blast
  next
    assume h3: "?c"
    show "?c"
    by (rule h3)
  qed
qed

lemma zenon_recfield_1:
  "l \\in DOMAIN r & r[l] = v ==>
   l \\in DOMAIN (r @@ m :> w) & (r @@ m :> w)[l] = v"
by auto

lemma zenon_recfield_2:
  "l \\notin DOMAIN r ==>
   l \\in DOMAIN (r @@ l :> v) & (r @@ l :> v)[l] = v"
by auto

lemma zenon_recfield_2b: "l \\in DOMAIN (l :> v) & (l :> v)[l] = v" by auto

lemma zenon_recfield_3:
  "l \\notin DOMAIN r ==> l ~= m ==> l \\notin DOMAIN (r @@ m :> v)"
by auto

lemma zenon_recfield_3b: "l ~= m ==> l \\notin DOMAIN (m :> v)" by auto

(* support lemmas for the generic proof rules *)

lemma zenon_range_1 : "isASeq (<<>>) & {} = Range (<<>>)" by auto

lemma zenon_range_2 :
  assumes h: "(isASeq (s) & a = Range (s))"
  shows "(isASeq (Append (s, x)) & addElt (x, a) = Range (Append (s, x)))"
using h by auto

lemma zenon_set_rev_1 : "a = {} \\cup c ==> c = a" by auto

lemma zenon_set_rev_2 : "a = addElt (x, b) \\cup c ==> a = b \\cup addElt (x, c)"
by auto

lemma zenon_set_rev_3 : "a = c ==> a = c \\cup {}" by auto

lemma zenon_tuple_dom_1 :
  "isASeq (<<>>) & isASeq (<<>>) & DOMAIN <<>> = DOMAIN <<>>"
by auto

lemma zenon_tuple_dom_2 :
  "isASeq (s) & isASeq (t) & DOMAIN s = DOMAIN t ==>
   isASeq (Append (s, x)) & isASeq (Append (t, y))
   & DOMAIN (Append (s, x)) = DOMAIN (Append (t, y))"
by auto

lemma zenon_tuple_dom_3 :
  "isASeq (s) & isASeq (t) & DOMAIN s = DOMAIN t ==> DOMAIN s = DOMAIN t"
by auto

lemma zenon_all_rec_1 : "ALL i in {} : r[doms[i]] \\in rngs[i]" by auto

lemma zenon_all_rec_2 :
  "ALL i in s : r[doms[i]] \\in rngs[i] ==>
   r[doms[j]] \\in rngs[j] ==>
   ALL i in addElt (j, s) : r[doms[i]] \\in rngs[i]"
by auto

lemma zenon_tuple_acc_1 :
  "isASeq (r) ==> Len (r) = n ==> x = Append (r, x) [Succ[n]]" by auto

lemma zenon_tuple_acc_2 :
  "isASeq (r) ==> k \\in Nat ==> 0 < k ==> k \<le> Len (r) ==>
   x = r[k] ==> x = Append (r, e) [k]"
by auto

definition zenon_ss :: "c \<Rightarrow> c"
where "zenon_ss (n) \<equiv> IF n \\in Nat THEN Succ[n] ELSE 1"

lemma zenon_ss_nat : "zenon_ss(x) \\in Nat" by (auto simp add: zenon_ss_def)

lemma zenon_ss_1 : "Succ[0] = zenon_ss(0)" by (auto simp add: zenon_ss_def)

lemma zenon_ss_2 : "Succ[zenon_ss(x)] = zenon_ss(zenon_ss(x))" by (auto simp add: zenon_ss_def)

lemma zenon_zero_lt : "0 < zenon_ss(x)"
  by (simp add: zenon_ss_def, rule disjE [of "x \\in Nat" "x \\notin Nat"], rule excluded_middle, simp+)

lemma zenon_ss_le_sa_1 : "zenon_ss(0) <= Len (zenon_sa (s, x))"
  by (auto simp add: zenon_ss_def zenon_sa_def, rule disjE [of "isASeq (s)" "~isASeq (s)"], rule excluded_middle, simp+)

lemma zenon_ss_le_sa_2 :
  fixes x y z
  assumes h0: "zenon_ss (x) <= Len (zenon_sa (s, y))"
  shows "zenon_ss (zenon_ss (x)) <= Len (zenon_sa (zenon_sa (s, y), z))"
proof -
  have h1: "Succ [Len (zenon_sa (s, y))] = Len (zenon_sa (zenon_sa (s, y), z))"
  using zenon_sa_seq by (auto simp add: zenon_sa_def)

  have h2: "Len (zenon_sa (s, y)) \\in Nat"
  using zenon_sa_seq by (rule LenInNat)
  have h3: "Succ [zenon_ss (x)] \<le> Succ [Len (zenon_sa (s, y))]"
  using zenon_ss_nat h2 h0 by (simp only: nat_Succ_leq_Succ)
  show ?thesis
  using h3 by (auto simp add: zenon_ss_2 h1)
qed

lemma zenon_dom_app_1 : "isASeq (<<>>) & 0 = Len (<<>>) & {} = 1..Len(<<>>)"
by auto

lemma zenon_dom_app_2 :
  assumes h: "isASeq (s) & n = Len (s) & x = 1 .. Len (s)"
  shows "isASeq (Append (s, y)) & Succ[n] = Len (Append (s, y))
         & addElt (Succ[n], x) = 1 .. Len (Append (s, y))" (is "?a & ?b & ?c")
using h by auto

(* generic proof rules instantiated for small n *)

(*** BEGIN AUTO-GENERATED STUFF ***)

lemma zenon_inrecordsetI1 :
  fixes r l1x s1x
  assumes hfcn: "isAFcn (r)"
  assumes hdom: "DOMAIN r = {l1x}"
  assumes h1: "r[l1x] \\in s1x"
  shows "r \\in [l1x : s1x]"
proof -
  let ?doms = "<<l1x>>"
  let ?domset = "{l1x}"
  let ?domsetrev = "{l1x}"
  let ?rngs = "<<s1x>>"
  let ?n0n = "0"
  let ?n1n = "Succ[?n0n]"
  let ?indices = "{?n1n}"
  have hdomx : "?domsetrev = DOMAIN r"
  by (rule zenon_set_rev_1, (rule zenon_set_rev_2)+, rule zenon_set_rev_3,
      rule hdom)
  show "r \\in EnumFuncSet (?doms, ?rngs)"
  proof (rule EnumFuncSetI [of r, OF hfcn])
    have hx1: "isASeq (?doms) & ?domsetrev = Range (?doms)"
    by ((rule zenon_range_2)+, rule zenon_range_1)
    have hx2: "?domsetrev = Range (?doms)"
    by (rule conjD2 [OF hx1])
    show "DOMAIN r = Range (?doms)"
    by (rule subst [where P = "%x. x = Range (?doms)", OF hdomx hx2])
  next
    show "DOMAIN ?rngs = DOMAIN ?doms"
    by (rule zenon_tuple_dom_3, (rule zenon_tuple_dom_2)+,
        rule zenon_tuple_dom_1)
  next
    have hdomseq: "isASeq (?doms)" by auto
    have hindx: "isASeq (?doms) & ?n1n = Len (?doms)
                  & ?indices = DOMAIN ?doms"
    by (simp only: DomainSeqLen [OF hdomseq], (rule zenon_dom_app_2)+,
        rule zenon_dom_app_1)
    have hind: "?indices = DOMAIN ?doms" by (rule conjE [OF hindx], elim conjE)
    show "ALL i in DOMAIN ?doms : r[?doms[i]] \\in ?rngs[i]"
    proof (rule subst [OF hind], (rule zenon_all_rec_2)+, rule zenon_all_rec_1)

      have hn: "l1x = ?doms[?n1n]"
      by (((rule zenon_tuple_acc_2, safe, simp only: zenon_ss_1 zenon_ss_2,
            rule zenon_zero_lt,
            simp only: zenon_ss_1 zenon_ss_2 zenon_sa_1 zenon_sa_2,
            ((rule zenon_ss_le_sa_2)+)?, rule zenon_ss_le_sa_1
           )+)?,
          rule zenon_tuple_acc_1, auto)
      have hs: "s1x = ?rngs[?n1n]"
      by (((rule zenon_tuple_acc_2, safe, simp only: zenon_ss_1 zenon_ss_2,
            rule zenon_zero_lt,
            simp only: zenon_ss_1 zenon_ss_2 zenon_sa_1 zenon_sa_2,
            ((rule zenon_ss_le_sa_2)+)?, rule zenon_ss_le_sa_1
           )+)?,
          rule zenon_tuple_acc_1, auto)
      show "r[?doms[?n1n]] \\in ?rngs[?n1n]"
      by (rule subst[OF hs], rule subst[OF hn], rule h1)

    qed
  qed
qed

lemma zenon_inrecordsetI2 :
  fixes r l1x s1x l2x s2x
  assumes hfcn: "isAFcn (r)"
  assumes hdom: "DOMAIN r = {l1x, l2x}"
  assumes h1: "r[l1x] \\in s1x"
  assumes h2: "r[l2x] \\in s2x"
  shows "r \\in [l1x : s1x, l2x : s2x]"
proof -
  let ?doms = "<<l1x, l2x>>"
  let ?domset = "{l1x, l2x}"
  let ?domsetrev = "{l2x, l1x}"
  let ?rngs = "<<s1x, s2x>>"
  let ?n0n = "0"
  let ?n1n = "Succ[?n0n]"
  let ?n2n = "Succ[?n1n]"
  let ?indices = "{?n2n, ?n1n}"
  have hdomx : "?domsetrev = DOMAIN r"
  by (rule zenon_set_rev_1, (rule zenon_set_rev_2)+, rule zenon_set_rev_3,
      rule hdom)
  show "r \\in EnumFuncSet (?doms, ?rngs)"
  proof (rule EnumFuncSetI [of r, OF hfcn])
    have hx1: "isASeq (?doms) & ?domsetrev = Range (?doms)"
    by ((rule zenon_range_2)+, rule zenon_range_1)
    have hx2: "?domsetrev = Range (?doms)"
    by (rule conjD2 [OF hx1])
    show "DOMAIN r = Range (?doms)"
    by (rule subst [where P = "%x. x = Range (?doms)", OF hdomx hx2])
  next
    show "DOMAIN ?rngs = DOMAIN ?doms"
    by (rule zenon_tuple_dom_3, (rule zenon_tuple_dom_2)+,
        rule zenon_tuple_dom_1)
  next
    have hdomseq: "isASeq (?doms)" by auto
    have hindx: "isASeq (?doms) & ?n2n = Len (?doms)
                  & ?indices = DOMAIN ?doms"
    by (simp only: DomainSeqLen [OF hdomseq], (rule zenon_dom_app_2)+,
        rule zenon_dom_app_1)
    have hind: "?indices = DOMAIN ?doms" by (rule conjE [OF hindx], elim conjE)
    show "ALL i in DOMAIN ?doms : r[?doms[i]] \\in ?rngs[i]"
    proof (rule subst [OF hind], (rule zenon_all_rec_2)+, rule zenon_all_rec_1)

      have hn: "l1x = ?doms[?n1n]"
      by (((rule zenon_tuple_acc_2, safe, simp only: zenon_ss_1 zenon_ss_2,
            rule zenon_zero_lt,
            simp only: zenon_ss_1 zenon_ss_2 zenon_sa_1 zenon_sa_2,
            ((rule zenon_ss_le_sa_2)+)?, rule zenon_ss_le_sa_1
           )+)?,
          rule zenon_tuple_acc_1, auto)
      have hs: "s1x = ?rngs[?n1n]"
      by (((rule zenon_tuple_acc_2, safe, simp only: zenon_ss_1 zenon_ss_2,
            rule zenon_zero_lt,
            simp only: zenon_ss_1 zenon_ss_2 zenon_sa_1 zenon_sa_2,
            ((rule zenon_ss_le_sa_2)+)?, rule zenon_ss_le_sa_1
           )+)?,
          rule zenon_tuple_acc_1, auto)
      show "r[?doms[?n1n]] \\in ?rngs[?n1n]"
      by (rule subst[OF hs], rule subst[OF hn], rule h1)
    next
      have hn: "l2x = ?doms[?n2n]"
      by (((rule zenon_tuple_acc_2, safe, simp only: zenon_ss_1 zenon_ss_2,
            rule zenon_zero_lt,
            simp only: zenon_ss_1 zenon_ss_2 zenon_sa_1 zenon_sa_2,
            ((rule zenon_ss_le_sa_2)+)?, rule zenon_ss_le_sa_1
           )+)?,
          rule zenon_tuple_acc_1, auto)
      have hs: "s2x = ?rngs[?n2n]"
      by (((rule zenon_tuple_acc_2, safe, simp only: zenon_ss_1 zenon_ss_2,
            rule zenon_zero_lt,
            simp only: zenon_ss_1 zenon_ss_2 zenon_sa_1 zenon_sa_2,
            ((rule zenon_ss_le_sa_2)+)?, rule zenon_ss_le_sa_1
           )+)?,
          rule zenon_tuple_acc_1, auto)
      show "r[?doms[?n2n]] \\in ?rngs[?n2n]"
      by (rule subst[OF hs], rule subst[OF hn], rule h2)

    qed
  qed
qed

lemma zenon_inrecordsetI3 :
  fixes r l1x s1x l2x s2x l3x s3x
  assumes hfcn: "isAFcn (r)"
  assumes hdom: "DOMAIN r = {l1x, l2x, l3x}"
  assumes h1: "r[l1x] \\in s1x"
  assumes h2: "r[l2x] \\in s2x"
  assumes h3: "r[l3x] \\in s3x"
  shows "r \\in [l1x : s1x, l2x : s2x, l3x : s3x]"
proof -
  let ?doms = "<<l1x, l2x, l3x>>"
  let ?domset = "{l1x, l2x, l3x}"
  let ?domsetrev = "{l3x, l2x, l1x}"
  let ?rngs = "<<s1x, s2x, s3x>>"
  let ?n0n = "0"
  let ?n1n = "Succ[?n0n]"
  let ?n2n = "Succ[?n1n]"
  let ?n3n = "Succ[?n2n]"
  let ?indices = "{?n3n, ?n2n, ?n1n}"
  have hdomx : "?domsetrev = DOMAIN r"
  by (rule zenon_set_rev_1, (rule zenon_set_rev_2)+, rule zenon_set_rev_3,
      rule hdom)
  show "r \\in EnumFuncSet (?doms, ?rngs)"
  proof (rule EnumFuncSetI [of r, OF hfcn])
    have hx1: "isASeq (?doms) & ?domsetrev = Range (?doms)"
    by ((rule zenon_range_2)+, rule zenon_range_1)
    have hx2: "?domsetrev = Range (?doms)"
    by (rule conjD2 [OF hx1])
    show "DOMAIN r = Range (?doms)"
    by (rule subst [where P = "%x. x = Range (?doms)", OF hdomx hx2])
  next
    show "DOMAIN ?rngs = DOMAIN ?doms"
    by (rule zenon_tuple_dom_3, (rule zenon_tuple_dom_2)+,
        rule zenon_tuple_dom_1)
  next
    have hdomseq: "isASeq (?doms)" by auto
    have hindx: "isASeq (?doms) & ?n3n = Len (?doms)
                  & ?indices = DOMAIN ?doms"
    by (simp only: DomainSeqLen [OF hdomseq], (rule zenon_dom_app_2)+,
        rule zenon_dom_app_1)
    have hind: "?indices = DOMAIN ?doms" by (rule conjE [OF hindx], elim conjE)
    show "ALL i in DOMAIN ?doms : r[?doms[i]] \\in ?rngs[i]"
    proof (rule subst [OF hind], (rule zenon_all_rec_2)+, rule zenon_all_rec_1)

      have hn: "l1x = ?doms[?n1n]"
      by (((rule zenon_tuple_acc_2, safe, simp only: zenon_ss_1 zenon_ss_2,
            rule zenon_zero_lt,
            simp only: zenon_ss_1 zenon_ss_2 zenon_sa_1 zenon_sa_2,
            ((rule zenon_ss_le_sa_2)+)?, rule zenon_ss_le_sa_1
           )+)?,
          rule zenon_tuple_acc_1, auto)
      have hs: "s1x = ?rngs[?n1n]"
      by (((rule zenon_tuple_acc_2, safe, simp only: zenon_ss_1 zenon_ss_2,
            rule zenon_zero_lt,
            simp only: zenon_ss_1 zenon_ss_2 zenon_sa_1 zenon_sa_2,
            ((rule zenon_ss_le_sa_2)+)?, rule zenon_ss_le_sa_1
           )+)?,
          rule zenon_tuple_acc_1, auto)
      show "r[?doms[?n1n]] \\in ?rngs[?n1n]"
      by (rule subst[OF hs], rule subst[OF hn], rule h1)
    next
      have hn: "l2x = ?doms[?n2n]"
      by (((rule zenon_tuple_acc_2, safe, simp only: zenon_ss_1 zenon_ss_2,
            rule zenon_zero_lt,
            simp only: zenon_ss_1 zenon_ss_2 zenon_sa_1 zenon_sa_2,
            ((rule zenon_ss_le_sa_2)+)?, rule zenon_ss_le_sa_1
           )+)?,
          rule zenon_tuple_acc_1, auto)
      have hs: "s2x = ?rngs[?n2n]"
      by (((rule zenon_tuple_acc_2, safe, simp only: zenon_ss_1 zenon_ss_2,
            rule zenon_zero_lt,
            simp only: zenon_ss_1 zenon_ss_2 zenon_sa_1 zenon_sa_2,
            ((rule zenon_ss_le_sa_2)+)?, rule zenon_ss_le_sa_1
           )+)?,
          rule zenon_tuple_acc_1, auto)
      show "r[?doms[?n2n]] \\in ?rngs[?n2n]"
      by (rule subst[OF hs], rule subst[OF hn], rule h2)
    next
      have hn: "l3x = ?doms[?n3n]"
      by (((rule zenon_tuple_acc_2, safe, simp only: zenon_ss_1 zenon_ss_2,
            rule zenon_zero_lt,
            simp only: zenon_ss_1 zenon_ss_2 zenon_sa_1 zenon_sa_2,
            ((rule zenon_ss_le_sa_2)+)?, rule zenon_ss_le_sa_1
           )+)?,
          rule zenon_tuple_acc_1, auto)
      have hs: "s3x = ?rngs[?n3n]"
      by (((rule zenon_tuple_acc_2, safe, simp only: zenon_ss_1 zenon_ss_2,
            rule zenon_zero_lt,
            simp only: zenon_ss_1 zenon_ss_2 zenon_sa_1 zenon_sa_2,
            ((rule zenon_ss_le_sa_2)+)?, rule zenon_ss_le_sa_1
           )+)?,
          rule zenon_tuple_acc_1, auto)
      show "r[?doms[?n3n]] \\in ?rngs[?n3n]"
      by (rule subst[OF hs], rule subst[OF hn], rule h3)

    qed
  qed
qed

lemma zenon_inrecordsetI4 :
  fixes r l1x s1x l2x s2x l3x s3x l4x s4x
  assumes hfcn: "isAFcn (r)"
  assumes hdom: "DOMAIN r = {l1x, l2x, l3x, l4x}"
  assumes h1: "r[l1x] \\in s1x"
  assumes h2: "r[l2x] \\in s2x"
  assumes h3: "r[l3x] \\in s3x"
  assumes h4: "r[l4x] \\in s4x"
  shows "r \\in [l1x : s1x, l2x : s2x, l3x : s3x, l4x : s4x]"
proof -
  let ?doms = "<<l1x, l2x, l3x, l4x>>"
  let ?domset = "{l1x, l2x, l3x, l4x}"
  let ?domsetrev = "{l4x, l3x, l2x, l1x}"
  let ?rngs = "<<s1x, s2x, s3x, s4x>>"
  let ?n0n = "0"
  let ?n1n = "Succ[?n0n]"
  let ?n2n = "Succ[?n1n]"
  let ?n3n = "Succ[?n2n]"
  let ?n4n = "Succ[?n3n]"
  let ?indices = "{?n4n, ?n3n, ?n2n, ?n1n}"
  have hdomx : "?domsetrev = DOMAIN r"
  by (rule zenon_set_rev_1, (rule zenon_set_rev_2)+, rule zenon_set_rev_3,
      rule hdom)
  show "r \\in EnumFuncSet (?doms, ?rngs)"
  proof (rule EnumFuncSetI [of r, OF hfcn])
    have hx1: "isASeq (?doms) & ?domsetrev = Range (?doms)"
    by ((rule zenon_range_2)+, rule zenon_range_1)
    have hx2: "?domsetrev = Range (?doms)"
    by (rule conjD2 [OF hx1])
    show "DOMAIN r = Range (?doms)"
    by (rule subst [where P = "%x. x = Range (?doms)", OF hdomx hx2])
  next
    show "DOMAIN ?rngs = DOMAIN ?doms"
    by (rule zenon_tuple_dom_3, (rule zenon_tuple_dom_2)+,
        rule zenon_tuple_dom_1)
  next
    have hdomseq: "isASeq (?doms)" by auto
    have hindx: "isASeq (?doms) & ?n4n = Len (?doms)
                  & ?indices = DOMAIN ?doms"
    by (simp only: DomainSeqLen [OF hdomseq], (rule zenon_dom_app_2)+,
        rule zenon_dom_app_1)
    have hind: "?indices = DOMAIN ?doms" by (rule conjE [OF hindx], elim conjE)
    show "ALL i in DOMAIN ?doms : r[?doms[i]] \\in ?rngs[i]"
    proof (rule subst [OF hind], (rule zenon_all_rec_2)+, rule zenon_all_rec_1)

      have hn: "l1x = ?doms[?n1n]"
      by (((rule zenon_tuple_acc_2, safe, simp only: zenon_ss_1 zenon_ss_2,
            rule zenon_zero_lt,
            simp only: zenon_ss_1 zenon_ss_2 zenon_sa_1 zenon_sa_2,
            ((rule zenon_ss_le_sa_2)+)?, rule zenon_ss_le_sa_1
           )+)?,
          rule zenon_tuple_acc_1, auto)
      have hs: "s1x = ?rngs[?n1n]"
      by (((rule zenon_tuple_acc_2, safe, simp only: zenon_ss_1 zenon_ss_2,
            rule zenon_zero_lt,
            simp only: zenon_ss_1 zenon_ss_2 zenon_sa_1 zenon_sa_2,
            ((rule zenon_ss_le_sa_2)+)?, rule zenon_ss_le_sa_1
           )+)?,
          rule zenon_tuple_acc_1, auto)
      show "r[?doms[?n1n]] \\in ?rngs[?n1n]"
      by (rule subst[OF hs], rule subst[OF hn], rule h1)
    next
      have hn: "l2x = ?doms[?n2n]"
      by (((rule zenon_tuple_acc_2, safe, simp only: zenon_ss_1 zenon_ss_2,
            rule zenon_zero_lt,
            simp only: zenon_ss_1 zenon_ss_2 zenon_sa_1 zenon_sa_2,
            ((rule zenon_ss_le_sa_2)+)?, rule zenon_ss_le_sa_1
           )+)?,
          rule zenon_tuple_acc_1, auto)
      have hs: "s2x = ?rngs[?n2n]"
      by (((rule zenon_tuple_acc_2, safe, simp only: zenon_ss_1 zenon_ss_2,
            rule zenon_zero_lt,
            simp only: zenon_ss_1 zenon_ss_2 zenon_sa_1 zenon_sa_2,
            ((rule zenon_ss_le_sa_2)+)?, rule zenon_ss_le_sa_1
           )+)?,
          rule zenon_tuple_acc_1, auto)
      show "r[?doms[?n2n]] \\in ?rngs[?n2n]"
      by (rule subst[OF hs], rule subst[OF hn], rule h2)
    next
      have hn: "l3x = ?doms[?n3n]"
      by (((rule zenon_tuple_acc_2, safe, simp only: zenon_ss_1 zenon_ss_2,
            rule zenon_zero_lt,
            simp only: zenon_ss_1 zenon_ss_2 zenon_sa_1 zenon_sa_2,
            ((rule zenon_ss_le_sa_2)+)?, rule zenon_ss_le_sa_1
           )+)?,
          rule zenon_tuple_acc_1, auto)
      have hs: "s3x = ?rngs[?n3n]"
      by (((rule zenon_tuple_acc_2, safe, simp only: zenon_ss_1 zenon_ss_2,
            rule zenon_zero_lt,
            simp only: zenon_ss_1 zenon_ss_2 zenon_sa_1 zenon_sa_2,
            ((rule zenon_ss_le_sa_2)+)?, rule zenon_ss_le_sa_1
           )+)?,
          rule zenon_tuple_acc_1, auto)
      show "r[?doms[?n3n]] \\in ?rngs[?n3n]"
      by (rule subst[OF hs], rule subst[OF hn], rule h3)
    next
      have hn: "l4x = ?doms[?n4n]"
      by (((rule zenon_tuple_acc_2, safe, simp only: zenon_ss_1 zenon_ss_2,
            rule zenon_zero_lt,
            simp only: zenon_ss_1 zenon_ss_2 zenon_sa_1 zenon_sa_2,
            ((rule zenon_ss_le_sa_2)+)?, rule zenon_ss_le_sa_1
           )+)?,
          rule zenon_tuple_acc_1, auto)
      have hs: "s4x = ?rngs[?n4n]"
      by (((rule zenon_tuple_acc_2, safe, simp only: zenon_ss_1 zenon_ss_2,
            rule zenon_zero_lt,
            simp only: zenon_ss_1 zenon_ss_2 zenon_sa_1 zenon_sa_2,
            ((rule zenon_ss_le_sa_2)+)?, rule zenon_ss_le_sa_1
           )+)?,
          rule zenon_tuple_acc_1, auto)
      show "r[?doms[?n4n]] \\in ?rngs[?n4n]"
      by (rule subst[OF hs], rule subst[OF hn], rule h4)

    qed
  qed
qed

lemma zenon_inrecordsetI5 :
  fixes r l1x s1x l2x s2x l3x s3x l4x s4x l5x s5x
  assumes hfcn: "isAFcn (r)"
  assumes hdom: "DOMAIN r = {l1x, l2x, l3x, l4x, l5x}"
  assumes h1: "r[l1x] \\in s1x"
  assumes h2: "r[l2x] \\in s2x"
  assumes h3: "r[l3x] \\in s3x"
  assumes h4: "r[l4x] \\in s4x"
  assumes h5: "r[l5x] \\in s5x"
  shows "r \\in [l1x : s1x, l2x : s2x, l3x : s3x, l4x : s4x, l5x : s5x]"
proof -
  let ?doms = "<<l1x, l2x, l3x, l4x, l5x>>"
  let ?domset = "{l1x, l2x, l3x, l4x, l5x}"
  let ?domsetrev = "{l5x, l4x, l3x, l2x, l1x}"
  let ?rngs = "<<s1x, s2x, s3x, s4x, s5x>>"
  let ?n0n = "0"
  let ?n1n = "Succ[?n0n]"
  let ?n2n = "Succ[?n1n]"
  let ?n3n = "Succ[?n2n]"
  let ?n4n = "Succ[?n3n]"
  let ?n5n = "Succ[?n4n]"
  let ?indices = "{?n5n, ?n4n, ?n3n, ?n2n, ?n1n}"
  have hdomx : "?domsetrev = DOMAIN r"
  by (rule zenon_set_rev_1, (rule zenon_set_rev_2)+, rule zenon_set_rev_3,
      rule hdom)
  show "r \\in EnumFuncSet (?doms, ?rngs)"
  proof (rule EnumFuncSetI [of r, OF hfcn])
    have hx1: "isASeq (?doms) & ?domsetrev = Range (?doms)"
    by ((rule zenon_range_2)+, rule zenon_range_1)
    have hx2: "?domsetrev = Range (?doms)"
    by (rule conjD2 [OF hx1])
    show "DOMAIN r = Range (?doms)"
    by (rule subst [where P = "%x. x = Range (?doms)", OF hdomx hx2])
  next
    show "DOMAIN ?rngs = DOMAIN ?doms"
    by (rule zenon_tuple_dom_3, (rule zenon_tuple_dom_2)+,
        rule zenon_tuple_dom_1)
  next
    have hdomseq: "isASeq (?doms)" by auto
    have hindx: "isASeq (?doms) & ?n5n = Len (?doms)
                  & ?indices = DOMAIN ?doms"
    by (simp only: DomainSeqLen [OF hdomseq], (rule zenon_dom_app_2)+,
        rule zenon_dom_app_1)
    have hind: "?indices = DOMAIN ?doms" by (rule conjE [OF hindx], elim conjE)
    show "ALL i in DOMAIN ?doms : r[?doms[i]] \\in ?rngs[i]"
    proof (rule subst [OF hind], (rule zenon_all_rec_2)+, rule zenon_all_rec_1)

      have hn: "l1x = ?doms[?n1n]"
      by (((rule zenon_tuple_acc_2, safe, simp only: zenon_ss_1 zenon_ss_2,
            rule zenon_zero_lt,
            simp only: zenon_ss_1 zenon_ss_2 zenon_sa_1 zenon_sa_2,
            ((rule zenon_ss_le_sa_2)+)?, rule zenon_ss_le_sa_1
           )+)?,
          rule zenon_tuple_acc_1, auto)
      have hs: "s1x = ?rngs[?n1n]"
      by (((rule zenon_tuple_acc_2, safe, simp only: zenon_ss_1 zenon_ss_2,
            rule zenon_zero_lt,
            simp only: zenon_ss_1 zenon_ss_2 zenon_sa_1 zenon_sa_2,
            ((rule zenon_ss_le_sa_2)+)?, rule zenon_ss_le_sa_1
           )+)?,
          rule zenon_tuple_acc_1, auto)
      show "r[?doms[?n1n]] \\in ?rngs[?n1n]"
      by (rule subst[OF hs], rule subst[OF hn], rule h1)
    next
      have hn: "l2x = ?doms[?n2n]"
      by (((rule zenon_tuple_acc_2, safe, simp only: zenon_ss_1 zenon_ss_2,
            rule zenon_zero_lt,
            simp only: zenon_ss_1 zenon_ss_2 zenon_sa_1 zenon_sa_2,
            ((rule zenon_ss_le_sa_2)+)?, rule zenon_ss_le_sa_1
           )+)?,
          rule zenon_tuple_acc_1, auto)
      have hs: "s2x = ?rngs[?n2n]"
      by (((rule zenon_tuple_acc_2, safe, simp only: zenon_ss_1 zenon_ss_2,
            rule zenon_zero_lt,
            simp only: zenon_ss_1 zenon_ss_2 zenon_sa_1 zenon_sa_2,
            ((rule zenon_ss_le_sa_2)+)?, rule zenon_ss_le_sa_1
           )+)?,
          rule zenon_tuple_acc_1, auto)
      show "r[?doms[?n2n]] \\in ?rngs[?n2n]"
      by (rule subst[OF hs], rule subst[OF hn], rule h2)
    next
      have hn: "l3x = ?doms[?n3n]"
      by (((rule zenon_tuple_acc_2, safe, simp only: zenon_ss_1 zenon_ss_2,
            rule zenon_zero_lt,
            simp only: zenon_ss_1 zenon_ss_2 zenon_sa_1 zenon_sa_2,
            ((rule zenon_ss_le_sa_2)+)?, rule zenon_ss_le_sa_1
           )+)?,
          rule zenon_tuple_acc_1, auto)
      have hs: "s3x = ?rngs[?n3n]"
      by (((rule zenon_tuple_acc_2, safe, simp only: zenon_ss_1 zenon_ss_2,
            rule zenon_zero_lt,
            simp only: zenon_ss_1 zenon_ss_2 zenon_sa_1 zenon_sa_2,
            ((rule zenon_ss_le_sa_2)+)?, rule zenon_ss_le_sa_1
           )+)?,
          rule zenon_tuple_acc_1, auto)
      show "r[?doms[?n3n]] \\in ?rngs[?n3n]"
      by (rule subst[OF hs], rule subst[OF hn], rule h3)
    next
      have hn: "l4x = ?doms[?n4n]"
      by (((rule zenon_tuple_acc_2, safe, simp only: zenon_ss_1 zenon_ss_2,
            rule zenon_zero_lt,
            simp only: zenon_ss_1 zenon_ss_2 zenon_sa_1 zenon_sa_2,
            ((rule zenon_ss_le_sa_2)+)?, rule zenon_ss_le_sa_1
           )+)?,
          rule zenon_tuple_acc_1, auto)
      have hs: "s4x = ?rngs[?n4n]"
      by (((rule zenon_tuple_acc_2, safe, simp only: zenon_ss_1 zenon_ss_2,
            rule zenon_zero_lt,
            simp only: zenon_ss_1 zenon_ss_2 zenon_sa_1 zenon_sa_2,
            ((rule zenon_ss_le_sa_2)+)?, rule zenon_ss_le_sa_1
           )+)?,
          rule zenon_tuple_acc_1, auto)
      show "r[?doms[?n4n]] \\in ?rngs[?n4n]"
      by (rule subst[OF hs], rule subst[OF hn], rule h4)
    next
      have hn: "l5x = ?doms[?n5n]"
      by (((rule zenon_tuple_acc_2, safe, simp only: zenon_ss_1 zenon_ss_2,
            rule zenon_zero_lt,
            simp only: zenon_ss_1 zenon_ss_2 zenon_sa_1 zenon_sa_2,
            ((rule zenon_ss_le_sa_2)+)?, rule zenon_ss_le_sa_1
           )+)?,
          rule zenon_tuple_acc_1, auto)
      have hs: "s5x = ?rngs[?n5n]"
      by (((rule zenon_tuple_acc_2, safe, simp only: zenon_ss_1 zenon_ss_2,
            rule zenon_zero_lt,
            simp only: zenon_ss_1 zenon_ss_2 zenon_sa_1 zenon_sa_2,
            ((rule zenon_ss_le_sa_2)+)?, rule zenon_ss_le_sa_1
           )+)?,
          rule zenon_tuple_acc_1, auto)
      show "r[?doms[?n5n]] \\in ?rngs[?n5n]"
      by (rule subst[OF hs], rule subst[OF hn], rule h5)

    qed
  qed
qed

lemma zenon_inrecordsetI6 :
  fixes r l1x s1x l2x s2x l3x s3x l4x s4x l5x s5x l6x s6x
  assumes hfcn: "isAFcn (r)"
  assumes hdom: "DOMAIN r = {l1x, l2x, l3x, l4x, l5x, l6x}"
  assumes h1: "r[l1x] \\in s1x"
  assumes h2: "r[l2x] \\in s2x"
  assumes h3: "r[l3x] \\in s3x"
  assumes h4: "r[l4x] \\in s4x"
  assumes h5: "r[l5x] \\in s5x"
  assumes h6: "r[l6x] \\in s6x"
  shows "r \\in [l1x : s1x, l2x : s2x, l3x : s3x, l4x : s4x, l5x : s5x, l6x : s6x]"
proof -
  let ?doms = "<<l1x, l2x, l3x, l4x, l5x, l6x>>"
  let ?domset = "{l1x, l2x, l3x, l4x, l5x, l6x}"
  let ?domsetrev = "{l6x, l5x, l4x, l3x, l2x, l1x}"
  let ?rngs = "<<s1x, s2x, s3x, s4x, s5x, s6x>>"
  let ?n0n = "0"
  let ?n1n = "Succ[?n0n]"
  let ?n2n = "Succ[?n1n]"
  let ?n3n = "Succ[?n2n]"
  let ?n4n = "Succ[?n3n]"
  let ?n5n = "Succ[?n4n]"
  let ?n6n = "Succ[?n5n]"
  let ?indices = "{?n6n, ?n5n, ?n4n, ?n3n, ?n2n, ?n1n}"
  have hdomx : "?domsetrev = DOMAIN r"
  by (rule zenon_set_rev_1, (rule zenon_set_rev_2)+, rule zenon_set_rev_3,
      rule hdom)
  show "r \\in EnumFuncSet (?doms, ?rngs)"
  proof (rule EnumFuncSetI [of r, OF hfcn])
    have hx1: "isASeq (?doms) & ?domsetrev = Range (?doms)"
    by ((rule zenon_range_2)+, rule zenon_range_1)
    have hx2: "?domsetrev = Range (?doms)"
    by (rule conjD2 [OF hx1])
    show "DOMAIN r = Range (?doms)"
    by (rule subst [where P = "%x. x = Range (?doms)", OF hdomx hx2])
  next
    show "DOMAIN ?rngs = DOMAIN ?doms"
    by (rule zenon_tuple_dom_3, (rule zenon_tuple_dom_2)+,
        rule zenon_tuple_dom_1)
  next
    have hdomseq: "isASeq (?doms)" by auto
    have hindx: "isASeq (?doms) & ?n6n = Len (?doms)
                  & ?indices = DOMAIN ?doms"
    by (simp only: DomainSeqLen [OF hdomseq], (rule zenon_dom_app_2)+,
        rule zenon_dom_app_1)
    have hind: "?indices = DOMAIN ?doms" by (rule conjE [OF hindx], elim conjE)
    show "ALL i in DOMAIN ?doms : r[?doms[i]] \\in ?rngs[i]"
    proof (rule subst [OF hind], (rule zenon_all_rec_2)+, rule zenon_all_rec_1)

      have hn: "l1x = ?doms[?n1n]"
      by (((rule zenon_tuple_acc_2, safe, simp only: zenon_ss_1 zenon_ss_2,
            rule zenon_zero_lt,
            simp only: zenon_ss_1 zenon_ss_2 zenon_sa_1 zenon_sa_2,
            ((rule zenon_ss_le_sa_2)+)?, rule zenon_ss_le_sa_1
           )+)?,
          rule zenon_tuple_acc_1, auto)
      have hs: "s1x = ?rngs[?n1n]"
      by (((rule zenon_tuple_acc_2, safe, simp only: zenon_ss_1 zenon_ss_2,
            rule zenon_zero_lt,
            simp only: zenon_ss_1 zenon_ss_2 zenon_sa_1 zenon_sa_2,
            ((rule zenon_ss_le_sa_2)+)?, rule zenon_ss_le_sa_1
           )+)?,
          rule zenon_tuple_acc_1, auto)
      show "r[?doms[?n1n]] \\in ?rngs[?n1n]"
      by (rule subst[OF hs], rule subst[OF hn], rule h1)
    next
      have hn: "l2x = ?doms[?n2n]"
      by (((rule zenon_tuple_acc_2, safe, simp only: zenon_ss_1 zenon_ss_2,
            rule zenon_zero_lt,
            simp only: zenon_ss_1 zenon_ss_2 zenon_sa_1 zenon_sa_2,
            ((rule zenon_ss_le_sa_2)+)?, rule zenon_ss_le_sa_1
           )+)?,
          rule zenon_tuple_acc_1, auto)
      have hs: "s2x = ?rngs[?n2n]"
      by (((rule zenon_tuple_acc_2, safe, simp only: zenon_ss_1 zenon_ss_2,
            rule zenon_zero_lt,
            simp only: zenon_ss_1 zenon_ss_2 zenon_sa_1 zenon_sa_2,
            ((rule zenon_ss_le_sa_2)+)?, rule zenon_ss_le_sa_1
           )+)?,
          rule zenon_tuple_acc_1, auto)
      show "r[?doms[?n2n]] \\in ?rngs[?n2n]"
      by (rule subst[OF hs], rule subst[OF hn], rule h2)
    next
      have hn: "l3x = ?doms[?n3n]"
      by (((rule zenon_tuple_acc_2, safe, simp only: zenon_ss_1 zenon_ss_2,
            rule zenon_zero_lt,
            simp only: zenon_ss_1 zenon_ss_2 zenon_sa_1 zenon_sa_2,
            ((rule zenon_ss_le_sa_2)+)?, rule zenon_ss_le_sa_1
           )+)?,
          rule zenon_tuple_acc_1, auto)
      have hs: "s3x = ?rngs[?n3n]"
      by (((rule zenon_tuple_acc_2, safe, simp only: zenon_ss_1 zenon_ss_2,
            rule zenon_zero_lt,
            simp only: zenon_ss_1 zenon_ss_2 zenon_sa_1 zenon_sa_2,
            ((rule zenon_ss_le_sa_2)+)?, rule zenon_ss_le_sa_1
           )+)?,
          rule zenon_tuple_acc_1, auto)
      show "r[?doms[?n3n]] \\in ?rngs[?n3n]"
      by (rule subst[OF hs], rule subst[OF hn], rule h3)
    next
      have hn: "l4x = ?doms[?n4n]"
      by (((rule zenon_tuple_acc_2, safe, simp only: zenon_ss_1 zenon_ss_2,
            rule zenon_zero_lt,
            simp only: zenon_ss_1 zenon_ss_2 zenon_sa_1 zenon_sa_2,
            ((rule zenon_ss_le_sa_2)+)?, rule zenon_ss_le_sa_1
           )+)?,
          rule zenon_tuple_acc_1, auto)
      have hs: "s4x = ?rngs[?n4n]"
      by (((rule zenon_tuple_acc_2, safe, simp only: zenon_ss_1 zenon_ss_2,
            rule zenon_zero_lt,
            simp only: zenon_ss_1 zenon_ss_2 zenon_sa_1 zenon_sa_2,
            ((rule zenon_ss_le_sa_2)+)?, rule zenon_ss_le_sa_1
           )+)?,
          rule zenon_tuple_acc_1, auto)
      show "r[?doms[?n4n]] \\in ?rngs[?n4n]"
      by (rule subst[OF hs], rule subst[OF hn], rule h4)
    next
      have hn: "l5x = ?doms[?n5n]"
      by (((rule zenon_tuple_acc_2, safe, simp only: zenon_ss_1 zenon_ss_2,
            rule zenon_zero_lt,
            simp only: zenon_ss_1 zenon_ss_2 zenon_sa_1 zenon_sa_2,
            ((rule zenon_ss_le_sa_2)+)?, rule zenon_ss_le_sa_1
           )+)?,
          rule zenon_tuple_acc_1, auto)
      have hs: "s5x = ?rngs[?n5n]"
      by (((rule zenon_tuple_acc_2, safe, simp only: zenon_ss_1 zenon_ss_2,
            rule zenon_zero_lt,
            simp only: zenon_ss_1 zenon_ss_2 zenon_sa_1 zenon_sa_2,
            ((rule zenon_ss_le_sa_2)+)?, rule zenon_ss_le_sa_1
           )+)?,
          rule zenon_tuple_acc_1, auto)
      show "r[?doms[?n5n]] \\in ?rngs[?n5n]"
      by (rule subst[OF hs], rule subst[OF hn], rule h5)
    next
      have hn: "l6x = ?doms[?n6n]"
      by (((rule zenon_tuple_acc_2, safe, simp only: zenon_ss_1 zenon_ss_2,
            rule zenon_zero_lt,
            simp only: zenon_ss_1 zenon_ss_2 zenon_sa_1 zenon_sa_2,
            ((rule zenon_ss_le_sa_2)+)?, rule zenon_ss_le_sa_1
           )+)?,
          rule zenon_tuple_acc_1, auto)
      have hs: "s6x = ?rngs[?n6n]"
      by (((rule zenon_tuple_acc_2, safe, simp only: zenon_ss_1 zenon_ss_2,
            rule zenon_zero_lt,
            simp only: zenon_ss_1 zenon_ss_2 zenon_sa_1 zenon_sa_2,
            ((rule zenon_ss_le_sa_2)+)?, rule zenon_ss_le_sa_1
           )+)?,
          rule zenon_tuple_acc_1, auto)
      show "r[?doms[?n6n]] \\in ?rngs[?n6n]"
      by (rule subst[OF hs], rule subst[OF hn], rule h6)

    qed
  qed
qed

lemma zenon_inrecordsetI7 :
  fixes r l1x s1x l2x s2x l3x s3x l4x s4x l5x s5x l6x s6x l7x s7x
  assumes hfcn: "isAFcn (r)"
  assumes hdom: "DOMAIN r = {l1x, l2x, l3x, l4x, l5x, l6x, l7x}"
  assumes h1: "r[l1x] \\in s1x"
  assumes h2: "r[l2x] \\in s2x"
  assumes h3: "r[l3x] \\in s3x"
  assumes h4: "r[l4x] \\in s4x"
  assumes h5: "r[l5x] \\in s5x"
  assumes h6: "r[l6x] \\in s6x"
  assumes h7: "r[l7x] \\in s7x"
  shows "r \\in [l1x : s1x, l2x : s2x, l3x : s3x, l4x : s4x, l5x : s5x, l6x : s6x, l7x : s7x]"
proof -
  let ?doms = "<<l1x, l2x, l3x, l4x, l5x, l6x, l7x>>"
  let ?domset = "{l1x, l2x, l3x, l4x, l5x, l6x, l7x}"
  let ?domsetrev = "{l7x, l6x, l5x, l4x, l3x, l2x, l1x}"
  let ?rngs = "<<s1x, s2x, s3x, s4x, s5x, s6x, s7x>>"
  let ?n0n = "0"
  let ?n1n = "Succ[?n0n]"
  let ?n2n = "Succ[?n1n]"
  let ?n3n = "Succ[?n2n]"
  let ?n4n = "Succ[?n3n]"
  let ?n5n = "Succ[?n4n]"
  let ?n6n = "Succ[?n5n]"
  let ?n7n = "Succ[?n6n]"
  let ?indices = "{?n7n, ?n6n, ?n5n, ?n4n, ?n3n, ?n2n, ?n1n}"
  have hdomx : "?domsetrev = DOMAIN r"
  by (rule zenon_set_rev_1, (rule zenon_set_rev_2)+, rule zenon_set_rev_3,
      rule hdom)
  show "r \\in EnumFuncSet (?doms, ?rngs)"
  proof (rule EnumFuncSetI [of r, OF hfcn])
    have hx1: "isASeq (?doms) & ?domsetrev = Range (?doms)"
    by ((rule zenon_range_2)+, rule zenon_range_1)
    have hx2: "?domsetrev = Range (?doms)"
    by (rule conjD2 [OF hx1])
    show "DOMAIN r = Range (?doms)"
    by (rule subst [where P = "%x. x = Range (?doms)", OF hdomx hx2])
  next
    show "DOMAIN ?rngs = DOMAIN ?doms"
    by (rule zenon_tuple_dom_3, (rule zenon_tuple_dom_2)+,
        rule zenon_tuple_dom_1)
  next
    have hdomseq: "isASeq (?doms)" by auto
    have hindx: "isASeq (?doms) & ?n7n = Len (?doms)
                  & ?indices = DOMAIN ?doms"
    by (simp only: DomainSeqLen [OF hdomseq], (rule zenon_dom_app_2)+,
        rule zenon_dom_app_1)
    have hind: "?indices = DOMAIN ?doms" by (rule conjE [OF hindx], elim conjE)
    show "ALL i in DOMAIN ?doms : r[?doms[i]] \\in ?rngs[i]"
    proof (rule subst [OF hind], (rule zenon_all_rec_2)+, rule zenon_all_rec_1)

      have hn: "l1x = ?doms[?n1n]"
      by (((rule zenon_tuple_acc_2, safe, simp only: zenon_ss_1 zenon_ss_2,
            rule zenon_zero_lt,
            simp only: zenon_ss_1 zenon_ss_2 zenon_sa_1 zenon_sa_2,
            ((rule zenon_ss_le_sa_2)+)?, rule zenon_ss_le_sa_1
           )+)?,
          rule zenon_tuple_acc_1, auto)
      have hs: "s1x = ?rngs[?n1n]"
      by (((rule zenon_tuple_acc_2, safe, simp only: zenon_ss_1 zenon_ss_2,
            rule zenon_zero_lt,
            simp only: zenon_ss_1 zenon_ss_2 zenon_sa_1 zenon_sa_2,
            ((rule zenon_ss_le_sa_2)+)?, rule zenon_ss_le_sa_1
           )+)?,
          rule zenon_tuple_acc_1, auto)
      show "r[?doms[?n1n]] \\in ?rngs[?n1n]"
      by (rule subst[OF hs], rule subst[OF hn], rule h1)
    next
      have hn: "l2x = ?doms[?n2n]"
      by (((rule zenon_tuple_acc_2, safe, simp only: zenon_ss_1 zenon_ss_2,
            rule zenon_zero_lt,
            simp only: zenon_ss_1 zenon_ss_2 zenon_sa_1 zenon_sa_2,
            ((rule zenon_ss_le_sa_2)+)?, rule zenon_ss_le_sa_1
           )+)?,
          rule zenon_tuple_acc_1, auto)
      have hs: "s2x = ?rngs[?n2n]"
      by (((rule zenon_tuple_acc_2, safe, simp only: zenon_ss_1 zenon_ss_2,
            rule zenon_zero_lt,
            simp only: zenon_ss_1 zenon_ss_2 zenon_sa_1 zenon_sa_2,
            ((rule zenon_ss_le_sa_2)+)?, rule zenon_ss_le_sa_1
           )+)?,
          rule zenon_tuple_acc_1, auto)
      show "r[?doms[?n2n]] \\in ?rngs[?n2n]"
      by (rule subst[OF hs], rule subst[OF hn], rule h2)
    next
      have hn: "l3x = ?doms[?n3n]"
      by (((rule zenon_tuple_acc_2, safe, simp only: zenon_ss_1 zenon_ss_2,
            rule zenon_zero_lt,
            simp only: zenon_ss_1 zenon_ss_2 zenon_sa_1 zenon_sa_2,
            ((rule zenon_ss_le_sa_2)+)?, rule zenon_ss_le_sa_1
           )+)?,
          rule zenon_tuple_acc_1, auto)
      have hs: "s3x = ?rngs[?n3n]"
      by (((rule zenon_tuple_acc_2, safe, simp only: zenon_ss_1 zenon_ss_2,
            rule zenon_zero_lt,
            simp only: zenon_ss_1 zenon_ss_2 zenon_sa_1 zenon_sa_2,
            ((rule zenon_ss_le_sa_2)+)?, rule zenon_ss_le_sa_1
           )+)?,
          rule zenon_tuple_acc_1, auto)
      show "r[?doms[?n3n]] \\in ?rngs[?n3n]"
      by (rule subst[OF hs], rule subst[OF hn], rule h3)
    next
      have hn: "l4x = ?doms[?n4n]"
      by (((rule zenon_tuple_acc_2, safe, simp only: zenon_ss_1 zenon_ss_2,
            rule zenon_zero_lt,
            simp only: zenon_ss_1 zenon_ss_2 zenon_sa_1 zenon_sa_2,
            ((rule zenon_ss_le_sa_2)+)?, rule zenon_ss_le_sa_1
           )+)?,
          rule zenon_tuple_acc_1, auto)
      have hs: "s4x = ?rngs[?n4n]"
      by (((rule zenon_tuple_acc_2, safe, simp only: zenon_ss_1 zenon_ss_2,
            rule zenon_zero_lt,
            simp only: zenon_ss_1 zenon_ss_2 zenon_sa_1 zenon_sa_2,
            ((rule zenon_ss_le_sa_2)+)?, rule zenon_ss_le_sa_1
           )+)?,
          rule zenon_tuple_acc_1, auto)
      show "r[?doms[?n4n]] \\in ?rngs[?n4n]"
      by (rule subst[OF hs], rule subst[OF hn], rule h4)
    next
      have hn: "l5x = ?doms[?n5n]"
      by (((rule zenon_tuple_acc_2, safe, simp only: zenon_ss_1 zenon_ss_2,
            rule zenon_zero_lt,
            simp only: zenon_ss_1 zenon_ss_2 zenon_sa_1 zenon_sa_2,
            ((rule zenon_ss_le_sa_2)+)?, rule zenon_ss_le_sa_1
           )+)?,
          rule zenon_tuple_acc_1, auto)
      have hs: "s5x = ?rngs[?n5n]"
      by (((rule zenon_tuple_acc_2, safe, simp only: zenon_ss_1 zenon_ss_2,
            rule zenon_zero_lt,
            simp only: zenon_ss_1 zenon_ss_2 zenon_sa_1 zenon_sa_2,
            ((rule zenon_ss_le_sa_2)+)?, rule zenon_ss_le_sa_1
           )+)?,
          rule zenon_tuple_acc_1, auto)
      show "r[?doms[?n5n]] \\in ?rngs[?n5n]"
      by (rule subst[OF hs], rule subst[OF hn], rule h5)
    next
      have hn: "l6x = ?doms[?n6n]"
      by (((rule zenon_tuple_acc_2, safe, simp only: zenon_ss_1 zenon_ss_2,
            rule zenon_zero_lt,
            simp only: zenon_ss_1 zenon_ss_2 zenon_sa_1 zenon_sa_2,
            ((rule zenon_ss_le_sa_2)+)?, rule zenon_ss_le_sa_1
           )+)?,
          rule zenon_tuple_acc_1, auto)
      have hs: "s6x = ?rngs[?n6n]"
      by (((rule zenon_tuple_acc_2, safe, simp only: zenon_ss_1 zenon_ss_2,
            rule zenon_zero_lt,
            simp only: zenon_ss_1 zenon_ss_2 zenon_sa_1 zenon_sa_2,
            ((rule zenon_ss_le_sa_2)+)?, rule zenon_ss_le_sa_1
           )+)?,
          rule zenon_tuple_acc_1, auto)
      show "r[?doms[?n6n]] \\in ?rngs[?n6n]"
      by (rule subst[OF hs], rule subst[OF hn], rule h6)
    next
      have hn: "l7x = ?doms[?n7n]"
      by (((rule zenon_tuple_acc_2, safe, simp only: zenon_ss_1 zenon_ss_2,
            rule zenon_zero_lt,
            simp only: zenon_ss_1 zenon_ss_2 zenon_sa_1 zenon_sa_2,
            ((rule zenon_ss_le_sa_2)+)?, rule zenon_ss_le_sa_1
           )+)?,
          rule zenon_tuple_acc_1, auto)
      have hs: "s7x = ?rngs[?n7n]"
      by (((rule zenon_tuple_acc_2, safe, simp only: zenon_ss_1 zenon_ss_2,
            rule zenon_zero_lt,
            simp only: zenon_ss_1 zenon_ss_2 zenon_sa_1 zenon_sa_2,
            ((rule zenon_ss_le_sa_2)+)?, rule zenon_ss_le_sa_1
           )+)?,
          rule zenon_tuple_acc_1, auto)
      show "r[?doms[?n7n]] \\in ?rngs[?n7n]"
      by (rule subst[OF hs], rule subst[OF hn], rule h7)

    qed
  qed
qed

(*** END AUTO_GENERATED STUFF ***)

(* ------------- Proof rules for CASE expressions ------ *)

lemma zenon_caseother0 :
  "P (CASE OTHER -> e0) ==> (P (e0) ==> FALSE) ==> FALSE"
proof -
  fix P e0
  assume h: "P (CASE OTHER -> e0)"
  def cas == "CASE OTHER -> e0"
  have hh: "P (cas)" using h by (fold cas_def)
  assume hoth: "P (e0) ==> FALSE"
  have hb: "(\<forall> i \<in> DOMAIN <<>> : ~<<>>[i]) = TRUE" by auto
  have hc: "cas = e0" using hb by (unfold cas_def, auto)
  have hg: "P (e0)" using hh by (rule subst [OF hc])
  show FALSE
  by (rule hoth [OF hg])
qed

(* support lemmas for the generic proof rules *)

lemma zenon_disjE1 :
  assumes h1: "A | B"
  assumes h2: "A => FALSE"
  shows "B"
using h1 h2 by blast

definition zenon_seqify where
"zenon_seqify (x) \<equiv> IF isASeq (x) THEN x ELSE <<>>"

definition zenon_appseq where
"zenon_appseq (xs, x) \<equiv> Append (zenon_seqify (xs), x)"

lemma zenon_seqifyIsASeq :
  fixes x
  shows "isASeq (zenon_seqify (x))"
by (simp only: zenon_seqify_def, rule condI, auto)

lemma zenon_isASeqSeqify :
  fixes x
  assumes h: "isASeq (x)"
  shows "zenon_seqify (x) = x"
using h by (simp only: zenon_seqify_def, auto)

lemma zenon_seqify_appseq :
  fixes cs c
  shows "zenon_seqify (zenon_appseq (cs, c)) = Append (zenon_seqify (cs), c)"
by (simp only: zenon_appseq_def, rule zenon_isASeqSeqify, rule appendIsASeq,
    rule zenon_seqifyIsASeq)

lemma zenon_seqify_empty :
  shows "zenon_seqify (<<>>) = <<>>"
using zenon_seqify_def by auto

lemma zenon_case_seq_simpl :
  fixes cs c
  shows "(\<exists> i \<in> DOMAIN zenon_seqify (zenon_appseq (cs, c))
          : zenon_seqify (zenon_appseq (cs, c))[i])
         = (c | (\<exists> i \<in> DOMAIN zenon_seqify (cs)
                 : zenon_seqify (cs)[i]))"
proof (rule boolEqual, simp only: zenon_seqify_appseq, rule iffI)
  have h6: "isASeq (zenon_seqify (cs))" using zenon_seqifyIsASeq by auto
  assume h1: "\<exists> i \<in> DOMAIN Append (zenon_seqify (cs), c)
              : Append (zenon_seqify (cs), c)[i]"
  show "c | (\<exists> i \<in> DOMAIN zenon_seqify (cs) : zenon_seqify (cs)[i])"
  proof
    assume h4: "~ c"
    with h1 h6 obtain i
      where i: "i \<in> DOMAIN zenon_seqify(cs)" "Append(zenon_seqify(cs), c)[i]"
      by auto
    with h6 have "zenon_seqify(cs)[i]" by (auto simp: leq_neq_iff_less[simplified])
    with i show "\<exists> i \<in> DOMAIN zenon_seqify (cs) : zenon_seqify (cs)[i]" by blast
  qed
next
  have h0: "isASeq (zenon_seqify (cs))" using zenon_seqifyIsASeq by auto
  assume h1: "c | (\<exists> i \<in> DOMAIN zenon_seqify (cs)
                   : zenon_seqify (cs)[i])"
  show "\<exists> i \<in> DOMAIN Append (zenon_seqify (cs), c)
        : Append (zenon_seqify (cs), c)[i]" (is "?g")
  proof (rule disjE [OF h1])
    assume h2: c
    show "?g"
    using h2 h0 by auto
  next
    assume h2: "\<exists> i \<in> DOMAIN zenon_seqify (cs)
                : zenon_seqify (cs)[i]"
    show "?g"
    proof (rule bExE [OF h2])
      fix i
      assume h3: "i \\in DOMAIN zenon_seqify (cs)"
      have h4: "i \\in DOMAIN Append (zenon_seqify (cs), c)"
        using h0 h3 by auto
      assume h5: "zenon_seqify (cs)[i]"
      have h6: "i ~= Succ[Len (zenon_seqify (cs))]"
        using h0 h3 by auto
      have h7: "Append (zenon_seqify (cs), c)[i]"
        using h6 h5 h3 h0 by force
      show "?g"
        using h4 h7 by auto
    qed
  qed
qed (simp_all)

lemma zenon_case_seq_empty :
  assumes h0: "\<exists> i \<in> DOMAIN zenon_seqify (<<>>)
               : zenon_seqify (<<>>)[i]"
  shows FALSE
using zenon_seqify_empty h0 by auto

lemma zenon_case_domain :
  fixes cs es
  assumes h0: "\<exists> i \<in> DOMAIN cs : cs[i]"
  shows "\<exists> x : x \<in> UNION {CaseArm (cs[i], es[i]) : i \\in DOMAIN cs}"
        (is "?g")
proof (rule bExE [OF h0])
  fix i
  assume h1: "i \\in DOMAIN cs"
  assume h2: "cs[i]"
  show "?g"
    using h1 h2 by auto
qed

lemma zenon_case_append1 :
  fixes s x i
  assumes h1: "isASeq (s)"
  assumes h2: "i \\in DOMAIN s"
  shows "Append (s, x)[i] = s[i]"
using assms by force

lemma zenon_case_len_domain :
  fixes cs es
  assumes h1: "Len (zenon_seqify (cs)) = Len (zenon_seqify (es))"
  shows "DOMAIN zenon_seqify (cs) = DOMAIN zenon_seqify (es)"
using h1 zenon_seqifyIsASeq DomainSeqLen by auto

lemma zenon_case_union_split :
  fixes cs c es e x
  assumes h1: "x \\in UNION {CaseArm (Append (zenon_seqify (cs), c)[i],
                                      Append (zenon_seqify (es), e)[i])
                             : i \\in DOMAIN Append (zenon_seqify (cs), c)}"
  assumes h2: "Len (zenon_seqify (cs)) = Len (zenon_seqify (es))"
  shows "x \\in CaseArm (c, e)
         | x \\in UNION {CaseArm (zenon_seqify (cs)[i], zenon_seqify (es)[i])
                         : i \\in DOMAIN zenon_seqify (cs)}"
proof
  have h3c: "isASeq (zenon_seqify (cs))" using zenon_seqifyIsASeq by auto
  have h3e: "isASeq (zenon_seqify (es))" using zenon_seqifyIsASeq by auto
  assume h4: "~ (x \\in CaseArm (c, e))"
  have h5: "\<exists> i \<in> DOMAIN Append (zenon_seqify (cs), c)
            : x \\in CaseArm (Append (zenon_seqify (cs), c)[i],
                              Append (zenon_seqify (es), e)[i])"
    using h1 by auto
  show "x \\in UNION {CaseArm (zenon_seqify (cs)[i], zenon_seqify (es)[i])
                      : i \\in DOMAIN zenon_seqify (cs)}"
       (is "?g1")
  proof (rule bExE [OF h5])
    fix i
    assume h6: "i \\in DOMAIN Append (zenon_seqify(cs), c)"
    have h7: "i = Succ [Len (zenon_seqify (cs))]
              | i \\in DOMAIN (zenon_seqify (cs))"
      using h3c h6 by auto
    assume h8: "x \\in CaseArm (Append (zenon_seqify (cs), c)[i],
                                Append (zenon_seqify (es), e)[i])"
    have h9: "i \\in DOMAIN (zenon_seqify (cs))" (is "?g")
    proof (rule disjE [OF h7])
      assume h10: "i = Succ [Len (zenon_seqify (cs))]"
      have h11: FALSE using h8 h10 h4 h3c h3e h2 by auto
      show "?g" using h11 by auto
    next
      assume "?g" thus "?g" by auto
    qed
    have h10: "i \\in DOMAIN (zenon_seqify (es))"
      using h9 h2 h3c h3e DomainSeqLen by auto
    have h11: "x \\in CaseArm (zenon_seqify (cs)[i], zenon_seqify (es)[i])"
    using h8 h9 h3c h3e h10 zenon_case_append1 by auto
    show "?g1" using h11 h9 by auto
  qed
qed

lemma zenon_case_union_simpl :
  fixes cs c es e x
  shows "(Len (zenon_seqify (zenon_appseq (cs, c)))
          = Len (zenon_seqify (zenon_appseq (es, e)))
          & x \\in UNION {CaseArm (zenon_seqify (zenon_appseq (cs, c))[i],
                                   zenon_seqify (zenon_appseq (es, e))[i])
                          : i \\in DOMAIN zenon_seqify (zenon_appseq (cs, c))})
         = (  Len (zenon_seqify (zenon_appseq (cs, c)))
              = Len (zenon_seqify (zenon_appseq (es, e)))
              & x \\in CaseArm (c, e)
            | Len (zenon_seqify (cs)) = Len (zenon_seqify (es))
              & x \\in UNION {CaseArm (zenon_seqify (cs)[i],
                                       zenon_seqify (es)[i])
                              : i \\in DOMAIN zenon_seqify (cs)})"
proof (rule boolEqual, simp only: zenon_seqify_appseq, rule iffI)
  assume h1: "Len (Append (zenon_seqify (cs), c))
              = Len (Append (zenon_seqify (es), e))
              & x \\in UNION {CaseArm (Append (zenon_seqify (cs), c)[i],
                                       Append (zenon_seqify (es), e)[i])
                              : i \\in DOMAIN Append (zenon_seqify (cs), c)}"
  have h1a: "Len (Append (zenon_seqify (cs), c))
             = Len (Append (zenon_seqify (es), e))"
    using h1 by blast
  have h1b: "x \\in UNION {CaseArm (Append (zenon_seqify (cs), c)[i],
                                    Append (zenon_seqify (es), e)[i])
                           : i \\in DOMAIN Append (zenon_seqify (cs), c)}"
    using h1 by blast
  show "  Len (Append (zenon_seqify (cs), c))
          = Len (Append (zenon_seqify (es), e))
          & x \\in CaseArm (c, e)
        | Len (zenon_seqify (cs)) = Len (zenon_seqify (es))
          & x \\in UNION {CaseArm (zenon_seqify (cs)[i], zenon_seqify (es)[i])
                          : i \\in DOMAIN zenon_seqify (cs)}"
  proof
    assume h2: "~(Len (Append (zenon_seqify (cs), c))
                  = Len (Append (zenon_seqify (es), e))
                  & x \\in CaseArm (c, e))"
    have h3: "Len (zenon_seqify (cs)) = Len (zenon_seqify (es))" (is "?g3")
      using h1a zenon_seqifyIsASeq by auto
    have h4: "~(x \\in CaseArm (c, e))"
      using h2 h1a by blast
    have h5: "x \\in UNION {CaseArm (zenon_seqify (cs)[i], zenon_seqify (es)[i])
                            : i \\in DOMAIN zenon_seqify (cs)}" (is "?g5")
      using zenon_case_union_split [OF h1b h3] h4 by auto
    show "?g3 & ?g5" using h3 h5 by blast
  qed
next
  assume h1: "  Len (Append (zenon_seqify (cs), c))
                = Len (Append (zenon_seqify (es), e))
                & x \\in CaseArm (c, e)
              | Len (zenon_seqify (cs)) = Len (zenon_seqify (es))
                & x \\in UNION {CaseArm (zenon_seqify (cs)[i],
                                         zenon_seqify (es)[i])
                                : i \\in DOMAIN zenon_seqify (cs)}"
  show "Len (Append (zenon_seqify (cs), c))
        = Len (Append (zenon_seqify (es), e))
        & x \\in UNION {CaseArm (Append (zenon_seqify (cs), c)[i],
                                 Append (zenon_seqify (es), e)[i])
                        : i \\in DOMAIN Append (zenon_seqify (cs), c)}"
        (is "?g")
  proof (rule disjE [OF h1])
    assume h2: "Len (Append (zenon_seqify (cs), c))
                = Len (Append (zenon_seqify (es), e))
                & x \\in CaseArm (c, e)"
    have h4: "Len (Append (zenon_seqify (cs), c))
              = Len (Append (zenon_seqify (es), e))"
      using h2 by blast
    have h3: "Len (zenon_seqify (cs)) = Len (zenon_seqify (es))"
      using h4 zenon_seqifyIsASeq by auto
    have h5: "x \\in CaseArm (c, e)"
      using h2 by blast
    have h6: "x \\in UNION {CaseArm (Append (zenon_seqify (cs), c)[i],
                                     Append (zenon_seqify (es), e)[i])
                            : i \\in DOMAIN Append (zenon_seqify (cs), c)}"
      using h5 zenon_seqifyIsASeq appendElt2 h3 by auto
    show "?g"
      using h4 h6 by auto
  next
    assume h2: "Len (zenon_seqify (cs)) = Len (zenon_seqify (es))
                & x \\in UNION {CaseArm (zenon_seqify (cs)[i],
                                         zenon_seqify (es)[i])
                                : i \\in DOMAIN zenon_seqify (cs)}"
    have h3: "Len (zenon_seqify (cs)) = Len (zenon_seqify (es))"
      using h2 by blast
    have h4: "Len (Append (zenon_seqify (cs), c))
              = Len (Append (zenon_seqify (es), e))"
      using h3 zenon_seqifyIsASeq by auto
    have h5: "x \\in UNION {CaseArm (zenon_seqify (cs)[i],
                                     zenon_seqify (es)[i])
                            : i \\in DOMAIN zenon_seqify (cs)}"
      using h2 by blast
    have h6: "\<exists> i \<in> DOMAIN zenon_seqify (cs)
              : x \\in CaseArm (zenon_seqify (cs)[i], zenon_seqify (es)[i])"
    using h5 by auto
    have h7: "x \\in UNION {CaseArm (Append (zenon_seqify (cs), c)[i],
                                     Append (zenon_seqify (es), e)[i])
                            : i \\in DOMAIN Append (zenon_seqify (cs), c)}"
             (is "?g7")
    proof (rule bExE [OF h6])
      fix i
      assume h8: "i \\in DOMAIN zenon_seqify (cs)"
      have h9: "i \\in DOMAIN zenon_seqify (es)"
        using h8 zenon_case_len_domain [OF h3] by auto
      have h10: "i \\in DOMAIN Append (zenon_seqify (cs), c)"
      using h8 zenon_seqifyIsASeq by auto
      assume h11: "x \\in CaseArm (zenon_seqify (cs)[i], zenon_seqify (es)[i])"
      have h12: "x \\in CaseArm (Append (zenon_seqify (cs), c)[i],
                                 Append (zenon_seqify (es), e)[i])"
                (is "?g12")
        using h11 zenon_case_append1 [OF _ h8] zenon_case_append1 [OF _ h9]
              zenon_seqifyIsASeq
        by auto
      show "?g7"
      proof
        show "?g12" by (rule h12)
      next
        show "CaseArm (Append (zenon_seqify (cs), c) [i],
                       Append (zenon_seqify (es), e) [i])
              \\in {CaseArm (Append (zenon_seqify (cs), c)[i],
                             Append (zenon_seqify (es), e)[i])
                    : i \\in DOMAIN Append (zenon_seqify (cs), c)}"
          using h10 by auto
      qed
    qed
    show "?g" using h4 h7 by blast
  qed
qed (simp_all)

lemma zenon_case_len_simpl :
  fixes cs c es e
  shows "(Len (zenon_seqify (zenon_appseq (cs, c)))
          = Len (zenon_seqify (zenon_appseq (es, e))))
         = (Len (zenon_seqify (cs)) = Len (zenon_seqify (es)))"
proof (rule boolEqual, simp only: zenon_seqify_appseq, rule iffI)
  assume h1: "Len (Append (zenon_seqify (cs), c))
              = Len (Append (zenon_seqify (es), e))"
  show "Len (zenon_seqify (cs)) = Len (zenon_seqify (es))"
    using h1 zenon_seqifyIsASeq by auto
next
  assume h1: "Len (zenon_seqify (cs)) = Len (zenon_seqify (es))"
  show "Len (Append (zenon_seqify (cs), c))
        = Len (Append (zenon_seqify (es), e))"
    using h1 zenon_seqifyIsASeq by auto
qed (simp_all)

lemma zenon_case_empty_union :
  fixes x
  assumes h: "x \\in UNION {CaseArm (<<>>[i], <<>>[i]) : i \\in DOMAIN <<>>}"
  shows "FALSE"
using h by auto

lemma zenon_case_oth_simpl_l1 :
  fixes cs c
  assumes g0 : "~c"
  shows "(\<forall> i \<in> DOMAIN Append(zenon_seqify(cs), c)
          : ~ Append(zenon_seqify(cs), c)[i])
         = (\<forall> i \<in> DOMAIN zenon_seqify(cs)
            : ~ zenon_seqify(cs)[i])"
        (is "?f1 = ?f2")
proof (rule boolEqual, rule iffI)
  assume h6: "?f1"
  show "?f2"
  proof
    fix i
    assume h7: "i \\in DOMAIN zenon_seqify (cs)"
    have h8: "i \\in DOMAIN Append (zenon_seqify (cs), c)"
      using h7 zenon_seqifyIsASeq by auto
    have h9: "zenon_seqify (cs) [i] = Append (zenon_seqify (cs), c)[i]"
      using zenon_case_append1 zenon_seqifyIsASeq h7 by auto
    show "~ zenon_seqify(cs)[i]"
      using h9 h8 h6 by auto
  qed
next
  assume h6: "?f2"
  show "?f1"
  proof
    fix i
    assume h7: "i \\in DOMAIN Append (zenon_seqify (cs), c)"
    show "~Append (zenon_seqify (cs), c)[i]"
      using g0 h7 h6 zenon_seqifyIsASeq by (unfold Append_def, auto)
  qed
qed (simp_all)

lemma zenon_case_oth_simpl_l2 :
  fixes cs c es e
  assumes g0: "~c"
  assumes g2: "Len(zenon_seqify(cs)) = Len(zenon_seqify(es))"
  shows "UNION {CaseArm
            (Append(zenon_seqify(cs), c)[i],
             Append
              (zenon_seqify(es),
               e)[i]) : i \\in DOMAIN Append(zenon_seqify(cs), c)}
            = UNION {CaseArm
                (zenon_seqify(cs)[i],
                 zenon_seqify(es)[i]) : i \\in DOMAIN zenon_seqify(cs)}"
           (is "?u1 = ?u2")
proof
  fix x
  assume h6: "x \\in ?u1"
  show "x \\in ?u2"
  proof (rule UNIONE [OF h6])
    fix B
    assume h7: "x \\in B"
    assume h8: "B \\in {CaseArm
          (Append(zenon_seqify(cs), c)[i],
           Append
            (zenon_seqify(es),
             e)[i]) : i \\in DOMAIN Append(zenon_seqify(cs), c)}"
    show "x \\in ?u2"
    proof (rule setOfAllE [OF h8])
      fix i
      assume h9: "i \\in DOMAIN Append (zenon_seqify (cs), c)"
      assume h10: "CaseArm (Append (zenon_seqify (cs), c)[i],
                            Append (zenon_seqify (es), e)[i]) = B"
      have h11: "i = Succ[Len (zenon_seqify (cs))] ==> FALSE"
      proof -
        assume h12: "i = Succ[Len (zenon_seqify (cs))]"
        have h13: "B = CaseArm (c, e)"
          using h10 h12 g0 appendElt2 zenon_seqifyIsASeq by auto
        show FALSE
          using h7 h13 g0 by auto
      qed
      have h12: "Append (zenon_seqify (cs), c)[i] = zenon_seqify (cs)[i]"
        using h11 zenon_seqifyIsASeq[of "cs"] h9 by force
      have h13: "Append (zenon_seqify (es), e)[i] = zenon_seqify (es)[i]"
        using h11 zenon_seqifyIsASeq[of "es"] h9 g2 by force
      show "x \\in ?u2"
      proof
        show "x \\in B" by (rule h7)
      next
        have h14: "i \\in DOMAIN zenon_seqify (cs)"
          using h9 zenon_seqifyIsASeq h11 by auto
        show "B \\in {CaseArm (zenon_seqify(cs)[i],
                               zenon_seqify(es)[i]) :
                      i \\in DOMAIN zenon_seqify(cs)}"
          using h10 h12 h13 h14 by auto
      qed
    qed
  qed
next
  fix x
  assume h6: "x \\in ?u2"
  show "x \\in ?u1"
  proof (rule UNIONE [OF h6])
    fix B
    assume h7: "x \\in B"
    assume h8: "B \\in {CaseArm (zenon_seqify (cs)[i],
                                 zenon_seqify (es)[i])
                        : i \\in DOMAIN zenon_seqify (cs)}"
    show "x \\in ?u1"
    proof (rule setOfAllE [OF h8])
      fix i
      assume h9: "i \\in DOMAIN zenon_seqify (cs)"
      assume h10: "CaseArm (zenon_seqify (cs)[i], zenon_seqify (es)[i]) = B"
      show "x \\in ?u1"
      proof
        show "x \\in B" by (rule h7)
      next
        show "B \\in {CaseArm (Append(zenon_seqify(cs), c)[i],
                               Append(zenon_seqify(es), e)[i])
                      : i \\in DOMAIN Append(zenon_seqify(cs), c)}"
        proof
          show "i \\in DOMAIN Append (zenon_seqify (cs), c)"
            using h9 zenon_seqifyIsASeq by auto
        next
          have h11: "Append (zenon_seqify (cs), c)[i] = zenon_seqify (cs)[i]"
            using zenon_seqifyIsASeq zenon_case_append1 [OF _ h9] by auto
          have h12: "i \\in DOMAIN zenon_seqify (es)"
            using h9 zenon_case_len_domain [OF g2] by auto
          have h13: "Append (zenon_seqify (es), e)[i] = zenon_seqify (es)[i]"
            using zenon_seqifyIsASeq zenon_case_append1 [OF _ h12] g2
                  zenon_case_len_domain
            by auto
          show "B = CaseArm (Append (zenon_seqify (cs), c)[i],
                             Append (zenon_seqify (es), e)[i])"
            using h11 h13 h10 by auto
        qed
      qed
    qed
  qed
qed

lemma zenon_case_oth_simpl :
  fixes cs c es e x dcs oth
  shows "(~ (c | dcs)
          & Len (zenon_seqify (zenon_appseq (cs, c)))
            = Len (zenon_seqify (zenon_appseq (es, e)))
          & x = UNION {CaseArm (zenon_seqify (zenon_appseq (cs, c))[i],
                                zenon_seqify (zenon_appseq (es, e))[i])
                       : i \\in DOMAIN zenon_seqify (zenon_appseq (cs, c))}
                \\cup CaseArm (\<forall> i \<in> DOMAIN zenon_seqify
                                                          (zenon_appseq (cs, c))
                               : ~zenon_seqify (zenon_appseq (cs, c))[i],
                               oth))
         = (~c
            & (~dcs
               & Len (zenon_seqify (cs)) = Len (zenon_seqify (es))
               & x = UNION {CaseArm (zenon_seqify (cs)[i], zenon_seqify (es)[i])
                            : i \\in DOMAIN zenon_seqify (cs)}
                     \\cup CaseArm (\<forall> i \<in> DOMAIN zenon_seqify (cs)
                                    : ~zenon_seqify(cs)[i],
                                    oth)))"
proof (rule boolEqual, simp only: zenon_seqify_appseq, rule iffI)
  assume h0: "~ (c | dcs)
              & Len(Append(zenon_seqify(cs), c))
                = Len(Append(zenon_seqify(es), e))
              & x = UNION {CaseArm (Append (zenon_seqify (cs), c)[i],
                                    Append (zenon_seqify (es), e)[i])
                           : i \\in DOMAIN Append(zenon_seqify(cs), c)}
                    \\cup CaseArm (\<forall> i \<in> DOMAIN Append (zenon_seqify
                                                                           (cs),
                                                                    c)
                                   : ~ Append(zenon_seqify(cs), c)[i],
                                   oth)"
             (is "?h1 & ?h2 & ?h3")
  have h1: "?h1" using h0 by blast
  have h2: "?h2" using h0 by blast
  have h3: "?h3" using h0 by blast
  have g0: "~c" (is "?g0") using h1 by blast
  have g1: "~dcs" (is "?g1") using h1 by blast
  have g2: "Len(zenon_seqify(cs)) = Len(zenon_seqify(es))" (is "?g2")
    using h2 zenon_seqifyIsASeq by auto
  have g3: "x = UNION {CaseArm (zenon_seqify(cs)[i],
                                zenon_seqify(es)[i])
                       : i \\in DOMAIN zenon_seqify(cs)}
                \\cup CaseArm (\<forall> i \<in> DOMAIN zenon_seqify(cs)
                               : ~ zenon_seqify(cs)[i],
                               oth)"
           (is "?g3")
    using h3 zenon_case_oth_simpl_l1 [OF g0] zenon_case_oth_simpl_l2 [OF g0 g2]
    by auto
  show "?g0 & ?g1 & ?g2 & ?g3"
    using g0 g1 g2 g3 by blast
next
  assume h: "~c
             & ~dcs
             & Len (zenon_seqify (cs)) = Len (zenon_seqify (es))
             & x = UNION {CaseArm (zenon_seqify (cs)[i], zenon_seqify (es)[i])
                          : i \\in DOMAIN zenon_seqify (cs)}
                   \\cup CaseArm (\<forall> i \<in> DOMAIN zenon_seqify (cs)
                                  : ~zenon_seqify (cs)[i],
                                  oth)"
            (is "?h0 & ?h1 & ?h2 & ?h3")
  have h0: "?h0" using h by blast
  have h1: "?h1" using h by blast
  have h2: "?h2" using h by blast
  have h3: "?h3" using h by blast
  have g1: "~(c | dcs)" (is "?g1") using h0 h1 by blast
  have g2: "Len (Append (zenon_seqify (cs), c))
            = Len (Append (zenon_seqify (es), e))"
           (is "?g2")
    using h2 zenon_seqifyIsASeq by auto
  have g3: "x = UNION {CaseArm (Append (zenon_seqify (cs), c)[i],
                                Append (zenon_seqify (es), e)[i])
                       : i \\in DOMAIN Append(zenon_seqify(cs), c)}
            \\cup CaseArm (\<forall> i \<in> DOMAIN Append(zenon_seqify(cs), c)
                           : ~ Append(zenon_seqify(cs), c)[i],
                           oth)"
           (is "?g3")
   using h3 zenon_case_oth_simpl_l1 [OF h0] zenon_case_oth_simpl_l2 [OF h0 h2]
   by auto
  show "?g1 & ?g2 & ?g3"
    using g1 g2 g3 by blast
qed (simp_all)

lemma zenon_case_oth_empty :
  fixes x
  shows "(x = UNION {CaseArm (zenon_seqify (<<>>)[i], zenon_seqify (<<>>)[i])
                     : i \\in DOMAIN zenon_seqify (<<>>)}
              \\cup CaseArm (\<forall> i \<in> DOMAIN zenon_seqify (<<>>)
                             : ~zenon_seqify(<<>>)[i],
                             oth))
         = (x = {oth})"
by (rule boolEqual, simp only: zenon_seqify_empty, rule iffI, auto)

(* generic proof rules instantiated for small n *)

(*** BEGIN AUTO-GENERATED STUFF ***)

lemma zenon_case1 :
  fixes P c1x e1x
  assumes h: "P (CASE c1x -> e1x)"
             (is "P (?cas)")
  assumes h1: "c1x ==> P (e1x) ==> FALSE"

  assumes hoth: "~c1x & TRUE ==> FALSE"
  shows FALSE
proof -
  def cs == "<<c1x>>" (is "?cs")
  def es == "<<e1x>>" (is "?es")
  def arms == "UNION {CaseArm (?cs[i], ?es[i]) : i \\in DOMAIN ?cs}"
              (is "?arms")
  def cas == "?cas"
  have h0: "P (cas)" using h by (fold cas_def)
  def dcs == "c1x" (is "?dcs")
  show FALSE
  proof (rule zenon_em [of "?dcs"])
    assume ha: "~(?dcs)"
    have hh1: "~c1x" using ha by blast

    show FALSE
      using hoth hh1 by blast
  next
    assume ha: "?dcs"
    def scs == "zenon_seqify (zenon_appseq (
                               <<>>, c1x))"
               (is "?scs")
    def ses == "zenon_seqify (zenon_appseq (
                               <<>>, e1x))"
               (is "?ses")
    have ha1: "\<exists> i \<in> DOMAIN ?scs : ?scs[i]"
      using ha zenon_case_seq_empty
      by (simp only: zenon_case_seq_simpl zenon_seqify_empty, blast)
    have ha2: "\<exists> i \<in> DOMAIN ?cs : ?cs[i]"
      using ha1 by (simp only: zenon_seqify_appseq zenon_seqify_empty)
    have hb: "\\E x : x \\in arms"
      using zenon_case_domain [OF ha2, where es = "?es"]
      by (unfold arms_def, blast)
    have hc: "(CHOOSE x : x \\in arms) \\in arms"
      using hb by (unfold Ex_def, auto)
    have hf0: "?cas \\in arms"
      using hc by (unfold arms_def, fold Case_def)
    have hf3: "cas \\in UNION {CaseArm (?scs[i], ?ses[i])
                                  : i \\in DOMAIN ?scs}"
              (is "?hf3")
      using hf0 by (fold cas_def, unfold arms_def,
                    simp only: zenon_seqify_appseq zenon_seqify_empty)
    have hf4: "Len (?scs) = Len (?ses)" (is "?hf4")
      by (simp only: zenon_case_len_simpl)
    have hf5: "?hf4 & ?hf3"
      by (rule conjI [OF hf4 hf3])
    have hf: "
               cas \\in CaseArm (c1x, e1x)
             | cas \\in UNION {CaseArm (zenon_seqify (<<>>)[i],
                                          zenon_seqify (<<>>)[i])
                                 : i \\in DOMAIN zenon_seqify (<<>>)}
             " (is "_ | ?gxx")
      using hf5 by (simp only: zenon_case_union_simpl, blast)
    have hg1x: "cas \\in CaseArm (c1x, e1x) => FALSE"
      using h0 h1 by auto

    from hf
    have hh0: "?gxx"
      by (rule zenon_disjE1 [OF _ hg1x])
    have hi: "cas \\in UNION {CaseArm (<<>>[i], <<>>[i])
                                 : i \\in DOMAIN <<>>}"
      using hh0 by (simp only: zenon_seqify_empty)
    show FALSE
      by (rule zenon_case_empty_union [OF hi])
  qed
qed

lemma zenon_caseother1 :
  fixes P oth c1x e1x
  assumes h: "P (CASE c1x -> e1x
                  [] OTHER -> oth)"
             (is "P (?cas)")
  assumes h1: "c1x ==> P (e1x) ==> FALSE"

  assumes hoth: "~c1x & TRUE ==> P (oth) ==> FALSE"
  shows FALSE
proof -
  def cs == "<<c1x>>" (is "?cs")
  def es == "<<e1x>>" (is "?es")
  def arms == "UNION {CaseArm (?cs[i], ?es[i]) : i \\in DOMAIN ?cs}"
              (is "?arms")
  def cas == "?cas"
  have h0: "P (cas)" using h by (fold cas_def)
  def dcs == "c1x | FALSE" (is "?dcs")
  def scs == "zenon_seqify (zenon_appseq (
                             <<>>, c1x))"
             (is "?scs")
  have hscs : "?cs = ?scs"
    by (simp only: zenon_seqify_appseq zenon_seqify_empty)
  def ses == "zenon_seqify (zenon_appseq (
                             <<>>, e1x))"
             (is "?ses")
  have hses : "?es = ?ses"
    by (simp only: zenon_seqify_appseq zenon_seqify_empty)
  have hlen: "Len (?scs) = Len (?ses)" (is "?hlen")
    by (simp only: zenon_case_len_simpl)
  def armoth == "CaseArm (\<forall> i \<in> DOMAIN ?cs : ~?cs[i], oth)"
                (is "?armoth")
  show FALSE
  proof (rule zenon_em [of "?dcs"])
    assume ha: "~(?dcs)"
    have hb: "P (CHOOSE x : x \\in arms \<union> armoth)"
      using h by (unfold CaseOther_def, fold arms_def armoth_def)
    have hc: "arms \\cup armoth
              = UNION {CaseArm (?scs[i], ?ses[i]) : i \\in DOMAIN ?scs}
                \\cup CaseArm (\<forall> i \<in> DOMAIN ?scs : ~?scs[i],
                                 oth)"
             (is "_ = ?sarmsoth")
      using hscs hses by (unfold arms_def armoth_def, auto)
    have hd: "~(?dcs) & ?hlen & arms \<union> armoth = ?sarmsoth"
      using ha hlen hc by blast
    have he: "arms \<union> armoth = {oth}"
      using hd by (simp only: zenon_case_oth_simpl zenon_case_oth_empty)
    have hf: "(CHOOSE x : x \\in arms \\cup armoth) = oth"
      using he by auto
    have hg: "P (oth)"
      using hb hf by auto
    have hh1: "~c1x" using ha by blast

    show FALSE
      using hg hoth hh1 by blast
  next
    assume ha: "?dcs"
    have ha1: "\<exists> i \<in> DOMAIN ?scs : ?scs[i]"
      using ha zenon_case_seq_empty
      by (simp only: zenon_case_seq_simpl zenon_seqify_empty, blast)
    have ha2: "\<exists> i \<in> DOMAIN ?cs : ?cs[i]"
      using ha1 hscs by auto
    have ha3: "~ (\<forall> i \<in> DOMAIN ?cs : ~?cs[i])"
      using ha2 by blast
    have ha4: "armoth = {}"
      using ha3 condElse [OF ha3, where t = "{oth}" and e = "{}"]
      by (unfold armoth_def CaseArm_def, blast)
    have hb: "\\E x : x \\in arms \\cup armoth"
      using zenon_case_domain [OF ha2, where es = "?es"]
      by (unfold arms_def, blast)
    have hc: "(CHOOSE x : x \\in arms \\cup armoth)
               \\in arms \\cup armoth"
      using hb by (unfold Ex_def, auto)
    have hf0: "?cas \\in arms \\cup armoth"
      using hc by (unfold arms_def armoth_def, fold CaseOther_def)
    have hf1: "cas \\in arms \\cup armoth"
      using hf0 by (fold cas_def)
    have hf2: "cas \\in arms"
      using hf1 ha4 by auto
    have hf3: "cas \\in UNION {CaseArm (?scs[i], ?ses[i])
                                  : i \\in DOMAIN ?scs}"
              (is "?hf3")
      using hf2 by (unfold arms_def,
                    simp only: zenon_seqify_appseq zenon_seqify_empty)
    have hf5: "?hlen & ?hf3"
      by (rule conjI [OF hlen hf3])
    have hf: "
               cas \\in CaseArm (c1x, e1x)
             | cas \\in UNION {CaseArm (zenon_seqify (<<>>)[i],
                                          zenon_seqify (<<>>)[i])
                                 : i \\in DOMAIN zenon_seqify (<<>>)}
             " (is "_ | ?gxx")
      using hf5 by (simp only: zenon_case_union_simpl, blast)
    have hg1x: "cas \\in CaseArm (c1x, e1x) => FALSE"
      using h0 h1 by auto

    from hf
    have hh0: "?gxx"
      by (rule zenon_disjE1 [OF _ hg1x])
    have hi: "cas \\in UNION {CaseArm (<<>>[i], <<>>[i])
                                 : i \\in DOMAIN <<>>}"
      using hh0 by (simp only: zenon_seqify_empty)
    show FALSE
      by (rule zenon_case_empty_union [OF hi])
  qed
qed

lemma zenon_case2 :
  fixes P c1x e1x c2x e2x
  assumes h: "P (CASE c1x -> e1x [] c2x -> e2x)"
             (is "P (?cas)")
  assumes h1: "c1x ==> P (e1x) ==> FALSE"
  assumes h2: "c2x ==> P (e2x) ==> FALSE"
  assumes hoth: "~c2x & ~c1x & TRUE ==> FALSE"
  shows FALSE
proof -
  def cs == "<<c1x, c2x>>" (is "?cs")
  def es == "<<e1x, e2x>>" (is "?es")
  def arms == "UNION {CaseArm (?cs[i], ?es[i]) : i \\in DOMAIN ?cs}"
              (is "?arms")
  def cas == "?cas"
  have h0: "P (cas)" using h by (fold cas_def)
  def dcs == "c2x | c1x" (is "?dcs")
  show FALSE
  proof (rule zenon_em [of "?dcs"])
    assume ha: "~(?dcs)"
    have hh1: "~c1x" using ha by blast
    have hh2: "~c2x" using ha by blast
    show FALSE
      using hoth hh1 hh2 by blast
  next
    assume ha: "?dcs"
    def scs == "zenon_seqify (zenon_appseq (zenon_appseq (
                               <<>>, c1x), c2x))"
               (is "?scs")
    def ses == "zenon_seqify (zenon_appseq (zenon_appseq (
                               <<>>, e1x), e2x))"
               (is "?ses")
    have ha1: "\<exists> i \<in> DOMAIN ?scs : ?scs[i]"
      using ha zenon_case_seq_empty
      by (simp only: zenon_case_seq_simpl zenon_seqify_empty, blast)
    have ha2: "\<exists> i \<in> DOMAIN ?cs : ?cs[i]"
      using ha1 by (simp only: zenon_seqify_appseq zenon_seqify_empty)
    have hb: "\\E x : x \\in arms"
      using zenon_case_domain [OF ha2, where es = "?es"]
      by (unfold arms_def, blast)
    have hc: "(CHOOSE x : x \\in arms) \\in arms"
      using hb by (unfold Ex_def, auto)
    have hf0: "?cas \\in arms"
      using hc by (unfold arms_def, fold Case_def)
    have hf3: "cas \\in UNION {CaseArm (?scs[i], ?ses[i])
                                  : i \\in DOMAIN ?scs}"
              (is "?hf3")
      using hf0 by (fold cas_def, unfold arms_def,
                    simp only: zenon_seqify_appseq zenon_seqify_empty)
    have hf4: "Len (?scs) = Len (?ses)" (is "?hf4")
      by (simp only: zenon_case_len_simpl)
    have hf5: "?hf4 & ?hf3"
      by (rule conjI [OF hf4 hf3])
    have hf: "
               cas \\in CaseArm (c2x, e2x)
             | cas \\in CaseArm (c1x, e1x)
             | cas \\in UNION {CaseArm (zenon_seqify (<<>>)[i],
                                          zenon_seqify (<<>>)[i])
                                 : i \\in DOMAIN zenon_seqify (<<>>)}
             " (is "_ | ?gxx")
      using hf5 by (simp only: zenon_case_union_simpl, blast)
    have hg1x: "cas \\in CaseArm (c1x, e1x) => FALSE"
      using h0 h1 by auto
    have hg2x: "cas \\in CaseArm (c2x, e2x) => FALSE"
      using h0 h2 by auto
    from hf
    have hh0: "?gxx" (is "_ | ?g0")
      by (rule zenon_disjE1 [OF _ hg2x])
    then have hh0: "?g0"
      by (rule zenon_disjE1 [OF _ hg1x])
    have hi: "cas \\in UNION {CaseArm (<<>>[i], <<>>[i])
                                 : i \\in DOMAIN <<>>}"
      using hh0 by (simp only: zenon_seqify_empty)
    show FALSE
      by (rule zenon_case_empty_union [OF hi])
  qed
qed

lemma zenon_caseother2 :
  fixes P oth c1x e1x c2x e2x
  assumes h: "P (CASE c1x -> e1x [] c2x -> e2x
                  [] OTHER -> oth)"
             (is "P (?cas)")
  assumes h1: "c1x ==> P (e1x) ==> FALSE"
  assumes h2: "c2x ==> P (e2x) ==> FALSE"
  assumes hoth: "~c2x & ~c1x & TRUE ==> P (oth) ==> FALSE"
  shows FALSE
proof -
  def cs == "<<c1x, c2x>>" (is "?cs")
  def es == "<<e1x, e2x>>" (is "?es")
  def arms == "UNION {CaseArm (?cs[i], ?es[i]) : i \\in DOMAIN ?cs}"
              (is "?arms")
  def cas == "?cas"
  have h0: "P (cas)" using h by (fold cas_def)
  def dcs == "c2x | c1x | FALSE" (is "?dcs")
  def scs == "zenon_seqify (zenon_appseq (zenon_appseq (
                             <<>>, c1x), c2x))"
             (is "?scs")
  have hscs : "?cs = ?scs"
    by (simp only: zenon_seqify_appseq zenon_seqify_empty)
  def ses == "zenon_seqify (zenon_appseq (zenon_appseq (
                             <<>>, e1x), e2x))"
             (is "?ses")
  have hses : "?es = ?ses"
    by (simp only: zenon_seqify_appseq zenon_seqify_empty)
  have hlen: "Len (?scs) = Len (?ses)" (is "?hlen")
    by (simp only: zenon_case_len_simpl)
  def armoth == "CaseArm (\<forall> i \<in> DOMAIN ?cs : ~?cs[i], oth)"
                (is "?armoth")
  show FALSE
  proof (rule zenon_em [of "?dcs"])
    assume ha: "~(?dcs)"
    have hb: "P (CHOOSE x : x \\in arms \<union> armoth)"
      using h by (unfold CaseOther_def, fold arms_def armoth_def)
    have hc: "arms \\cup armoth
              = UNION {CaseArm (?scs[i], ?ses[i]) : i \\in DOMAIN ?scs}
                \\cup CaseArm (\<forall> i \<in> DOMAIN ?scs : ~?scs[i],
                                 oth)"
             (is "_ = ?sarmsoth")
      using hscs hses by (unfold arms_def armoth_def, auto)
    have hd: "~(?dcs) & ?hlen & arms \<union> armoth = ?sarmsoth"
      using ha hlen hc by blast
    have he: "arms \<union> armoth = {oth}"
      using hd by (simp only: zenon_case_oth_simpl zenon_case_oth_empty)
    have hf: "(CHOOSE x : x \\in arms \\cup armoth) = oth"
      using he by auto
    have hg: "P (oth)"
      using hb hf by auto
    have hh1: "~c1x" using ha by blast
    have hh2: "~c2x" using ha by blast
    show FALSE
      using hg hoth hh1 hh2 by blast
  next
    assume ha: "?dcs"
    have ha1: "\<exists> i \<in> DOMAIN ?scs : ?scs[i]"
      using ha zenon_case_seq_empty
      by (simp only: zenon_case_seq_simpl zenon_seqify_empty, blast)
    have ha2: "\<exists> i \<in> DOMAIN ?cs : ?cs[i]"
      using ha1 hscs by auto
    have ha3: "~ (\<forall> i \<in> DOMAIN ?cs : ~?cs[i])"
      using ha2 by blast
    have ha4: "armoth = {}"
      using ha3 condElse [OF ha3, where t = "{oth}" and e = "{}"]
      by (unfold armoth_def CaseArm_def, blast)
    have hb: "\\E x : x \\in arms \\cup armoth"
      using zenon_case_domain [OF ha2, where es = "?es"]
      by (unfold arms_def, blast)
    have hc: "(CHOOSE x : x \\in arms \\cup armoth)
               \\in arms \\cup armoth"
      using hb by (unfold Ex_def, auto)
    have hf0: "?cas \\in arms \\cup armoth"
      using hc by (unfold arms_def armoth_def, fold CaseOther_def)
    have hf1: "cas \\in arms \\cup armoth"
      using hf0 by (fold cas_def)
    have hf2: "cas \\in arms"
      using hf1 ha4 by auto
    have hf3: "cas \\in UNION {CaseArm (?scs[i], ?ses[i])
                                  : i \\in DOMAIN ?scs}"
              (is "?hf3")
      using hf2 by (unfold arms_def,
                    simp only: zenon_seqify_appseq zenon_seqify_empty)
    have hf5: "?hlen & ?hf3"
      by (rule conjI [OF hlen hf3])
    have hf: "
               cas \\in CaseArm (c2x, e2x)
             | cas \\in CaseArm (c1x, e1x)
             | cas \\in UNION {CaseArm (zenon_seqify (<<>>)[i],
                                          zenon_seqify (<<>>)[i])
                                 : i \\in DOMAIN zenon_seqify (<<>>)}
             " (is "_ | ?gxx")
      using hf5 by (simp only: zenon_case_union_simpl, blast)
    have hg1x: "cas \\in CaseArm (c1x, e1x) => FALSE"
      using h0 h1 by auto
    have hg2x: "cas \\in CaseArm (c2x, e2x) => FALSE"
      using h0 h2 by auto
    from hf
    have hh0: "?gxx" (is "_ | ?g0")
      by (rule zenon_disjE1 [OF _ hg2x])
    then have hh0: "?g0"
      by (rule zenon_disjE1 [OF _ hg1x])
    have hi: "cas \\in UNION {CaseArm (<<>>[i], <<>>[i])
                                 : i \\in DOMAIN <<>>}"
      using hh0 by (simp only: zenon_seqify_empty)
    show FALSE
      by (rule zenon_case_empty_union [OF hi])
  qed
qed

lemma zenon_case3 :
  fixes P c1x e1x c2x e2x c3x e3x
  assumes h: "P (CASE c1x -> e1x [] c2x -> e2x [] c3x -> e3x)"
             (is "P (?cas)")
  assumes h1: "c1x ==> P (e1x) ==> FALSE"
  assumes h2: "c2x ==> P (e2x) ==> FALSE"
  assumes h3: "c3x ==> P (e3x) ==> FALSE"
  assumes hoth: "~c3x & ~c2x & ~c1x & TRUE ==> FALSE"
  shows FALSE
proof -
  def cs == "<<c1x, c2x, c3x>>" (is "?cs")
  def es == "<<e1x, e2x, e3x>>" (is "?es")
  def arms == "UNION {CaseArm (?cs[i], ?es[i]) : i \\in DOMAIN ?cs}"
              (is "?arms")
  def cas == "?cas"
  have h0: "P (cas)" using h by (fold cas_def)
  def dcs == "c3x | c2x | c1x" (is "?dcs")
  show FALSE
  proof (rule zenon_em [of "?dcs"])
    assume ha: "~(?dcs)"
    have hh1: "~c1x" using ha by blast
    have hh2: "~c2x" using ha by blast
    have hh3: "~c3x" using ha by blast
    show FALSE
      using hoth hh1 hh2 hh3 by blast
  next
    assume ha: "?dcs"
    def scs == "zenon_seqify (zenon_appseq (zenon_appseq (zenon_appseq (
                               <<>>, c1x), c2x), c3x))"
               (is "?scs")
    def ses == "zenon_seqify (zenon_appseq (zenon_appseq (zenon_appseq (
                               <<>>, e1x), e2x), e3x))"
               (is "?ses")
    have ha1: "\<exists> i \<in> DOMAIN ?scs : ?scs[i]"
      using ha zenon_case_seq_empty
      by (simp only: zenon_case_seq_simpl zenon_seqify_empty, blast)
    have ha2: "\<exists> i \<in> DOMAIN ?cs : ?cs[i]"
      using ha1 by (simp only: zenon_seqify_appseq zenon_seqify_empty)
    have hb: "\\E x : x \\in arms"
      using zenon_case_domain [OF ha2, where es = "?es"]
      by (unfold arms_def, blast)
    have hc: "(CHOOSE x : x \\in arms) \\in arms"
      using hb by (unfold Ex_def, auto)
    have hf0: "?cas \\in arms"
      using hc by (unfold arms_def, fold Case_def)
    have hf3: "cas \\in UNION {CaseArm (?scs[i], ?ses[i])
                                  : i \\in DOMAIN ?scs}"
              (is "?hf3")
      using hf0 by (fold cas_def, unfold arms_def,
                    simp only: zenon_seqify_appseq zenon_seqify_empty)
    have hf4: "Len (?scs) = Len (?ses)" (is "?hf4")
      by (simp only: zenon_case_len_simpl)
    have hf5: "?hf4 & ?hf3"
      by (rule conjI [OF hf4 hf3])
    have hf: "
               cas \\in CaseArm (c3x, e3x)
             | cas \\in CaseArm (c2x, e2x)
             | cas \\in CaseArm (c1x, e1x)
             | cas \\in UNION {CaseArm (zenon_seqify (<<>>)[i],
                                          zenon_seqify (<<>>)[i])
                                 : i \\in DOMAIN zenon_seqify (<<>>)}
             " (is "_ | ?gxx")
      using hf5 by (simp only: zenon_case_union_simpl, blast)
    have hg1x: "cas \\in CaseArm (c1x, e1x) => FALSE"
      using h0 h1 by auto
    have hg2x: "cas \\in CaseArm (c2x, e2x) => FALSE"
      using h0 h2 by auto
    have hg3x: "cas \\in CaseArm (c3x, e3x) => FALSE"
      using h0 h3 by auto
    from hf
    have hh0: "?gxx" (is "_ | ?g1")
      by (rule zenon_disjE1 [OF _ hg3x])
    then have hh1: "?g1" (is "_ | ?g0")
      by (rule zenon_disjE1 [OF _ hg2x])
    then have hh0: "?g0"
      by (rule zenon_disjE1 [OF _ hg1x])
    have hi: "cas \\in UNION {CaseArm (<<>>[i], <<>>[i])
                                 : i \\in DOMAIN <<>>}"
      using hh0 by (simp only: zenon_seqify_empty)
    show FALSE
      by (rule zenon_case_empty_union [OF hi])
  qed
qed

lemma zenon_caseother3 :
  fixes P oth c1x e1x c2x e2x c3x e3x
  assumes h: "P (CASE c1x -> e1x [] c2x -> e2x [] c3x -> e3x
                  [] OTHER -> oth)"
             (is "P (?cas)")
  assumes h1: "c1x ==> P (e1x) ==> FALSE"
  assumes h2: "c2x ==> P (e2x) ==> FALSE"
  assumes h3: "c3x ==> P (e3x) ==> FALSE"
  assumes hoth: "~c3x & ~c2x & ~c1x & TRUE ==> P (oth) ==> FALSE"
  shows FALSE
proof -
  def cs == "<<c1x, c2x, c3x>>" (is "?cs")
  def es == "<<e1x, e2x, e3x>>" (is "?es")
  def arms == "UNION {CaseArm (?cs[i], ?es[i]) : i \\in DOMAIN ?cs}"
              (is "?arms")
  def cas == "?cas"
  have h0: "P (cas)" using h by (fold cas_def)
  def dcs == "c3x | c2x | c1x | FALSE" (is "?dcs")
  def scs == "zenon_seqify (zenon_appseq (zenon_appseq (zenon_appseq (
                             <<>>, c1x), c2x), c3x))"
             (is "?scs")
  have hscs : "?cs = ?scs"
    by (simp only: zenon_seqify_appseq zenon_seqify_empty)
  def ses == "zenon_seqify (zenon_appseq (zenon_appseq (zenon_appseq (
                             <<>>, e1x), e2x), e3x))"
             (is "?ses")
  have hses : "?es = ?ses"
    by (simp only: zenon_seqify_appseq zenon_seqify_empty)
  have hlen: "Len (?scs) = Len (?ses)" (is "?hlen")
    by (simp only: zenon_case_len_simpl)
  def armoth == "CaseArm (\<forall> i \<in> DOMAIN ?cs : ~?cs[i], oth)"
                (is "?armoth")
  show FALSE
  proof (rule zenon_em [of "?dcs"])
    assume ha: "~(?dcs)"
    have hb: "P (CHOOSE x : x \\in arms \<union> armoth)"
      using h by (unfold CaseOther_def, fold arms_def armoth_def)
    have hc: "arms \\cup armoth
              = UNION {CaseArm (?scs[i], ?ses[i]) : i \\in DOMAIN ?scs}
                \\cup CaseArm (\<forall> i \<in> DOMAIN ?scs : ~?scs[i],
                                 oth)"
             (is "_ = ?sarmsoth")
      using hscs hses by (unfold arms_def armoth_def, auto)
    have hd: "~(?dcs) & ?hlen & arms \<union> armoth = ?sarmsoth"
      using ha hlen hc by blast
    have he: "arms \<union> armoth = {oth}"
      using hd by (simp only: zenon_case_oth_simpl zenon_case_oth_empty)
    have hf: "(CHOOSE x : x \\in arms \\cup armoth) = oth"
      using he by auto
    have hg: "P (oth)"
      using hb hf by auto
    have hh1: "~c1x" using ha by blast
    have hh2: "~c2x" using ha by blast
    have hh3: "~c3x" using ha by blast
    show FALSE
      using hg hoth hh1 hh2 hh3 by blast
  next
    assume ha: "?dcs"
    have ha1: "\<exists> i \<in> DOMAIN ?scs : ?scs[i]"
      using ha zenon_case_seq_empty
      by (simp only: zenon_case_seq_simpl zenon_seqify_empty, blast)
    have ha2: "\<exists> i \<in> DOMAIN ?cs : ?cs[i]"
      using ha1 hscs by auto
    have ha3: "~ (\<forall> i \<in> DOMAIN ?cs : ~?cs[i])"
      using ha2 by blast
    have ha4: "armoth = {}"
      using ha3 condElse [OF ha3, where t = "{oth}" and e = "{}"]
      by (unfold armoth_def CaseArm_def, blast)
    have hb: "\\E x : x \\in arms \\cup armoth"
      using zenon_case_domain [OF ha2, where es = "?es"]
      by (unfold arms_def, blast)
    have hc: "(CHOOSE x : x \\in arms \\cup armoth)
               \\in arms \\cup armoth"
      using hb by (unfold Ex_def, auto)
    have hf0: "?cas \\in arms \\cup armoth"
      using hc by (unfold arms_def armoth_def, fold CaseOther_def)
    have hf1: "cas \\in arms \\cup armoth"
      using hf0 by (fold cas_def)
    have hf2: "cas \\in arms"
      using hf1 ha4 by auto
    have hf3: "cas \\in UNION {CaseArm (?scs[i], ?ses[i])
                                  : i \\in DOMAIN ?scs}"
              (is "?hf3")
      using hf2 by (unfold arms_def,
                    simp only: zenon_seqify_appseq zenon_seqify_empty)
    have hf5: "?hlen & ?hf3"
      by (rule conjI [OF hlen hf3])
    have hf: "
               cas \\in CaseArm (c3x, e3x)
             | cas \\in CaseArm (c2x, e2x)
             | cas \\in CaseArm (c1x, e1x)
             | cas \\in UNION {CaseArm (zenon_seqify (<<>>)[i],
                                          zenon_seqify (<<>>)[i])
                                 : i \\in DOMAIN zenon_seqify (<<>>)}
             " (is "_ | ?gxx")
      using hf5 by (simp only: zenon_case_union_simpl, blast)
    have hg1x: "cas \\in CaseArm (c1x, e1x) => FALSE"
      using h0 h1 by auto
    have hg2x: "cas \\in CaseArm (c2x, e2x) => FALSE"
      using h0 h2 by auto
    have hg3x: "cas \\in CaseArm (c3x, e3x) => FALSE"
      using h0 h3 by auto
    from hf
    have hh0: "?gxx" (is "_ | ?g1")
      by (rule zenon_disjE1 [OF _ hg3x])
    then have hh1: "?g1" (is "_ | ?g0")
      by (rule zenon_disjE1 [OF _ hg2x])
    then have hh0: "?g0"
      by (rule zenon_disjE1 [OF _ hg1x])
    have hi: "cas \\in UNION {CaseArm (<<>>[i], <<>>[i])
                                 : i \\in DOMAIN <<>>}"
      using hh0 by (simp only: zenon_seqify_empty)
    show FALSE
      by (rule zenon_case_empty_union [OF hi])
  qed
qed

lemma zenon_case4 :
  fixes P c1x e1x c2x e2x c3x e3x c4x e4x
  assumes h: "P (CASE c1x -> e1x [] c2x -> e2x [] c3x -> e3x [] c4x -> e4x)"
             (is "P (?cas)")
  assumes h1: "c1x ==> P (e1x) ==> FALSE"
  assumes h2: "c2x ==> P (e2x) ==> FALSE"
  assumes h3: "c3x ==> P (e3x) ==> FALSE"
  assumes h4: "c4x ==> P (e4x) ==> FALSE"
  assumes hoth: "~c4x & ~c3x & ~c2x & ~c1x & TRUE ==> FALSE"
  shows FALSE
proof -
  def cs == "<<c1x, c2x, c3x, c4x>>" (is "?cs")
  def es == "<<e1x, e2x, e3x, e4x>>" (is "?es")
  def arms == "UNION {CaseArm (?cs[i], ?es[i]) : i \\in DOMAIN ?cs}"
              (is "?arms")
  def cas == "?cas"
  have h0: "P (cas)" using h by (fold cas_def)
  def dcs == "c4x | c3x | c2x | c1x" (is "?dcs")
  show FALSE
  proof (rule zenon_em [of "?dcs"])
    assume ha: "~(?dcs)"
    have hh1: "~c1x" using ha by blast
    have hh2: "~c2x" using ha by blast
    have hh3: "~c3x" using ha by blast
    have hh4: "~c4x" using ha by blast
    show FALSE
      using hoth hh1 hh2 hh3 hh4 by blast
  next
    assume ha: "?dcs"
    def scs == "zenon_seqify (zenon_appseq (zenon_appseq (zenon_appseq (zenon_appseq (
                               <<>>, c1x), c2x), c3x), c4x))"
               (is "?scs")
    def ses == "zenon_seqify (zenon_appseq (zenon_appseq (zenon_appseq (zenon_appseq (
                               <<>>, e1x), e2x), e3x), e4x))"
               (is "?ses")
    have ha1: "\<exists> i \<in> DOMAIN ?scs : ?scs[i]"
      using ha zenon_case_seq_empty
      by (simp only: zenon_case_seq_simpl zenon_seqify_empty, blast)
    have ha2: "\<exists> i \<in> DOMAIN ?cs : ?cs[i]"
      using ha1 by (simp only: zenon_seqify_appseq zenon_seqify_empty)
    have hb: "\\E x : x \\in arms"
      using zenon_case_domain [OF ha2, where es = "?es"]
      by (unfold arms_def, blast)
    have hc: "(CHOOSE x : x \\in arms) \\in arms"
      using hb by (unfold Ex_def, auto)
    have hf0: "?cas \\in arms"
      using hc by (unfold arms_def, fold Case_def)
    have hf3: "cas \\in UNION {CaseArm (?scs[i], ?ses[i])
                                  : i \\in DOMAIN ?scs}"
              (is "?hf3")
      using hf0 by (fold cas_def, unfold arms_def,
                    simp only: zenon_seqify_appseq zenon_seqify_empty)
    have hf4: "Len (?scs) = Len (?ses)" (is "?hf4")
      by (simp only: zenon_case_len_simpl)
    have hf5: "?hf4 & ?hf3"
      by (rule conjI [OF hf4 hf3])
    have hf: "
               cas \\in CaseArm (c4x, e4x)
             | cas \\in CaseArm (c3x, e3x)
             | cas \\in CaseArm (c2x, e2x)
             | cas \\in CaseArm (c1x, e1x)
             | cas \\in UNION {CaseArm (zenon_seqify (<<>>)[i],
                                          zenon_seqify (<<>>)[i])
                                 : i \\in DOMAIN zenon_seqify (<<>>)}
             " (is "_ | ?gxx")
      using hf5 by (simp only: zenon_case_union_simpl, blast)
    have hg1x: "cas \\in CaseArm (c1x, e1x) => FALSE"
      using h0 h1 by auto
    have hg2x: "cas \\in CaseArm (c2x, e2x) => FALSE"
      using h0 h2 by auto
    have hg3x: "cas \\in CaseArm (c3x, e3x) => FALSE"
      using h0 h3 by auto
    have hg4x: "cas \\in CaseArm (c4x, e4x) => FALSE"
      using h0 h4 by auto
    from hf
    have hh0: "?gxx" (is "_ | ?g2")
      by (rule zenon_disjE1 [OF _ hg4x])
    then have hh2: "?g2" (is "_ | ?g1")
      by (rule zenon_disjE1 [OF _ hg3x])
    then have hh1: "?g1" (is "_ | ?g0")
      by (rule zenon_disjE1 [OF _ hg2x])
    then have hh0: "?g0"
      by (rule zenon_disjE1 [OF _ hg1x])
    have hi: "cas \\in UNION {CaseArm (<<>>[i], <<>>[i])
                                 : i \\in DOMAIN <<>>}"
      using hh0 by (simp only: zenon_seqify_empty)
    show FALSE
      by (rule zenon_case_empty_union [OF hi])
  qed
qed

lemma zenon_caseother4 :
  fixes P oth c1x e1x c2x e2x c3x e3x c4x e4x
  assumes h: "P (CASE c1x -> e1x [] c2x -> e2x [] c3x -> e3x [] c4x -> e4x
                  [] OTHER -> oth)"
             (is "P (?cas)")
  assumes h1: "c1x ==> P (e1x) ==> FALSE"
  assumes h2: "c2x ==> P (e2x) ==> FALSE"
  assumes h3: "c3x ==> P (e3x) ==> FALSE"
  assumes h4: "c4x ==> P (e4x) ==> FALSE"
  assumes hoth: "~c4x & ~c3x & ~c2x & ~c1x & TRUE ==> P (oth) ==> FALSE"
  shows FALSE
proof -
  def cs == "<<c1x, c2x, c3x, c4x>>" (is "?cs")
  def es == "<<e1x, e2x, e3x, e4x>>" (is "?es")
  def arms == "UNION {CaseArm (?cs[i], ?es[i]) : i \\in DOMAIN ?cs}"
              (is "?arms")
  def cas == "?cas"
  have h0: "P (cas)" using h by (fold cas_def)
  def dcs == "c4x | c3x | c2x | c1x | FALSE" (is "?dcs")
  def scs == "zenon_seqify (zenon_appseq (zenon_appseq (zenon_appseq (zenon_appseq (
                             <<>>, c1x), c2x), c3x), c4x))"
             (is "?scs")
  have hscs : "?cs = ?scs"
    by (simp only: zenon_seqify_appseq zenon_seqify_empty)
  def ses == "zenon_seqify (zenon_appseq (zenon_appseq (zenon_appseq (zenon_appseq (
                             <<>>, e1x), e2x), e3x), e4x))"
             (is "?ses")
  have hses : "?es = ?ses"
    by (simp only: zenon_seqify_appseq zenon_seqify_empty)
  have hlen: "Len (?scs) = Len (?ses)" (is "?hlen")
    by (simp only: zenon_case_len_simpl)
  def armoth == "CaseArm (\<forall> i \<in> DOMAIN ?cs : ~?cs[i], oth)"
                (is "?armoth")
  show FALSE
  proof (rule zenon_em [of "?dcs"])
    assume ha: "~(?dcs)"
    have hb: "P (CHOOSE x : x \\in arms \<union> armoth)"
      using h by (unfold CaseOther_def, fold arms_def armoth_def)
    have hc: "arms \\cup armoth
              = UNION {CaseArm (?scs[i], ?ses[i]) : i \\in DOMAIN ?scs}
                \\cup CaseArm (\<forall> i \<in> DOMAIN ?scs : ~?scs[i],
                                 oth)"
             (is "_ = ?sarmsoth")
      using hscs hses by (unfold arms_def armoth_def, auto)
    have hd: "~(?dcs) & ?hlen & arms \<union> armoth = ?sarmsoth"
      using ha hlen hc by blast
    have he: "arms \<union> armoth = {oth}"
      using hd by (simp only: zenon_case_oth_simpl zenon_case_oth_empty)
    have hf: "(CHOOSE x : x \\in arms \\cup armoth) = oth"
      using he by auto
    have hg: "P (oth)"
      using hb hf by auto
    have hh1: "~c1x" using ha by blast
    have hh2: "~c2x" using ha by blast
    have hh3: "~c3x" using ha by blast
    have hh4: "~c4x" using ha by blast
    show FALSE
      using hg hoth hh1 hh2 hh3 hh4 by blast
  next
    assume ha: "?dcs"
    have ha1: "\<exists> i \<in> DOMAIN ?scs : ?scs[i]"
      using ha zenon_case_seq_empty
      by (simp only: zenon_case_seq_simpl zenon_seqify_empty, blast)
    have ha2: "\<exists> i \<in> DOMAIN ?cs : ?cs[i]"
      using ha1 hscs by auto
    have ha3: "~ (\<forall> i \<in> DOMAIN ?cs : ~?cs[i])"
      using ha2 by blast
    have ha4: "armoth = {}"
      using ha3 condElse [OF ha3, where t = "{oth}" and e = "{}"]
      by (unfold armoth_def CaseArm_def, blast)
    have hb: "\\E x : x \\in arms \\cup armoth"
      using zenon_case_domain [OF ha2, where es = "?es"]
      by (unfold arms_def, blast)
    have hc: "(CHOOSE x : x \\in arms \\cup armoth)
               \\in arms \\cup armoth"
      using hb by (unfold Ex_def, auto)
    have hf0: "?cas \\in arms \\cup armoth"
      using hc by (unfold arms_def armoth_def, fold CaseOther_def)
    have hf1: "cas \\in arms \\cup armoth"
      using hf0 by (fold cas_def)
    have hf2: "cas \\in arms"
      using hf1 ha4 by auto
    have hf3: "cas \\in UNION {CaseArm (?scs[i], ?ses[i])
                                  : i \\in DOMAIN ?scs}"
              (is "?hf3")
      using hf2 by (unfold arms_def,
                    simp only: zenon_seqify_appseq zenon_seqify_empty)
    have hf5: "?hlen & ?hf3"
      by (rule conjI [OF hlen hf3])
    have hf: "
               cas \\in CaseArm (c4x, e4x)
             | cas \\in CaseArm (c3x, e3x)
             | cas \\in CaseArm (c2x, e2x)
             | cas \\in CaseArm (c1x, e1x)
             | cas \\in UNION {CaseArm (zenon_seqify (<<>>)[i],
                                          zenon_seqify (<<>>)[i])
                                 : i \\in DOMAIN zenon_seqify (<<>>)}
             " (is "_ | ?gxx")
      using hf5 by (simp only: zenon_case_union_simpl, blast)
    have hg1x: "cas \\in CaseArm (c1x, e1x) => FALSE"
      using h0 h1 by auto
    have hg2x: "cas \\in CaseArm (c2x, e2x) => FALSE"
      using h0 h2 by auto
    have hg3x: "cas \\in CaseArm (c3x, e3x) => FALSE"
      using h0 h3 by auto
    have hg4x: "cas \\in CaseArm (c4x, e4x) => FALSE"
      using h0 h4 by auto
    from hf
    have hh0: "?gxx" (is "_ | ?g2")
      by (rule zenon_disjE1 [OF _ hg4x])
    then have hh2: "?g2" (is "_ | ?g1")
      by (rule zenon_disjE1 [OF _ hg3x])
    then have hh1: "?g1" (is "_ | ?g0")
      by (rule zenon_disjE1 [OF _ hg2x])
    then have hh0: "?g0"
      by (rule zenon_disjE1 [OF _ hg1x])
    have hi: "cas \\in UNION {CaseArm (<<>>[i], <<>>[i])
                                 : i \\in DOMAIN <<>>}"
      using hh0 by (simp only: zenon_seqify_empty)
    show FALSE
      by (rule zenon_case_empty_union [OF hi])
  qed
qed

lemma zenon_case5 :
  fixes P c1x e1x c2x e2x c3x e3x c4x e4x c5x e5x
  assumes h: "P (CASE c1x -> e1x [] c2x -> e2x [] c3x -> e3x [] c4x -> e4x [] c5x -> e5x)"
             (is "P (?cas)")
  assumes h1: "c1x ==> P (e1x) ==> FALSE"
  assumes h2: "c2x ==> P (e2x) ==> FALSE"
  assumes h3: "c3x ==> P (e3x) ==> FALSE"
  assumes h4: "c4x ==> P (e4x) ==> FALSE"
  assumes h5: "c5x ==> P (e5x) ==> FALSE"
  assumes hoth: "~c5x & ~c4x & ~c3x & ~c2x & ~c1x & TRUE ==> FALSE"
  shows FALSE
proof -
  def cs == "<<c1x, c2x, c3x, c4x, c5x>>" (is "?cs")
  def es == "<<e1x, e2x, e3x, e4x, e5x>>" (is "?es")
  def arms == "UNION {CaseArm (?cs[i], ?es[i]) : i \\in DOMAIN ?cs}"
              (is "?arms")
  def cas == "?cas"
  have h0: "P (cas)" using h by (fold cas_def)
  def dcs == "c5x | c4x | c3x | c2x | c1x" (is "?dcs")
  show FALSE
  proof (rule zenon_em [of "?dcs"])
    assume ha: "~(?dcs)"
    have hh1: "~c1x" using ha by blast
    have hh2: "~c2x" using ha by blast
    have hh3: "~c3x" using ha by blast
    have hh4: "~c4x" using ha by blast
    have hh5: "~c5x" using ha by blast
    show FALSE
      using hoth hh1 hh2 hh3 hh4 hh5 by blast
  next
    assume ha: "?dcs"
    def scs == "zenon_seqify (zenon_appseq (zenon_appseq (zenon_appseq (zenon_appseq (zenon_appseq (
                               <<>>, c1x), c2x), c3x), c4x), c5x))"
               (is "?scs")
    def ses == "zenon_seqify (zenon_appseq (zenon_appseq (zenon_appseq (zenon_appseq (zenon_appseq (
                               <<>>, e1x), e2x), e3x), e4x), e5x))"
               (is "?ses")
    have ha1: "\<exists> i \<in> DOMAIN ?scs : ?scs[i]"
      using ha zenon_case_seq_empty
      by (simp only: zenon_case_seq_simpl zenon_seqify_empty, blast)
    have ha2: "\<exists> i \<in> DOMAIN ?cs : ?cs[i]"
      using ha1 by (simp only: zenon_seqify_appseq zenon_seqify_empty)
    have hb: "\\E x : x \\in arms"
      using zenon_case_domain [OF ha2, where es = "?es"]
      by (unfold arms_def, blast)
    have hc: "(CHOOSE x : x \\in arms) \\in arms"
      using hb by (unfold Ex_def, auto)
    have hf0: "?cas \\in arms"
      using hc by (unfold arms_def, fold Case_def)
    have hf3: "cas \\in UNION {CaseArm (?scs[i], ?ses[i])
                                  : i \\in DOMAIN ?scs}"
              (is "?hf3")
      using hf0 by (fold cas_def, unfold arms_def,
                    simp only: zenon_seqify_appseq zenon_seqify_empty)
    have hf4: "Len (?scs) = Len (?ses)" (is "?hf4")
      by (simp only: zenon_case_len_simpl)
    have hf5: "?hf4 & ?hf3"
      by (rule conjI [OF hf4 hf3])
    have hf: "
               cas \\in CaseArm (c5x, e5x)
             | cas \\in CaseArm (c4x, e4x)
             | cas \\in CaseArm (c3x, e3x)
             | cas \\in CaseArm (c2x, e2x)
             | cas \\in CaseArm (c1x, e1x)
             | cas \\in UNION {CaseArm (zenon_seqify (<<>>)[i],
                                          zenon_seqify (<<>>)[i])
                                 : i \\in DOMAIN zenon_seqify (<<>>)}
             " (is "_ | ?gxx")
      using hf5 by (simp only: zenon_case_union_simpl, blast)
    have hg1x: "cas \\in CaseArm (c1x, e1x) => FALSE"
      using h0 h1 by auto
    have hg2x: "cas \\in CaseArm (c2x, e2x) => FALSE"
      using h0 h2 by auto
    have hg3x: "cas \\in CaseArm (c3x, e3x) => FALSE"
      using h0 h3 by auto
    have hg4x: "cas \\in CaseArm (c4x, e4x) => FALSE"
      using h0 h4 by auto
    have hg5x: "cas \\in CaseArm (c5x, e5x) => FALSE"
      using h0 h5 by auto
    from hf
    have hh0: "?gxx" (is "_ | ?g3")
      by (rule zenon_disjE1 [OF _ hg5x])
    then have hh3: "?g3" (is "_ | ?g2")
      by (rule zenon_disjE1 [OF _ hg4x])
    then have hh2: "?g2" (is "_ | ?g1")
      by (rule zenon_disjE1 [OF _ hg3x])
    then have hh1: "?g1" (is "_ | ?g0")
      by (rule zenon_disjE1 [OF _ hg2x])
    then have hh0: "?g0"
      by (rule zenon_disjE1 [OF _ hg1x])
    have hi: "cas \\in UNION {CaseArm (<<>>[i], <<>>[i])
                                 : i \\in DOMAIN <<>>}"
      using hh0 by (simp only: zenon_seqify_empty)
    show FALSE
      by (rule zenon_case_empty_union [OF hi])
  qed
qed

lemma zenon_caseother5 :
  fixes P oth c1x e1x c2x e2x c3x e3x c4x e4x c5x e5x
  assumes h: "P (CASE c1x -> e1x [] c2x -> e2x [] c3x -> e3x [] c4x -> e4x [] c5x -> e5x
                  [] OTHER -> oth)"
             (is "P (?cas)")
  assumes h1: "c1x ==> P (e1x) ==> FALSE"
  assumes h2: "c2x ==> P (e2x) ==> FALSE"
  assumes h3: "c3x ==> P (e3x) ==> FALSE"
  assumes h4: "c4x ==> P (e4x) ==> FALSE"
  assumes h5: "c5x ==> P (e5x) ==> FALSE"
  assumes hoth: "~c5x & ~c4x & ~c3x & ~c2x & ~c1x & TRUE ==> P (oth) ==> FALSE"
  shows FALSE
proof -
  def cs == "<<c1x, c2x, c3x, c4x, c5x>>" (is "?cs")
  def es == "<<e1x, e2x, e3x, e4x, e5x>>" (is "?es")
  def arms == "UNION {CaseArm (?cs[i], ?es[i]) : i \\in DOMAIN ?cs}"
              (is "?arms")
  def cas == "?cas"
  have h0: "P (cas)" using h by (fold cas_def)
  def dcs == "c5x | c4x | c3x | c2x | c1x | FALSE" (is "?dcs")
  def scs == "zenon_seqify (zenon_appseq (zenon_appseq (zenon_appseq (zenon_appseq (zenon_appseq (
                             <<>>, c1x), c2x), c3x), c4x), c5x))"
             (is "?scs")
  have hscs : "?cs = ?scs"
    by (simp only: zenon_seqify_appseq zenon_seqify_empty)
  def ses == "zenon_seqify (zenon_appseq (zenon_appseq (zenon_appseq (zenon_appseq (zenon_appseq (
                             <<>>, e1x), e2x), e3x), e4x), e5x))"
             (is "?ses")
  have hses : "?es = ?ses"
    by (simp only: zenon_seqify_appseq zenon_seqify_empty)
  have hlen: "Len (?scs) = Len (?ses)" (is "?hlen")
    by (simp only: zenon_case_len_simpl)
  def armoth == "CaseArm (\<forall> i \<in> DOMAIN ?cs : ~?cs[i], oth)"
                (is "?armoth")
  show FALSE
  proof (rule zenon_em [of "?dcs"])
    assume ha: "~(?dcs)"
    have hb: "P (CHOOSE x : x \\in arms \<union> armoth)"
      using h by (unfold CaseOther_def, fold arms_def armoth_def)
    have hc: "arms \\cup armoth
              = UNION {CaseArm (?scs[i], ?ses[i]) : i \\in DOMAIN ?scs}
                \\cup CaseArm (\<forall> i \<in> DOMAIN ?scs : ~?scs[i],
                                 oth)"
             (is "_ = ?sarmsoth")
      using hscs hses by (unfold arms_def armoth_def, auto)
    have hd: "~(?dcs) & ?hlen & arms \<union> armoth = ?sarmsoth"
      using ha hlen hc by blast
    have he: "arms \<union> armoth = {oth}"
      using hd by (simp only: zenon_case_oth_simpl zenon_case_oth_empty)
    have hf: "(CHOOSE x : x \\in arms \\cup armoth) = oth"
      using he by auto
    have hg: "P (oth)"
      using hb hf by auto
    have hh1: "~c1x" using ha by blast
    have hh2: "~c2x" using ha by blast
    have hh3: "~c3x" using ha by blast
    have hh4: "~c4x" using ha by blast
    have hh5: "~c5x" using ha by blast
    show FALSE
      using hg hoth hh1 hh2 hh3 hh4 hh5 by blast
  next
    assume ha: "?dcs"
    have ha1: "\<exists> i \<in> DOMAIN ?scs : ?scs[i]"
      using ha zenon_case_seq_empty
      by (simp only: zenon_case_seq_simpl zenon_seqify_empty, blast)
    have ha2: "\<exists> i \<in> DOMAIN ?cs : ?cs[i]"
      using ha1 hscs by auto
    have ha3: "~ (\<forall> i \<in> DOMAIN ?cs : ~?cs[i])"
      using ha2 by blast
    have ha4: "armoth = {}"
      using ha3 condElse [OF ha3, where t = "{oth}" and e = "{}"]
      by (unfold armoth_def CaseArm_def, blast)
    have hb: "\\E x : x \\in arms \\cup armoth"
      using zenon_case_domain [OF ha2, where es = "?es"]
      by (unfold arms_def, blast)
    have hc: "(CHOOSE x : x \\in arms \\cup armoth)
               \\in arms \\cup armoth"
      using hb by (unfold Ex_def, auto)
    have hf0: "?cas \\in arms \\cup armoth"
      using hc by (unfold arms_def armoth_def, fold CaseOther_def)
    have hf1: "cas \\in arms \\cup armoth"
      using hf0 by (fold cas_def)
    have hf2: "cas \\in arms"
      using hf1 ha4 by auto
    have hf3: "cas \\in UNION {CaseArm (?scs[i], ?ses[i])
                                  : i \\in DOMAIN ?scs}"
              (is "?hf3")
      using hf2 by (unfold arms_def,
                    simp only: zenon_seqify_appseq zenon_seqify_empty)
    have hf5: "?hlen & ?hf3"
      by (rule conjI [OF hlen hf3])
    have hf: "
               cas \\in CaseArm (c5x, e5x)
             | cas \\in CaseArm (c4x, e4x)
             | cas \\in CaseArm (c3x, e3x)
             | cas \\in CaseArm (c2x, e2x)
             | cas \\in CaseArm (c1x, e1x)
             | cas \\in UNION {CaseArm (zenon_seqify (<<>>)[i],
                                          zenon_seqify (<<>>)[i])
                                 : i \\in DOMAIN zenon_seqify (<<>>)}
             " (is "_ | ?gxx")
      using hf5 by (simp only: zenon_case_union_simpl, blast)
    have hg1x: "cas \\in CaseArm (c1x, e1x) => FALSE"
      using h0 h1 by auto
    have hg2x: "cas \\in CaseArm (c2x, e2x) => FALSE"
      using h0 h2 by auto
    have hg3x: "cas \\in CaseArm (c3x, e3x) => FALSE"
      using h0 h3 by auto
    have hg4x: "cas \\in CaseArm (c4x, e4x) => FALSE"
      using h0 h4 by auto
    have hg5x: "cas \\in CaseArm (c5x, e5x) => FALSE"
      using h0 h5 by auto
    from hf
    have hh0: "?gxx" (is "_ | ?g3")
      by (rule zenon_disjE1 [OF _ hg5x])
    then have hh3: "?g3" (is "_ | ?g2")
      by (rule zenon_disjE1 [OF _ hg4x])
    then have hh2: "?g2" (is "_ | ?g1")
      by (rule zenon_disjE1 [OF _ hg3x])
    then have hh1: "?g1" (is "_ | ?g0")
      by (rule zenon_disjE1 [OF _ hg2x])
    then have hh0: "?g0"
      by (rule zenon_disjE1 [OF _ hg1x])
    have hi: "cas \\in UNION {CaseArm (<<>>[i], <<>>[i])
                                 : i \\in DOMAIN <<>>}"
      using hh0 by (simp only: zenon_seqify_empty)
    show FALSE
      by (rule zenon_case_empty_union [OF hi])
  qed
qed

(*** END AUTO_GENERATED STUFF ***)

end
