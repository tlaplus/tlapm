(* An attempt at defining the integers.

The steps in Isabelle/Isar are named `si_j` where `s` stands for "step",
`i` is the proof level, and `j` the step number.

Author: Ioannis Filippidis
All rights reserved. Licensed under 2-clause BSD.
*)
theory NewIntegers
imports
    NatArith
    (*NatDivision
    Tuples*)
begin

(*
Properties to prove:
    typeness,
    commutativity, associativity, distributivity
    transitivity, symmetry, antisymmetry, reflexivity,
    monotonicity
*)

(*----------------------------------------------------------------------------*)
(* Overriding notation. *)

no_notation NatOrderings.leq (infixl "<=" 50)
no_notation NatOrderings.geq (infixl ">=" 50)
no_notation NatOrderings.less (infixl "<" 50)
no_notation NatOrderings.greater (infixl ">" 50)
no_notation NatOrderings.natInterval ("(_ .. _)" [90,90] 70)

no_notation NatArith.arith_add (infixl "+" 65)
(* no_notation NatArith.adiff (infixl "--" 65) *)
no_notation NatArith.mult (infixl "*" 70)

(* no_notation NatDivision.dvd (infixl "dvd" 50) *)


(*----------------------------------------------------------------------------*)
(* The minus operator. *)


(*
The minus operator can be defined, instead of axiomatized, as follows.

minus(x) ==
    LET singletons == {<<u>>: u \in Nat}
    IN
        IF x \in Nat THEN
            <<x>>
        ELSE IF x \in Singletons THEN
            CHOOSE u \in Nat:  x = <<u>>
        ELSE
            CHOOSE u \notin (Nat \cup Singletons):  TRUE
*)
consts
    "minus" :: "[c] \<Rightarrow> c"  ("-._" [75] 75)

axiomatization where
    neg0 [simp]: "-.0 = 0"
and
    neg_neg: "n \<in> Nat \<or> -.n \<in> Nat ==>
        -.-.n = n"
and
    neg_not_in_nat:
        "n \<in> (Nat \<setminus> {0}) ==>
            -.n \<notin> Nat"


(*----------------------------------------------------------------------------*)
(* The set of integers. *)

definition Int
where "Int \<equiv>
    Nat \<union> {-.n:  n \<in> Nat}"


definition negNat :: "c"
where "negNat \<equiv> {-.n:  n \<in> Nat}"


(*----------------------------------------------------------------------------*)
(* Successor and predecessor on integers. *)

definition iSucc :: "c"
where "iSucc \<equiv>
    [i \<in> Int \<mapsto> IF i \<in> Nat THEN Succ[i]
        ELSE -.Pred[-.i]]"


definition iPred :: "c"
where "iPred \<equiv>
    [i \<in> Int \<mapsto> IF i \<in> Nat \<setminus> {0}
        THEN Pred[i]
        ELSE -.Succ[-.i]]"


(*----------------------------------------------------------------------------*)
(* Recursive definitions on the integers. *)

(* TODO: replace axiom with proof of existence. *)
axiomatization where
    primrec_int: "
        \<exists> f:
            isAFcn(f) \<and>
            DOMAIN f = Int \<and>
            f[0] = e \<and>
            (\<forall> n \<in> Nat:
                f[Succ[n]] = h(n, f[n]) \<and>
                f[-.Succ[n]] = g(n, f[-.n]))
            "

(*----------------------------------------------------------------------------*)
(* Arithmetic operators. *)


(* Incrementing and decrementing function. *)
definition addint :: "[c] \<Rightarrow> c"
where "addint(m) \<equiv>
    CHOOSE g \<in> [Int -> Int]:
        g[0] = m \<and>
        (\<forall> n \<in> Nat:
            g[Succ[n]] = iSucc[g[n]] \<and>
            g[-.Succ[n]] = iPred[g[-.n]])"


(* Addition on integers. *)
definition add :: "[c, c] \<Rightarrow> c" (infixl "+" 65)
where "add(m, n) \<equiv> addint(m)[n]"


(* Subtraction on integers. *)
definition diff :: "[c, c] \<Rightarrow> c" (infixl "-" 65)
where "diff(m, n) \<equiv> add(m, -.n)"


(* Adding and subtracting function. *)
definition multint :: "[c] \<Rightarrow> c"
where "multint(m) \<equiv>
    CHOOSE g \<in> [Int -> Int]:
        g[0] = 0 \<and>
        (\<forall> n \<in> Nat:
            g[Succ[n]] = add(g[n], m) \<and>
            g[-.Succ[n]] = add(g[-.n], -.m))"


(* Multiplication on integers. *)
definition mult :: "[c,c] \<Rightarrow> c" (infixl "*" 70)
where "mult(m, n) \<equiv> multint(m)[n]"


(* Divisibility on the integers. *)
definition dvd :: "[c, c] \<Rightarrow> c" (infixl "dvd" 50)
where "b dvd a \<equiv>
    \<exists> k \<in> Int:  a = mult(b, k)"


(* Order on the integers.
This definition is motivated by proofs, where equality is easier to
reason about (adding on both sides, multiplying both sides).
*)
definition leq :: "[c,c] \<Rightarrow> c" (infixl "<=" 50)
where "leq(m, n) \<equiv>
    \<exists> k \<in> Nat:
        add(m, k) = n"


abbreviation (input)
    geq :: "[c, c] \<Rightarrow> c" (infixl ">=" 50)
    where "geq(x, y) \<equiv> leq(y, x)"


definition less :: "[c, c] \<Rightarrow> c" (infixl "<" 50)
where "less(a, b) \<equiv> leq(a, b)
                            \<and> (a \<noteq> b)"


abbreviation (input)
    greater :: "[c, c] \<Rightarrow> c" (infixl ">" 50)
    where "greater(x, y) \<equiv> less(y, x)"


definition interval :: "[c, c] \<Rightarrow> c" ("(_ .. _)" [90,90] 70)
where "m .. n \<equiv>
    {k \\in Int:  m <= k \<and> k <= n}"

(*----------------------------------------------------------------------------*)


theorem minus_involutive[simp]:
    assumes "n \<in> Int"
    shows "-.-.n = n"
    proof -
    have s1_1: "n \<in> Nat \<or> (\<exists> k \<in> Nat:  n = -.k)"
        using assms by (auto simp: Int_def)
    have s1_2: "n \<in> Nat ==> -.-.n = n"
        using neg_neg by auto
    have s1_3: "n \<notin> Nat ==> -.-.n = n"
        proof -
        {
            assume s2_1: "n \<notin> Nat"
            have s2_2: "\<exists> k \<in> Nat:  n = -.k"
                using s1_1 s2_1 by auto
            have s2_3: "\<exists> k \<in> Nat:  -.n = -.-.k"
                using s2_2 by auto
            have s2_4: "\<exists> k \<in> Nat:  k = -.n"
                using s2_3 neg_neg by auto
            have s2_5: "-.n \<in> Nat"
                using s2_4 by auto
            have s2_6: "-.-.n = n"
                using s2_5 neg_neg by auto
        }
        from this show "n \<notin> Nat ==> -.-.n = n" by auto
        qed
    show "-.-.n = n" using s1_2 s1_3 by iprover
    qed


theorem minus_injective[dest]:
    assumes "-.n = -.m" and "n \<in> Int \<and> m \<in> Int"
    shows "n = m"
    proof -
    have "<1>1": "-.-.n = -.-.m"
        using assms by simp
    have "<1>2": "-.-.n = n"
        proof -
        have "<2>1": "n \<in> Int ==> -.-.n = n"
            using minus_involutive by auto
        have "<2>2": "n \<in> Int"
            using assms by auto
        show "-.-.n = n"
            using "<2>1" "<2>2" by auto
        qed
    have "<1>3": "-.-.m = m"
        proof -
        have "<2>1": "m \<in> Int ==> -.-.m = m"
            using minus_involutive by auto
        have "<2>2": "m \<in> Int"
            using assms by auto
        show "-.-.m = m"
            using "<2>1" "<2>2" by auto
        qed
    show "n = m"
        using "<1>1" "<1>2" "<1>3" by auto
    qed


theorem minus_eq:
    assumes "x = y"
    shows "-.x = -.y"
    using assms by auto


theorem neg_succ_not_in_nat[simp]:
    "n \<in> Nat ==>
        -.(Succ[n]) \<notin> Nat"
    proof -
    {
        fix "n"
        assume "<2>1": "n \<in> Nat"
        have "<2>2": "Succ[n] \<in> (Nat \<setminus> {0})"
            using "<2>1" by auto
        have "-.(Succ[n]) \<notin> Nat"
            using "<2>2" neg_not_in_nat by auto
    }
    from this show "n \<in> Nat ==>
            -.(Succ[n]) \<notin> Nat"
        by auto
    qed


theorem neg0_iff_eq0[simp]:
    "(-.n = 0) = (n = 0)"
    proof auto
    assume "<1>1": "-.n = 0"
    have "<1>2": "-.n \<in> Nat"
        using "<1>1" by auto
    have "<1>3": "-.-.n = n"
        using "<1>2" neg_neg by auto
    have "<1>4": "-.-.n = 0"
        using "<1>1" by auto
    show "n = 0"
        using "<1>3" "<1>4" by simp
    qed


theorem neg0_imp_eq0[dest]:
    "(-.n = 0) ==> (n = 0)"
    by simp


theorem not_neg0_imp_not0[dest]:
    "(-.n \<noteq> 0) ==> (n \<noteq> 0)"
    by simp


(*----------------------------------------------------------------------------*)
(* Properties of the set `Int`. *)


theorem nat_in_int[simp]:
    "n \<in> Nat ==> n \<in> Int"
    by (simp add: Int_def)


theorem minus_nat_in_int:
    "n \<in> Nat ==> -.n \<in> Int"
    by (auto simp: Int_def)


theorem minus_nat_in_neg_nat:
    "n \<in> Nat ==> -.n \<in> negNat"
    by (auto simp: negNat_def)


theorem neg_nat_in_int:
    "n \<in> negNat ==> n \<in> Int"
    by (auto simp: negNat_def Int_def)


theorem int_disj:
    "n \<in> Int ==>
        n \<in> Nat
        \<or> n \<in> {-.n:  n \<in> Nat}"
    by (auto simp: Int_def)


theorem int_disj_nat_negnat:
    "n \<in> Int ==>
        n \<in> Nat
        \<or> n \<in> negNat"
    unfolding negNat_def
    using int_disj by auto


theorem int_union_nat_negnat:
    "Int = Nat \<union> negNat"
    using int_disj_nat_negnat nat_in_int
        neg_nat_in_int
    by auto


theorem int_union_nat_0_negnat:
    "Int = (Nat \<setminus> {0}) \<union> negNat"
    proof -
    have s1_1: "Int = Nat \<union> negNat"
        using int_union_nat_negnat by auto
    have s1_2: "0 \<in> negNat"
        unfolding negNat_def
        using zeroIsNat neg0 by auto
    show ?thesis
        using s1_1 s1_2 by auto
    qed


theorem int_union_nat_negnat_0:
    "Int = Nat \<union> (negNat \<setminus> {0})"
    proof -
    have s1_1: "Int = Nat \<union> negNat"
        using int_union_nat_negnat by auto
    have s1_2: "0 \<in> Nat"
        using zeroIsNat by auto
    show ?thesis
        using s1_1 s1_2 by auto
    qed


theorem neg_int_eq_int[simp]:
        "n \<in> Int ==> -.n \<in> Int"
    unfolding Int_def by auto


theorem minus_negnat_in_int:
    "n \<in> negNat ==> -.n \<in> Int"
    using neg_nat_in_int neg_int_eq_int by auto


theorem minus_neg_int_in_nat:
        "n \<in> Int \<and> n \<notin> Nat ==>
            -.n \<in> Nat \<setminus> {0}"
    proof -
    assume "<1>1": "n \<in> Int \<and> n \<notin> Nat"
    have "<1>2": "n \<in> {-.k:  k \<in> Nat}"
        using "<1>1" int_disj by iprover
    have "<1>3": "\<exists> k \<in> Nat:  n = -.k"
        using "<1>2" by auto
    have "<1>4": "\<exists> k \<in> Nat:  k = -.n"
        using "<1>3" minus_involutive by auto
    have "<1>5": "-.n \<in> Nat"
        using "<1>4" by auto
    have "<1>6": "-.n \<noteq> 0"
        proof -
        {
        assume "<2>1": "-.n = 0"
        have "<2>2": "n = 0"
            using neg0 "<2>1" by auto
        have "<2>3": "n \<in> Nat"
            using "<2>2" by auto
        have "<2>4": "n \<notin> Nat"
            using "<1>1" by auto
        have "<2>5": "FALSE"
            using "<2>3" "<2>4" by auto
        }
        from this show "-.n \<noteq> 0"
            by auto
        qed
    show "-.n \<in> Nat \<setminus> {0}"
        using "<1>5" "<1>6" by auto
    qed


theorem neg_negative_in_nat:
    assumes hyp: "n \<in> Int \<and> n \<notin> Nat"
    shows "-. n \<in> Nat"
    proof -
    have int: "n \<in> Int"
        using hyp by auto
    from int int_disj have disj:
            "n \<in> Nat \<or> n \<in> {-. m:  m \<in> Nat}"
        by auto
    from disj hyp have neg: "n \<in> {-. m:  m \<in> Nat}"
        by auto
    from neg have ex1: "\<exists> m \<in> Nat:  n = -. m"
        by auto
    from ex1 have ex2: "\<exists> m \<in> Nat:  -. n = -. -. m"
        by auto
    from ex2 neg_neg have ex3: "\<exists> m \<in> Nat:  -. n = m"
        by auto
    from ex3 show "-. n \<in> Nat"
        by auto
    qed


theorem minus_nat_0_or_not_in_nat:
        "n \<in> Nat ==>
            -.n = 0 \<or> -.n \<notin> Nat"
    using neg0 neg_not_in_nat by auto


theorem int_eq_neg_int_is_0[simp]:
    "n \<in> Int ==> (n = -.n) = (n = 0)"
    proof -
    have "<1>1": "n \<in> Nat \<setminus> {0} ==>
            -.n \<notin> Nat"
        proof -
        assume "<2>1": "n \<in> Nat \<setminus> {0}"
        show "-.n \<notin> Nat"
            using neg_not_in_nat "<2>1" by auto
        qed
    have "<1>2": "n \<in> Nat \<setminus> {0} ==>
            n \<noteq> -.n"
        using "<1>1" by force
    have "<1>3": "n \<in> Int \<and> n \<notin> Nat
            ==> -.n \<in> Nat"
        using minus_neg_int_in_nat by auto
    have "<1>4": "n \<in> Int \<and> n \<notin> Nat
            ==> n \<noteq> -.n"
        using "<1>3" by force
    have "<1>5": "n \<in> Int \<setminus> {0} ==>
            (n \<in> Nat \<setminus> {0}) \<or>
            (n \<in> {-.k:  k \<in> Nat})"
        using int_disj by auto
    have "<1>6": "n \<in> Int \<setminus> {0} ==>
            (n \<noteq> -.n)"
        using "<1>2" "<1>4" "<1>5" by auto
    have "<1>7": "n \<in> Int \<and> (n \<noteq> 0) ==>
            (n \<noteq> -.n)"
        using "<1>6" by auto
    have "<1>8": "n \<in> Int \<and> (n = -.n) ==>
            (n = 0)"
        using "<1>7" by auto
    have "<1>9": "n \<in> Int \<and> (n = 0) ==>
            (n = -.n)"
        using neg0 by auto
    show "n \<in> Int ==> (n = -.n) = (n = 0)"
        using "<1>8" "<1>9" by auto
    qed


theorem minus_neg_nat_in_nat:
    assumes hyp: "n \<in> negNat"
    shows "-.n \<in> Nat"
    proof -
    have s1_1: "\<exists> k \<in> Nat:  -.k = n"
        using hyp by (auto simp: negNat_def)
    have s1_2: "\<exists> k \<in> Nat:  -.-.k = -.n"
        using s1_1 by auto
    have s1_3: "\<exists> k \<in> Nat:  k = -.n"
        using s1_2 neg_neg by auto
    show "-.n \<in> Nat"
        using s1_3 by auto
    qed


theorem minus_neg_nat_0_in_nat_0:
    assumes hyp: "n \<in> negNat \<setminus> {0}"
    shows "-.n \<in> Nat \<setminus> {0}"
    proof -
    have s1_1: "-.n \<in> Nat"
        using hyp minus_neg_nat_in_nat by auto
    have s1_2: "-.n \<noteq> 0"
        proof -
        {
        assume s2_1: "-.n = 0"
        have s2_2: "-.-.n = -.0"
            using s2_1 by auto
        have s2_3: "-.-.n = 0"
            using s2_2 neg0 by auto
        have s2_4: "n = 0"
            proof -
            have s3_1: "n \<in> Int"
                using hyp neg_nat_in_int by auto
            have s3_2: "-.-.n = n"
                using s3_1 minus_involutive
                by auto
            show ?thesis
                using s3_2 s2_3 by auto
            qed
        have s2_5: "n \<noteq> 0"
            using hyp by auto
        have "FALSE"
            using s2_4 s2_5 by auto
        }
        from this show ?thesis
            by auto
        qed
    show ?thesis
        using s1_1 s1_2 by auto
    qed


theorem neg_nat_0_not_in_nat:
    assumes hyp: "n \<in> negNat \<setminus> {0}"
    shows "n \<notin> Nat"
    proof auto
    assume s1_1: "n \<in> Nat"
    have s1_2: "n \<noteq> 0"
        using hyp by auto
    have s1_3: "n \<in> Nat \<setminus> {0}"
        using s1_1 s1_2 by auto
    have s1_4: "-.n \<notin> Nat"
        using s1_3 neg_not_in_nat by auto
    have s1_5: "-.n \<in> Nat"
        using hyp minus_neg_nat_in_nat by auto
    show "FALSE"
        using s1_4 s1_5 by auto
    qed


theorem neg_nat_not_in_nat_setminus_0:
    assumes hyp: "n \<in> negNat"
    shows "n \<notin> Nat \<setminus> {0}"
    proof -
    have s1_1: "n \<in> negNat ==>
        n \<in> negNat \<setminus> {0}
        \<or> n = 0"
        by auto
    have s1_2: "n \<in> negNat \<setminus> {0}
        ==> n \<notin> Nat \<setminus> {0}"
        using neg_nat_0_not_in_nat by auto
    have s1_3: "n = 0 ==>
        n \<notin> Nat \<setminus> {0}"
        by auto
    show "n \<notin> Nat \<setminus> {0}"
        using hyp s1_1 s1_2 s1_3 by iprover
    qed


theorem minus_nat_0_in_negnat_0:
    assumes hyp: "n \<in> Nat \<setminus> {0}"
    shows "-.n \<in> negNat \<setminus> {0}"
    proof -
    have s1_1: "n \<in> Nat"
        using hyp by auto
    have s1_2: "-.n \<in> negNat"
        using s1_1 minus_nat_in_neg_nat by auto
    have s1_3: "-.n \<noteq> 0"
        proof -
        {
        assume s2_1: "-.n = 0"
        have s2_2: "-.-.n = -.0"
            using s2_1 by auto
        have s2_3: "-.-.n = 0"
            using s2_2 by auto
        have s2_4: "n = 0"
            using s1_1 neg_neg s2_3 by auto
        have s2_5: "n \<noteq> 0"
            using hyp by auto
        have "FALSE"
            using s2_4 s2_5 by auto
        }
        from this show ?thesis
            by auto
        qed
    show ?thesis
        using s1_2 s1_3 by auto
    qed


theorem minus_one_in_negnat:
    "-.1 \\in negNat"
    unfolding negNat_def
    using oneIsNat by auto


theorem minus_one_in_int:
    "-.1 \\in Int"
    using minus_one_in_negnat neg_nat_in_int by auto


theorem minus_one_neq_0:
    "-.1 \<noteq> 0"
    proof -
    {
    assume s1_1: "-.1 = 0"
    have s1_2: "-.-.1 = -.0"
        using s1_1 by auto
    have s1_3: "-.-.1 = 0"
        using s1_2 neg0 by auto
    have s1_4: "0 \<in> Nat"
        by auto
    have s1_5: "1 = 0"
        using s1_3 s1_4 by auto
    have "FALSE"
        using s1_5 succIrrefl
        by auto
    }
    from this show "-.1 \<noteq> 0"
        by auto
    qed


theorem minus_minus_one:
    "-.-.1 = 1"
    proof -
    have s1_1: "1 \<in> Nat"
        using oneIsNat by auto
    show "-.-.1 = 1"
        using neg_neg s1_1 by auto
    qed


theorem succ_zero_equality:
    assumes hyp: "x = Succ[0]"
    shows "x = 1"
    using hyp by auto


theorem pred_1:
    "Pred[1] = 0"
    proof -
    have s1_1: "1 = Succ[0]"
        by auto
    have s1_2: "\<forall> x \<in> Nat:  (1 = Succ[x]) => (x = 0)"
        using s1_1 succInjIff by auto
    show ?thesis
        using s1_1 s1_2 choose_equality by auto
    qed


theorem pred_2:
    "Pred[2] = 1"
    proof -
    have s1_1: "1 \\in Nat \<and> Succ[1] = 2"
        unfolding two_def
        using oneIsNat by auto
    have s1_2: "\<And> x.  x \\in Nat \<and> (Succ[x] = 2) ==> (x = 1)"
        using oneIsNat succInjIff by (auto simp: two_def)
    have s1_4: "Pred[2] = (CHOOSE x:  x \\in Nat \<and> Succ[x] = 2)"
        proof -
        have s2_1: "Pred[2] =
            (IF 2 = 0 THEN 0 ELSE CHOOSE x \<in> Nat:  2 = Succ[x])"
            unfolding Pred_def
            using twoIsNat by auto
        also have s2_2: "... = (CHOOSE x \<in> Nat:  2 = Succ[x])"
            proof -
            have s3_1: "2 \<noteq> 0"
                using succNotZero by (auto simp: two_def)
            show ?thesis
                using s3_1 by auto
            qed
        also have s2_3: "... = (CHOOSE x:  x \\in Nat \<and> 2 = Succ[x])"
            unfolding bChoose_def
            by auto
        also have s2_4: "... = (CHOOSE x:  x \\in Nat \<and> Succ[x] = 2)"
            proof -
            have s3_1: "\<And> x.  (2 = Succ[x]) = (Succ[x] = 2)"
                by auto
            show ?thesis
                using s3_1 by auto
            qed
        finally show ?thesis .
        qed
    show ?thesis
        using s1_1 s1_2 s1_4 choose_equality[
            of "\<lambda> x.  x \\in Nat \<and> Succ[x] = 2"
            "1" "1"]
            by auto
    qed


theorem zero_in_int:
    "0 \<in> Int"
    using zeroIsNat nat_in_int by auto


theorem ipred_0:
    shows "iPred[0] = -.1"
    proof -
    have s1_1: "iPred[0] = -.Succ[-.0]"
        proof -
        have s2_1: "0 \<in> Int"
            using zero_in_int by auto
        have s2_2: "0 \<notin> Nat \<setminus> {0}"
            by auto
        show ?thesis
            unfolding iPred_def
            using s2_1 s2_2 by auto
        qed
    also have s1_2: "... = -.Succ[0]"
        using neg0 by auto
    also have s1_3: "... = -.1"
        by auto
    show ?thesis
        using s1_1 s1_2 s1_3 by auto
    qed


theorem isucc_minus_1:
    "iSucc[-.1] = 0"
    unfolding iSucc_def
    using oneIsNat neg_neg pred_1 neg0 by auto


theorem negnat_succ_in_nat:
    assumes ndom: "n \\in negNat"
    shows "Succ[-.n] \\in Nat"
    using ndom minus_neg_nat_in_nat succIsNat by auto


theorem minus_negnat_succ_in_negnat:
    assumes ndom: "n \\in negNat"
    shows "-.Succ[-.n] \\in negNat"
    using ndom negnat_succ_in_nat minus_nat_in_neg_nat by auto


theorem minus_succ_minus_negnat_in_int:
    assumes ndom: "n \\in negNat"
    shows "-.Succ[-.n] \\in Int"
    proof -
    have s1_1: "-.n \\in Nat"
        using ndom minus_neg_nat_in_nat by auto
    have s1_2: "Succ[-.n] \\in Nat"
        using s1_1 succIsNat by auto
    show ?thesis
        using s1_2 minus_nat_in_int by auto
    qed

(*----------------------------------------------------------------------------*)
(* `iSucc` and `iPred` properties. *)

(* Typeness *)
theorem iSucc_type:
    assumes idom: "i \<in> Int"
    shows "iSucc[i] \<in> Int"
    proof -
    have s1_1: "i \<in> Nat ==>
        iSucc[i] \<in> Int"
        proof -
        assume s2_1: "i \<in> Nat"
        have s2_2: "iSucc[i] = Succ[i]"
            unfolding iSucc_def
            using s2_1 by auto
        have s2_3: "Succ[i] \<in> Nat"
            using s2_1 succIsNat by auto
        have s2_4: "Succ[i] \<in> Int"
            using s2_3 nat_in_int by auto
        show "iSucc[i] \<in> Int"
            using s2_2 s2_4 by auto
        qed
    have s1_2: "i \<notin> Nat ==>
        iSucc[i] \<in> Int"
        proof -
        assume s2_1: "i \<notin> Nat"
        have s2_2: "iSucc[i] = -.Pred[-.i]"
            unfolding iSucc_def
            using s2_1 idom by auto
        have s2_3: "Pred[-.i] \<in> Nat"
            proof -
            have s3_1: "-.i \<in> Nat"
                using idom s2_1 minus_neg_int_in_nat
                by auto
            show "Pred[-.i] \<in> Nat"
                using s3_1 Pred_in_nat by auto
            qed
        have s2_4: "-.Pred[-.i] \<in> Int"
            using s2_3 minus_nat_in_int by auto
        show "iSucc[i] \<in> Int"
            using s2_2 s2_4 by auto
        qed
    show "iSucc[i] \<in> Int"
        using s1_1 s1_2 by auto
    qed


theorem iPred_type:
    assumes idom: "i \<in> Int"
    shows "iPred[i] \<in> Int"
    proof -
    have s1_1: "i \<in> Nat \<setminus> {0}
        ==> iPred[i] \<in> Int"
        proof -
        assume s2_1: "i \<in> Nat \<setminus> {0}"
        have s2_2: "iPred[i] = Pred[i]"
            unfolding iPred_def
            using idom s2_1 by auto
        have s2_3: "Pred[i] \<in> Nat"
            using s2_1 Pred_in_nat by auto
        have s2_4: "Pred[i] \<in> Int"
            using s2_3 nat_in_int by auto
        show "iPred[i] \<in> Int"
            using s2_2 s2_4 by auto
        qed
    have s1_2: "i = 0 ==>
        iPred[i] \<in> Int"
        proof -
        assume s2_1: "i = 0"
        have s2_2: "iPred[i] = -.1"
            unfolding iPred_def
            using idom s2_1 by auto
        have s2_3: "-.1 \<in> Int"
            using oneIsNat by (auto simp: Int_def)
        show "iPred[i] \<in> Int"
            using s2_2 s2_3 by auto
        qed
    have s1_3: "i \<notin> Nat ==>
        iPred[i] \<in> Int"
        proof -
        assume s2_1: "i \<notin> Nat"
        have s2_2: "iPred[i] = -.Succ[-.i]"
            unfolding iPred_def
            using idom s2_1 by auto
        have s2_3: "-.Succ[-.i] \<in> Int"
            proof -
            have s3_1: "-.i \<in> Nat"
                using idom s2_1 minus_neg_int_in_nat
                by auto
            have s3_2: "Succ[-.i] \<in> Nat"
                using s3_1 succIsNat by auto
            show "-.Succ[-.i] \<in> Int"
                using s3_2 minus_nat_in_int by auto
            qed
        show "iPred[i] \<in> Int"
            using s2_2 s2_3 by auto
        qed
    show "iPred[i] \<in> Int"
        using s1_1 s1_2 s1_3 by auto
    qed


(*
THEOREM iSucciPredCommute ==
        \A i \in Int:  iSucc[iPred[i]] = iPred[iSucc[i]]
    PROOF
    <1>1. SUFFICES ASSUME NEW i \in Int
                   PROVE iSucc[iPred[i]] = iPred[iSucc[i]]
        BY <1>1
    <1>2. CASE i \in Nat \ {0}
        <2>1. iSucc[iPred[i]] = i
            <3>1. iPred[i] = Pred[i]
                <4>1. i \in Nat \ {0}
                    BY <1>2
                <4> QED
                    BY <4>1 DEF iPred
            <3>2. iSucc[iPred[i]] = Succ[Pred[i]]
                <4>1. Pred[i] \in Nat
                    <5>1. i \in Nat
                        BY <1>2
                    <5> QED
                        BY <5>1, Pred_in_nat
                <4> QED
                    BY <3>1, <4>1 DEF iSucc
            <3>3. Succ[Pred[i]] = i
                <4>1. i \in Nat \ {0}
                    BY <1>2
                <4> QED
                    BY <4>1, Succ_Pred_nat
            <3> QED
                BY <3>2, <3>3
        <2>2. iPred[iSucc[i]] = i
            <3>1. iSucc[i] = Succ[i]
                <4>1. i \in Nat
                    BY <1>2
                <4> QED
                    BY <4>1 DEF iSucc
            <3>2. iPred[iSucc[i]] = Pred[Succ[i]]
                <4>1. Succ[i] \in Nat
                    <5>1. i \in Nat
                        BY <1>2
                    <5> QED
                        BY <5>1, succIsNat
                <4>2. Succ[i] # 0
                    BY <1>2, succNotZero
                <4>3. Succ[i] \in Nat \ {0}
                    BY <4>1, <4>2
                <4>4. iPred[Succ[i]] = Pred[Succ[i]]
                    BY <4>3 DEF iPred
                <4> QED
                    BY <4>4, <3>1
            <3>3. Pred[Succ[i]] = i
                <4>1. i \in Nat
                    BY <1>2
                <4> QED
                    BY <4>1, Pred_Succ_nat
            <3> QED
                BY <3>2, <3>3
        <2> QED
            BY <2>1, <2>2
    <1>3. CASE i = 0
        <2>1. iSucc[iPred[i]] = 0
            <3>1. iSucc[iPred[i]] = iSucc[-.1]
                <4>1. iPred[i] = -.1
                    BY <1>3 DEF iPred
                <4> QED
                    BY <4>1
            <3>2. iSucc[-.1] = -.Pred[-.-.1]
                <4>1. -.1 \in Int
                    <5>1. -.1 \in negNat
                        BY oneIsNat DEF negNat
                    <5> QED
                        BY <5>1, neg_nat_in_int
                <4>2. -.1 \notin Nat
                    <5>1. -.1 \in negNat \ {0}
                        <6>1. -.1 # 0
                            BY minus_one_neq_0
                        <6>2. -.1 \in negNat
                            BY oneIsNat DEF negNat
                        <6> QED
                            BY <6>1, <6>2
                    <5> QED
                        BY <5>1, neg_nat_0_not_in_nat
                <4> QED
                    BY <4>1, <4>2 DEF iSucc
            <3>3. -.Pred[-.-.1] = 0
                <4>1. -.-.1 = 1
                    BY minus_minus_one
                <4>2. Pred[1] = 0
                    BY pred_1
                <4>3. -.0 = 0
                    BY neg0
                <4> QED
                    BY <4>1, <4>2, <4>3
            <3> QED
                BY <3>1, <3>2, <3>3
        <2>2. iPred[iSucc[i]] = 0
            <3>1. iSucc[i] = 1
                <4>1. i \in Nat
                    BY <1>3, zeroIsNat
                <4>2. iSucc[i] = Succ[i]
                    BY <4>1 DEF iSucc
                <4>3. Succ[i] = Succ[0]
                    BY <1>3
                <4>4. Succ[0] = 1
                    OBVIOUS
                <4> QED
                    BY <4>2, <4>3, <4>4
            <3>2. iPred[1] = 0
                <4>1. 1 \in Nat \ {0}
                    BY oneIsNat, succIrrefl
                <4>2. iPred[1] = Pred[1]
                    BY <4>1 DEF iPred
                <4>3. Pred[1] = 0
                    BY pred_1
                <4> QED
                    BY <4>2, <4>3
            <3> QED
                BY <3>1, <3>2
        <2> QED
            BY <2>1, <2>2
    <1>4. CASE i \in negNat
        <2>1. iSucc[iPred[i]] = i
            <3>1. iPred[i] = -.Succ[-.i]
                <4>1. i \in Int
                    BY <1>1
                <4>2. i \notin Nat \ {0}
                    BY <1>4, neg_nat_not_in_nat_setminus_0
                <4> QED
                    BY <4>1, <4>2 DEF iPred
            <3>2. -.Succ[-.i] \in negNat \ {0}
                <4>1. Succ[-.i] \in Nat \ {0}
                    <5>1. -.i \<in> Nat
                        BY <1>4, minus_neg_nat_in_nat
                    <5>2. Succ[-.i] \in Nat
                        BY <5>1, succIsNat
                    <5>3. Succ[-.i] \<noteq> 0
                        BY <5>1, succNotZero
                    <5> QED
                        BY <5>2, <5>3
                <4> QED
                    BY <4>1, minus_nat_0_in_negnat_0
            <3>3. iSucc[iPred[i]] = -.Pred[-.-.Succ[-.i]]
                <4>1. iPred[i] \in negNat \ {0}
                    BY <3>1, <3>2
                <4>2. iPred[i] \in Int
                    BY <4>1, neg_nat_in_int
                <4>3. iPred[i] \notin Nat
                    BY <4>1, neg_nat_0_not_in_nat
                <4>4. iSucc[iPred[i]] = -.Pred[-.iPred[i]]
                    BY <4>2, <4>3 DEF iSucc
                <4> QED
                    BY <4>4, <3>1
            <3>4. @ = -.Pred[Succ[-.i]]
                <4>1. -.i \in Nat
                    BY <1>4, minus_neg_nat_in_nat
                <4>2. Succ[-.i] \in Int
                    BY <4>1, succIsNat, nat_in_int
                <4>3. -.-.Succ[-.i] = Succ[-.i]
                    BY minus_involutive
                <4> QED
                    BY <4>3
            <3>5. @ = -.-.i
                <4>1. -.i \in Nat
                    BY <1>4, minus_neg_nat_in_nat
                <4>2. Pred[Succ[-.i]] = -.i
                    BY <4>1, Pred_Succ_nat
                <4> QED
                    BY <4>2
            <3>6. @ = i
                BY <1>4, minus_involutive
            <3> QED
                BY <3>3, <3>4, <3>5, <3>6
        <2>2. iPred[iSucc[i]] = i
            <3>1. CASE i = 0
                <4>1. iSucc[i] = 1
                    <5>1. 0 \in Nat
                        BY zeroIsNat
                    <5>2. 0 \in Int
                        BY <5>1, nat_in_int
                    <5>3. iSucc[i] = Succ[0]
                        BY <5>1, <5>2, <3>1 DEF iSucc
                    <5>4. Succ[0] = 1
                        OBVIOUS
                    <5> QED
                        BY <5>3, <5>4
                <4>2. iPred[1] = 0
                    <5>1. 1 \in Nat \ {0}
                        BY oneIsNat, succNotZero
                    <5>2. 1 \in Int
                        BY <5>1, nat_in_int
                    <5>3. iPred[1] = Pred[1]
                        BY <5>1, <5>2 DEF iPred
                    <5>4. Pred[1] = 0
                        BY pred_1
                    <5> QED
                        BY <5>3, <5>4
                <4> QED
                    BY <4>1, <4>2, <3>1
            <3>2. CASE i # 0
                <4>1. i \in negNat \ {0}
                    BY <1>4, <3>1
                <4>2. i \notin Nat
                    BY <4>1, neg_nat_0_not_in_nat
                <4>3. i \in Int
                    BY <4>1, neg_nat_in_int
                <4>4. iSucc[i] = -.Pred[-.i]
                    BY <4>2, <4>3 DEF iSucc
                <4>5. -.Pred[-.i] \in negNat
                    <5>1. -.i \in Nat
                        BY <4>1, minus_neg_nat_in_nat
                    <5>2. Pred[-.i] \in Nat
                        BY <5>1, Pred_in_nat
                    <5> QED
                        BY <5>2, minus_nat_in_neg_nat
                <4>6. -.Pred[-.i] \in Int
                    BY <4>5, neg_nat_in_int
                <4>7. -.Pred[-.i] \notin Nat \ {0}
                    BY <4>5, neg_nat_not_in_nat_setminus_0
                <4>8. iPred[-.Pred[-.i]] = -.Succ[-.-.Pred[-.i]]
                    BY <4>6, <4>7 DEF iPred
                <4>9. -.Succ[-.-.Pred[-.i]] = i
                    <5>1. -.-.Pred[-.i] = Pred[-.i]
                        <6>1. -.i \in Nat
                            BY <4>1, minus_neg_nat_in_nat
                        <6>2. Pred[-.i] \in Nat
                            BY <6>1, Pred_in_nat
                        <6>3. Pred[-.i] \in Int
                            BY <6>2, nat_in_int
                        <6> QED
                            BY <6>3, minus_involutive
                    <5>2. Succ[Pred[-.i]] = -.i
                        <6>1. -.i \in Nat \ {0}
                            BY <4>1, minus_neg_nat_0_in_nat_0
                        <6> QED
                            BY <6>1, Succ_Pred_nat
                    <5>3. -.-.i = i
                        BY <4>3, minus_involutive
                    <5> QED
                        BY <5>1, <5>2, <5>3
                <4> QED
                    BY <4>4, <4>8, <4>9
            <3> QED
                BY <3>1, <3>2
        <2> QED
            BY <2>1, <2>2
    <1> QED
        BY <1>1, <1>2, <1>3, <1>4
*)
theorem iSucciPredCommute:
    "\<forall> i \<in> Int:
        iSucc[iPred[i]] = iPred[iSucc[i]] \<and>
        iSucc[iPred[i]] = i \<and>
        iPred[iSucc[i]] = i
        "
    proof -
    {
    fix "i" :: "c"
    assume s1_1: "i \<in> Int"
    have s1_2: "i \<in> Nat \<setminus> {0} ==>
        iSucc[iPred[i]] = iPred[iSucc[i]] \<and>
        iSucc[iPred[i]] = i \<and>
        iPred[iSucc[i]] = i
        "
        proof -
        assume idom: "i \<in> Nat \<setminus> {0}"
        have s2_1: "iSucc[iPred[i]] = i"
            proof -
            have s3_1: "iPred[i] = Pred[i]"
                unfolding iPred_def
                using s1_1 idom by auto
            have s3_2: "iSucc[iPred[i]] = Succ[Pred[i]]"
                proof -
                have s4_1: "Pred[i] \<in> Nat"
                    proof -
                    have s5_1: "i \<in> Nat"
                        using idom by auto
                    show ?thesis
                        using s5_1 Pred_in_nat by auto
                    qed
                show ?thesis
                    unfolding iSucc_def
                    using s4_1 s3_1 by auto
                qed
            have s3_3: "Succ[Pred[i]] = i"
                using idom Succ_Pred_nat
                by auto
            show ?thesis
                using s3_2 s3_3 by auto
            qed
        have s2_2: "iPred[iSucc[i]] = i"
            proof -
            have s3_1: "iSucc[i] = Succ[i]"
                unfolding iSucc_def
                using s1_1 idom by auto
            have s3_2: "iPred[iSucc[i]] = Pred[Succ[i]]"
                proof -
                have s4_1: "Succ[i] \<in> Nat"
                    proof -
                    have s5_1: "i \<in> Nat"
                        using idom by auto
                    show ?thesis
                        using s5_1 succIsNat by auto
                    qed
                have s4_2: "Succ[i] \<noteq> 0"
                    using idom succNotZero by auto
                have s4_3: "Succ[i] \<in> Nat \<setminus> {0}"
                    using s4_1 s4_2 by auto
                have s4_4: "Succ[i] \<in> Int"
                    using s4_1 nat_in_int by auto
                have s4_5: "iPred[Succ[i]] = Pred[Succ[i]]"
                    unfolding iPred_def
                    using s4_3 s4_4 by auto
                show ?thesis
                    using s4_5 s3_1 by auto
                qed
            have s3_3: "Pred[Succ[i]] = i"
                proof -
                have s4_1: "i \<in> Nat"
                    using idom by auto
                show ?thesis
                    using s4_1 Pred_Succ_nat
                    by auto
                qed
            show ?thesis
                using s3_2 s3_3 by auto
            qed
        show ?thesis
            using s2_1 s2_2
            by auto
        qed
    have s1_3: "i \<in> negNat ==>
        iSucc[iPred[i]] = iPred[iSucc[i]] \<and>
        iSucc[iPred[i]] = i \<and>
        iPred[iSucc[i]] = i
        "
        proof -
        assume idom: "i \<in> negNat"
        have s2_1: "iSucc[iPred[i]] = i"
            proof -
            have s3_1: "iPred[i] = -.Succ[-.i]"
                proof -
                have s4_1: "i \<in> Int"
                    using s1_1 by auto
                have s4_2: "i \<notin> Nat \<setminus> {0}"
                    using idom neg_nat_not_in_nat_setminus_0
                    by auto
                show ?thesis
                    unfolding iPred_def
                    using s4_1 s4_2 by auto
                qed
            have s3_2: "-.Succ[-.i] \<in> negNat \<setminus> {0}"
                proof -
                have s4_1: "Succ[-.i] \<in> Nat \<setminus> {0}"
                    proof -
                    have s5_1: "-.i \<in> Nat"
                        using idom minus_neg_nat_in_nat
                        by auto
                    have s5_2: "Succ[-.i] \<in> Nat"
                        using s5_1 succIsNat by auto
                    have s5_3: "Succ[-.i] \<noteq> 0"
                        using s5_1 succNotZero by auto
                    show ?thesis
                        using s5_2 s5_3 by auto
                    qed
                show ?thesis
                    using s4_1 minus_nat_0_in_negnat_0
                    by auto
                qed
            have s3_3: "iSucc[iPred[i]] = -.Pred[-.-.Succ[-.i]]"
                proof -
                have s4_1: "iPred[i] \<in> negNat \<setminus> {0}"
                    using s3_1 s3_2 by auto
                have s4_2: "iPred[i] \<in> Int"
                    using s4_1 neg_nat_in_int by auto
                have s4_3: "iPred[i] \<notin> Nat"
                    using s4_1 neg_nat_0_not_in_nat by auto
                have s4_4: "iSucc[iPred[i]] = -.Pred[-.iPred[i]]"
                    unfolding iSucc_def
                    using s4_2 s4_3 by auto
                show ?thesis
                    using s4_4 s3_1 by auto
                qed
            have s3_4: "-.Pred[-.-.Succ[-.i]] = -.Pred[Succ[-.i]]"
                proof -
                have s4_1: "-.i \<in> Nat"
                    using idom minus_neg_nat_in_nat by auto
                have s4_2: "Succ[-.i] \<in> Int"
                    using s4_1 succIsNat nat_in_int by auto
                have s4_3: "-.-.Succ[-.i] = Succ[-.i]"
                    using s4_2 minus_involutive by auto
                show ?thesis
                    using s4_3 by auto
                qed
            have s3_5: "-.Pred[Succ[-.i]] = -.-.i"
                proof -
                have s4_1: "-.i \<in> Nat"
                    using idom minus_neg_nat_in_nat by auto
                have s4_2: "Pred[Succ[-.i]] = -.i"
                    using s4_1 Pred_Succ_nat by auto
                show ?thesis
                    using s4_2 by auto
                qed
            have s3_6: "-.-.i = i"
                using s1_1 minus_involutive by auto
            show ?thesis
                using s3_3 s3_4 s3_5 s3_6 by auto
            qed
        have s2_2: "iPred[iSucc[i]] = i"
            proof -
            have s3_1: "i = 0 ==>
                iPred[iSucc[i]] = i"
                proof -
                assume i0: "i = 0"
                have s4_1: "iSucc[i] = 1"
                    proof -
                    have s5_1: "0 \<in> Nat"
                        using zeroIsNat by auto
                    have s5_2: "0 \<in> Int"
                        using s5_1 nat_in_int by auto
                    have s5_3: "iSucc[i] = Succ[0]"
                        unfolding iSucc_def
                        using s5_1 s5_2 i0
                        by auto
                    have s5_4: "Succ[0] = 1"
                        by auto
                    show ?thesis
                        using s5_3 s5_4 by auto
                    qed
                have s4_2: "iPred[1] = 0"
                    proof -
                    have s5_1: "1 \<in> Nat \<setminus> {0}"
                        using oneIsNat succNotZero
                        by auto
                    have s5_2: "1 \<in> Int"
                        using s5_1 nat_in_int by auto
                    have s5_3: "iPred[1] = Pred[1]"
                        unfolding iPred_def
                        using s5_1 s5_2
                        by auto
                    have s5_4: "Pred[1] = 0"
                        using pred_1 by auto
                    show ?thesis
                        using s5_3 s5_4 by auto
                    qed
                show "iPred[iSucc[i]] = i"
                    using s4_1 s4_2 i0 by auto
                qed
            have s3_2: "i \<noteq> 0 ==>
                iPred[iSucc[i]] = i"
                proof -
                assume inot0: "i \<noteq> 0"
                have s4_1: "i \<in> negNat \<setminus> {0}"
                    using idom inot0 by auto
                have s4_2: "i \<notin> Nat"
                    using s4_1 neg_nat_0_not_in_nat
                    by auto
                have s4_3: "i \<in> Int"
                    using s4_1 neg_nat_in_int
                    by auto
                have s4_4: "iSucc[i] = -.Pred[-.i]"
                    unfolding iSucc_def
                    using s4_2 s4_3 by auto
                have s4_5: "-.Pred[-.i] \<in> negNat"
                    proof -
                    have s5_1: "-.i \<in> Nat"
                        using s4_1 minus_neg_nat_in_nat
                        by auto
                    have s5_2: "Pred[-.i] \<in> Nat"
                        using s5_1 Pred_in_nat
                        by auto
                    show ?thesis
                        using s5_2 minus_nat_in_neg_nat
                        by auto
                    qed
                have s4_6: "-.Pred[-.i] \<in> Int"
                    using s4_5 neg_nat_in_int
                    by auto
                have s4_7: "-.Pred[-.i] \<notin> Nat \<setminus> {0}"
                    using s4_5 neg_nat_not_in_nat_setminus_0
                    by blast
                have s4_8: "iPred[-.Pred[-.i]] = -.Succ[-.-.Pred[-.i]]"
                    unfolding iPred_def
                    using s4_6 s4_7 by auto
                have s4_9: "-.Succ[-.-.Pred[-.i]] = i"
                    proof -
                    have s5_1: "-.-.Pred[-.i] = Pred[-.i]"
                        proof -
                        have s6_1: "-.i \<in> Nat"
                            using s4_1 minus_neg_nat_in_nat
                            by auto
                        have s6_2: "Pred[-.i] \<in> Nat"
                            using s6_1 Pred_in_nat
                            by auto
                        have s6_3: "Pred[-.i] \<in> Int"
                            using s6_2 nat_in_int
                            by auto
                        show ?thesis
                            using s6_3 minus_involutive
                            by auto
                        qed
                    have s5_2: "Succ[Pred[-.i]] = -.i"
                        proof -
                        have s6_1: "-.i \<in> Nat \<setminus> {0}"
                            using s4_1 minus_neg_nat_0_in_nat_0
                            by auto
                        show ?thesis
                            using s6_1 Succ_Pred_nat
                            by auto
                        qed
                    have s5_3: "-.-.i = i"
                        using s4_3 minus_involutive by auto
                    show ?thesis
                        using s5_1 s5_2 s5_3 by auto
                    qed
                show "iPred[iSucc[i]] = i"
                    using s4_4 s4_8 s4_9 by auto
                qed
            show ?thesis
                using s3_1 s3_2 by auto
            qed
        show "iSucc[iPred[i]] = iPred[iSucc[i]] \<and>
            iSucc[iPred[i]] = i \<and>
            iPred[iSucc[i]] = i"
            using s2_1 s2_2 by auto
        qed
    have s1_4: "Int = (Nat \<setminus> {0}) \<union> negNat"
        using int_union_nat_0_negnat by auto
    have "iSucc[iPred[i]] = iPred[iSucc[i]] \<and>
        iSucc[iPred[i]] = i \<and>
        iPred[iSucc[i]] = i"
        using s1_1 s1_2 s1_3 s1_4 by auto
    }
    from this show ?thesis
        using allI by auto
    qed


(*
THEOREM iSuccMinusFlip ==
    \A i \in Int:  -.iSucc[-.i] = iPred[i]
PROOF
<1>1. SUFFICES
        ASSUME NEW i \in Int
        PROVE -.iSucc[-.i] = iPred[i]
    BY <1>1
<1>2. CASE i \in Nat \ {0}
    <2>1. i \in Int
        BY <1>2, nat_in_int
    <2>2. -.iSucc[-.i] = Pred[i]
        <3>1. -.iSucc[-.i] = -.-.Pred[-.-.i]
            <4>1. -.i \in negNat \ {0}
                BY <1>2, minus_nat_0_in_negnat_0
            <4>2. -.i \notin Nat
                BY <4>1, neg_nat_0_not_in_nat
            <4> QED
                BY <2>1, <4>2 DEF iSucc
        <3>2. @ = -.-.Pred[i]
            <4>1. -.-.i = i
                BY <2>1, minus_involutive
            <4> QED
                BY <4>1
        <3>3. @ = Pred[i]
            <4>1. Pred[i] \in Nat
                BY <1>2, Pred_in_nat
            <4>2. Pred[i] \in Int
                BY <4>1, nat_in_int
            <4> QED
                BY <4>2, minus_involutive
        <3> QED
            BY <3>1, <3>2, <3>3
    <2>3. iPred[i] = Pred[i]
        BY <2>1, <1>2 DEF iPred
    <2> QED
        BY <2>2, <2>3
<1>3. CASE i \in negNat
    <2>1. i \in Int
        BY <1>3, neg_nat_in_int
    <2>2. i \notin Nat \ {0}
        BY <1>3, neg_nat_not_in_nat_setminus_0
    <2>3. Pred[i] = -.Succ[-.i]
        BY <2>1, <2>2 DEF iPred
    <2>4. -.iSucc[-.i] = -.Succ[-.i]
        <3>1. -.i \in Nat
            BY <1>3, minus_neg_nat_in_nat
        <3>2. -.i \in Int
            BY <3>1, nat_in_int
        <3> QED
            BY <3>1, <3>2 DEF iSucc
    <2> QED
        BY <2>3, <2>4
<1> QED
    BY <1>1, <1>2, <1>3, int_union_nat_0_negnat
*)
theorem iSuccMinusFlip:
    "\<forall> i \<in> Int:
        -.iSucc[-.i] = iPred[i]"
    proof auto
    fix "i" :: "c"
    assume s1_1: "i \<in> Int"
    have s1_2: "i \<in> Nat \<setminus> {0} ==>
        -.iSucc[-.i] = iPred[i]"
        proof -
        assume s1_2_asm: "i \<in> Nat \<setminus> {0}"
        have s2_1: "i \<in> Int"
            using s1_2_asm nat_in_int
            by auto
        have s2_2: "-.iSucc[-.i] = Pred[i]"
            proof -
            have s3_1: "-.iSucc[-.i] = -.-.Pred[-.-.i]"
                proof -
                have s4_1: "-.i \<in> negNat \<setminus> {0}"
                    using s1_2_asm minus_nat_0_in_negnat_0
                    by auto
                have s4_2: "-.i \<notin> Nat"
                    using s4_1 neg_nat_0_not_in_nat
                    by auto
                show ?thesis
                    unfolding iSucc_def
                    using s2_1 s4_2 by auto
                qed
            have s3_2: "-.-.Pred[-.-.i] = -.-.Pred[i]"
                proof -
                have s4_1: "-.-.i = i"
                    using s2_1 minus_involutive
                    by auto
                show ?thesis
                    using s4_1 by auto
                qed
            have s3_3: "-.-.Pred[i] = Pred[i]"
                proof -
                have s4_1: "Pred[i] \<in> Nat"
                    using s1_2_asm Pred_in_nat by auto
                have s4_2: "Pred[i] \<in> Int"
                    using s4_1 nat_in_int by auto
                show ?thesis
                    using s4_2 minus_involutive by auto
                qed
            show ?thesis
                using s3_1 s3_2 s3_3 by auto
            qed
        have s2_3: "iPred[i] = Pred[i]"
            unfolding iPred_def
            using s2_1 s1_2_asm by auto
        show "-.iSucc[-.i] = iPred[i]"
            using s2_2 s2_3 by auto
        qed
    have s1_3: "i \<in> negNat ==>
        -.iSucc[-.i] = iPred[i]"
        proof -
        assume s1_3_asm: "i \<in> negNat"
        have s2_1: "i \<in> Int"
            using s1_3_asm neg_nat_in_int
            by auto
        have s2_2: "i \<notin> Nat \<setminus> {0}"
            using s1_3_asm neg_nat_not_in_nat_setminus_0
            by auto
        have s2_3: "-.Succ[-.i] = iPred[i]"
            unfolding iPred_def
            using s2_1 s2_2 by auto
        have s2_4: "-.iSucc[-.i] = -.Succ[-.i]"
            proof -
            have s3_1: "-.i \<in> Nat"
                using s1_3_asm minus_neg_nat_in_nat by auto
            have s3_2: "-.i \<in> Int"
                using s3_1 nat_in_int by auto
            show ?thesis
                unfolding iSucc_def
                using s3_1 s3_2 by auto
            qed
        show "-.iSucc[-.i] = iPred[i]"
            using s2_3 s2_4 by auto
        qed
    show "-.iSucc[-.i] = iPred[i]"
        using s1_1 s1_2 s1_3 int_union_nat_0_negnat
        by auto
    qed


(*
THEOREM iPredMinusFlip ==
    \A i \in Int:  -.iPred[-.i] = iSucc[i]
PROOF
<1>1. SUFFICES
        ASSUME NEW i \in Int
        PROVE -.iPred[-.i] = iSucc[i]
    BY <1>1
<1>2. -.iSucc[-.-.i] = iPred[-.i]
    <2>1. -.i \in Int
        BY <1>1, neg_int_eq_int
    <2> QED
        BY <2>1, iSuccMinusFlip
<1>3. -.iSucc[i] = iPred[-.i]
    <2>1. -.-.i = i
        BY <1>1, minus_involutive
    <2> QED
        BY <1>2, <2>1
<1>4. -.-.iSucc[i] = -.iPred[-.i]
    BY <1>3
<1>5. -.-.iSucc[i] = iSucc[i]
    <2>1. iSucc[i] \in Int
        BY <1>1, iSucc_type
    <2> QED
        BY <2>1, minus_involutive
<1> QED
    BY <1>4, <1>5
*)
theorem iPredMinusFlip:
    "\<forall> i \<in> Int:  -.iPred[-.i] = iSucc[i]"
    proof auto
    fix "i" :: "c"
    assume s1_1: "i \<in> Int"
    have s1_2: "-.iSucc[-.-.i] = iPred[-.i]"
        proof -
        have s2_1: "-.i \<in> Int"
            using s1_1 neg_int_eq_int by auto
        show ?thesis
            using s2_1 iSuccMinusFlip by auto
        qed
    have s1_3: "-.iSucc[i] = iPred[-.i]"
        proof -
        have s2_1: "-.-.i = i"
            using s1_1 minus_involutive by auto
        show ?thesis
            using s1_2 s2_1 by auto
        qed
    have s1_4: "-.-.iSucc[i] = -.iPred[-.i]"
        using s1_3 by auto
    have s1_5: "-.-.iSucc[i] = iSucc[i]"
        proof -
        have s2_1: "iSucc[i] \<in> Int"
            using s1_1 iSucc_type by auto
        show ?thesis
            using s2_1 minus_involutive by auto
        qed
    show "-.iPred[-.i] = iSucc[i]"
        using s1_4 s1_5 by auto
    qed


(*----------------------------------------------------------------------------*)
(* `neg_nat_induction` *)


(*
negNat == {-.n:  n \in Nat}


THEOREM negNatInduction ==
    ASSUME
        NEW P(n), P(0),
        \A i \in negNat:  P(i) => P(-.Succ[-.i])
    PROVE
        \A i \in negNat:  P(i)
    PROOF
    <1> DEFINE Q(n) == P(-.n)
    <1>1. \A n \in Nat:  Q(n)
        <2>1. Q(0)
            BY P(0), -.0 = 0 DEF Q
        <2>2. ASSUME NEW n \in Nat, Q(n)
              PROVE Q(Succ[n])
            <3>1. P(-.n)
                BY <2>2 DEF Q
            <3>2. -.n \in negNat
                BY <2>2, n \in Nat DEF negNat
            <3>3. \A i \in negNat:  P(i) => P(-.Succ[-.i])
                OBVIOUS
            <3>4. P(-.n) => P(-.Succ[-.-.n])
                BY <3>2, <3>3
            <3>5. P(-.Succ[-.-.n])
                BY <3>1, <3>4
            <3>6. P(-.Succ[n])
                <4>1. -.-.n = n
                    BY <2>2, minus_involutive, nat_in_int
                <4> QED
                    BY <3>5, <4>1
            <3> QED
                BY <3>6 DEF Q
        <2> QED
            BY <2>1, <2>2, NatInduction
    <1>2. ASSUME NEW i \in negNat
          PROVE P(i)
        <2>1. \E n \in Nat:  n = -.i
            <3>1. i \in negNat
                BY <1>3
            <3>2. \E n \in Nat:  i = -.n
                BY <3>1 DEF negNat
            <3>3. \E n \in Nat:  -.i = -.-.n
                BY <3>2
            <3>4. \A n \in Nat:  -.-.n = n
                BY minus_involutive, nat_in_int
            <3> QED
                BY <3>3, <3>4
        <2>2. \E n \in Nat:  Q(-.i)
            <3>1. \E n \in Nat:  n = -.i /\ Q(n)
                BY <1>1, <2>1
            <3>2. \E n \in Nat:  n = -.i /\ Q(-.i)
                BY <3>1
            <3> QED
                BY <3>2
        <2>3. Q(-.i)
            BY <2>2
        <2>4. P(-.-.i)
            BY <2>3 DEF Q
        <2>5. -.-.i = i
            <3>1. i \in Int
                BY <1>2 DEF negNat, Int
            <3> QED
                BY <3>1, minus_involutive
        <2> QED
            BY <2>4, <2>5
    <1> QED
        BY <1>2
*)
theorem neg_nat_induction:
    assumes z: "P(0)" and
        sc: "\<And> i.
            \<lbrakk>
                i \\in negNat;
                P(i)
            \<rbrakk> \<Longrightarrow>
                P(-.Succ[-.i])"
    shows "\<forall> i \<in> negNat:  P(i)"
    proof -
    {
    fix "Q" :: "[c] \<Rightarrow> c"
    assume q_def: "\<forall> n:  Q(n) = P(-.n)"
    have s1_1: "\<forall> n \<in> Nat:  Q(n)"
        proof -
        have s2_1: "Q(0)"
            proof -
            have s3_1: "P(-.0)"
                using z neg0 by auto
            show "Q(0)"
                using s3_1 q_def allE by auto
            qed
        have s2_2: "\<And> n.
            \<lbrakk>
            n \<in> Nat;  Q(n)
            \<rbrakk> \<Longrightarrow>
                Q(Succ[n])"
            proof -
            fix "n" :: "c"
            assume ndom: "n \<in> Nat"
            assume Qn: "Q(n)"
            have s3_1: "P(-.n)"
                using Qn q_def by auto
            have s3_2: "-.n \<in> negNat"
                unfolding negNat_def
                using ndom by auto
            have s3_3: "\<And> i. \<lbrakk> i \<in> negNat;
                P(i)\<rbrakk> \<Longrightarrow>
                    P(-.Succ[-.i])"
                using sc by auto
            have s3_4: "P(-.n) ==>
                P(-.Succ[-.-.n])"
                using s3_2 s3_3 by auto
            have s3_5: "P(-.Succ[-.-.n])"
                using s3_1 s3_4 by auto
            have s3_6: "P(-.Succ[n])"
                proof -
                have s4_1: "-.-.n = n"
                    using ndom minus_involutive nat_in_int
                    by auto
                show "P(-.Succ[n])"
                    using s3_5 s4_1 by auto
                qed
            show "Q(Succ[n])"
                using s3_6 q_def by auto
            qed
        show "\<forall> n \<in> Nat:  Q(n)"
            using s2_1 s2_2 natInduct
            by auto
        qed
    have s1_2: "\<And> i. i \\in negNat ==> P(i)"
        proof -
        fix "i" :: "c"
        assume idom: "i \<in> negNat"
        have s2_1: "\<exists> n \<in> Nat:  n = -.i"
            proof -
            have s3_1: "i \<in> negNat"
                using idom by auto
            have s3_2: "\<exists> n \<in> Nat:  i = -.n"
                using s3_1 by (auto simp: negNat_def)
            have s3_3: "\<exists> n \<in> Nat:  -.i = -.-.n"
                using s3_2 by auto
            have s3_4: "\<forall> n \<in> Nat:  -.-.n = n"
                using minus_involutive nat_in_int
                by auto
            show "\<exists> n \<in> Nat:  n = -.i"
                using s3_3 s3_4 by auto
            qed
        have s2_2: "\<exists> n \<in> Nat:  Q(-.i)"
            proof -
            have s3_1: "\<exists> n \<in> Nat:
                n = -.i \<and> Q(n)"
                using s1_1 s2_1 by auto
            have s3_2: "\<exists> n \<in> Nat:
                n = -.i \<and> Q(-.i)"
                using s3_1 by auto
            show "\<exists> n \<in> Nat:  Q(-.i)"
                using s3_2 by auto
            qed
        have s2_3: "Q(-.i)"
            using s2_2 by auto
        have s2_4: "P(-.-.i)"
            using s2_3 q_def by auto
        have s2_5: "-.-.i = i"
            proof -
            have s3_1: "i \<in> Int"
                using idom
                by (auto simp: negNat_def Int_def)
            show "-.-.i = i"
                using s3_1 minus_involutive
                by auto
            qed
        show "P(i)"
            using s2_4 s2_5 by auto
        qed
    have "\<forall> i \<in> negNat:  P(i)"
        proof -
        have s2_1:
            "\<And> i. i \<in> negNat => P(i)"
            using s1_2 impI by auto
        have s2_2:
            "\<forall> i:  i \<in> negNat => P(i)"
            using s2_1 allI by auto
        show "\<forall> i \<in> negNat:  P(i)"
            using s2_2 by auto
            (* by (rule allI, rule impI, rule s1_2) *)
        qed
    }
    from this have "\<forall> Q: (
            (\<forall> n:  Q(n) = P(-.n))
            =>
            (\<forall> i \<in> negNat:  P(i))
            )"
        by auto
    from this have "
        (\<forall> n:  P(-.n) = P(-.n))
        =>
        (\<forall> i \<in> negNat:  P(i))"
        by auto
    thus "
        (\<forall> i \<in> negNat:  P(i))"
        by auto
    qed

(*----------------------------------------------------------------------------*)
(* Primitive recursion in two directions: plus and minus infinity. *)


theorem bprimrec_int:
    assumes
        e: "e \<in> S" and
        succ_h: "\<forall> n \<in> Nat:
            \<forall> x \<in> S:
                h(n, x) \<in> S" and
        succ_g: "\<forall> n \<in> Nat:
            \<forall> x \<in> S:
                g(n, x) \<in> S"
    shows "\<exists> f \<in> [Int -> S]:
        f[0] = e \<and>
        (\<forall> n \<in> Nat:
            f[Succ[n]] = h(n, f[n]) \<and>
            f[-.Succ[n]] = g(n, f[-.n])
        )"
    proof -
    from primrec_int[of e h g] obtain f where
        1: "isAFcn(f)" and
        2: "DOMAIN f = Int" and
        3: "f[0] = e" and
        4: "\<forall> n \<in> Nat:
                   f[Succ[n]] = h(n, f[n])
            \<and> f[-.Succ[n]] = g(n, f[-.n])"
        by blast
    have s1_2: "\<forall> n \<in> Nat:  f[n] \<in> S"
        proof (rule natInduct)
            from 3 e show "f[0] \<in> S" by simp
        next
            fix n
            assume "n \<in> Nat" and "f[n] \<in> S"
            with succ_h 4 show "f[Succ[n]] \<in> S"
            by force
        qed
    have s1_3: "\<forall> i \<in> negNat:  f[i] \<in> S"
        proof (rule neg_nat_induction)
            from 3 e show "f[0] \<in> S" by simp
        next
            fix i
            assume ndom: "i \<in> negNat" and
                   fidom: "f[i] \<in> S"
            have s2_1: "-.i \<in> Nat"
                using ndom minus_neg_nat_in_nat by auto
            have s2_2: "f[-.Succ[-.i]] = g(-.i, f[-.-.i])"
                using 4 s2_1 by auto
            have s2_3: "g(-.i, f[-.-.i]) = g(-.i, f[i])"
                using ndom neg_nat_in_int minus_involutive
                by auto
            have s2_4: "g(-.i, f[i]) \<in> S"
                using s2_1 fidom succ_g by auto
            show "f[-.Succ[-.i]] \<in> S"
                using s2_2 s2_3 s2_4 by auto
        qed
    have 5: "\<forall> i \<in> Int:  f[i] \<in> S"
        using s1_2 s1_3 int_union_nat_negnat
        by auto
    with 1 2 3 4 5 show ?thesis
        by blast
    qed


theorem primrec_intE:
    assumes e: "e \<in> S" and
        succ_h: "\<forall> n \<in> Nat:
            \<forall> x \<in> S:
                h(n, x) \<in> S" and
        succ_g: "\<forall> n \<in> Nat:
            \<forall> x \<in> S:
                g(n, x) \<in> S" and
        f: "f = (CHOOSE r \<in> [Int -> S]:
            r[0] = e \<and>
            (\<forall> n \<in> Nat:
                r[Succ[n]] = h(n, r[n]) \<and>
                r[-.Succ[n]] = g(n, r[-.n])
            ))" (is "f = ?r") and
        maj: "\<lbrakk>
            f \<in> [Int -> S];
            f[0] = e;
            \<forall> n \<in> Nat:
                f[Succ[n]] = h(n, f[n]) \<and>
                f[-.Succ[n]] = g(n, f[-.n])
            \<rbrakk>
                \<Longrightarrow> P"
    shows "P"
    proof -
    from e succ_h succ_g have "
    \<exists> r \<in> [Int -> S]:
        r[0] = e \<and>
        (\<forall> n \<in> Nat:
            r[Succ[n]] = h(n, r[n]) \<and>
            r[-.Succ[n]] = g(n, r[-.n])
        )"
    by (rule bprimrec_int)
    hence "?r \<in> [Int -> S] \<and>
        ?r[0] = e \<and>
        (\<forall> n \<in> Nat:
            ?r[Succ[n]] = h(n, ?r[n]) \<and>
            ?r[-.Succ[n]] = g(n, ?r[-.n])
        )"
        by (rule bChooseI2, auto)
    with f maj show ?thesis by auto
    qed


theorem bprimrecType_int:
    assumes "e \<in> S" and
        "\<forall> n \<in> Nat:
        \<forall> x \<in> S:
            h(n, x) \<in> S" and
        "\<forall> n \<in> Nat:
        \<forall> x \<in> S:
            g(n, x) \<in> S"
    shows "(CHOOSE f \<in> [Int -> S]:
            f[0] = e \<and>
            (\<forall> n \<in> Nat:
                f[Succ[n]] = h(n, f[n]) \<and>
                f[-.Succ[n]] = g(n, f[-.n])
            )) \<in> [Int -> S]"
    by (rule primrec_intE[OF assms], auto)


(*----------------------------------------------------------------------------*)
(* Typeness of addition and recursive properties. *)


theorem addintType:
    assumes mdom: "m \<in> Int"
    shows "addint(m) \<in> [Int -> Int]"
    proof -
    have s1_1: "
        \<forall> n \<in> Nat:
        \<forall> x \<in> Int:
            iSucc[x] \<in> Int"
        using iSucc_type by auto
    have s1_2: "
        \<forall> n \<in> Nat:
        \<forall> x \<in> Int:
            iPred[x] \<in> Int"
        using iPred_type by auto
    have s1_3: "(CHOOSE f \<in> [Int -> Int]:
            f[0] = m \<and>
            (\<forall> n \<in> Nat:
                f[Succ[n]] = iSucc[f[n]] \<and>
                f[-.Succ[n]] = iPred[f[-.n]]
            )) \<in> [Int -> Int]"
        using mdom s1_1 s1_2
        by (rule bprimrecType_int)
    show "addint(m) \<in> [Int -> Int]"
        unfolding addint_def
        using s1_3 by auto
    qed


theorem addIsInt:
    assumes "m \<in> Int" and "n \<in> Int"
    shows "add(m, n) \<in> Int"
    unfolding add_def
    using assms addintType by blast


theorem diffIsInt:
    assumes mdom: "m \\in Int" and ndom: "n \\in Int"
    shows "diff(m, n) \\in Int"
    proof -
    have s1_1: "diff(m, n) = add(m, -.n)"
        unfolding diff_def by auto
    have s1_2: "-.n \\in Int"
        using ndom neg_int_eq_int by auto
    have s1_3: "add(m, -.n) \\in Int"
        using mdom s1_2 addIsInt by auto
    show ?thesis
        using s1_1 s1_3 by auto
    qed


theorem addint_0:
    assumes mdom: "m \<in> Int"
    shows "addint(m)[0] = m"
    proof -
    have s1_1: "
        \<forall> n \<in> Nat:
        \<forall> x \<in> Int:
            iSucc[x] \<in> Int"
        using iSucc_type by auto
    have s1_2: "
        \<forall> n \<in> Nat:
        \<forall> x \<in> Int:
            iPred[x] \<in> Int"
        using iPred_type by auto
    have s1_3: "
        addint(m) = (CHOOSE r \<in> [Int -> Int]:
            r[0] = m \<and>
            (\<forall> n \<in> Nat:
                r[Succ[n]] = iSucc[r[n]] \<and>
                r[-.Succ[n]] = iPred[r[-.n]])
            )"
        unfolding addint_def
        by auto
    have s1_4: "
        \<lbrakk>
        addint(m) \<in> [Int -> Int];
        addint(m)[0] = m;
        \<forall> n \<in> Nat:
            addint(m)[Succ[n]] = iSucc[addint(m)[n]] \<and>
            addint(m)[-.Succ[n]] = iPred[addint(m)[-.n]]
        \<rbrakk>
            \<Longrightarrow> addint(m)[0] = m"
        by auto
    show ?thesis
        using mdom s1_1 s1_2 s1_3 s1_4
            primrec_intE[of
                "m" "Int"
                "\<lambda> n x.  iSucc[x]"
                "\<lambda> n x.  iPred[x]"
                "addint(m)"]
        by auto
    qed


theorem add_0:
    assumes "m \<in> Int"
    shows "m + 0 = m"
    unfolding add_def
    using assms addint_0 by auto


theorem addint_succ:
    assumes mdom: "m \<in> Int"
    shows "\<forall> n \<in> Nat:
        addint(m)[Succ[n]] = iSucc[addint(m)[n]] \<and>
        addint(m)[-.Succ[n]] = iPred[addint(m)[-.n]]"
    proof -
    have s1_1: "
        \<forall> n \<in> Nat:
        \<forall> x \<in> Int:
            iSucc[x] \<in> Int"
        using iSucc_type by auto
    have s1_2: "
        \<forall> n \<in> Nat:
        \<forall> x \<in> Int:
            iPred[x] \<in> Int"
        using iPred_type by auto
    have s1_3: "
        addint(m) = (CHOOSE r \<in> [Int -> Int]:
            r[0] = m \<and>
            (\<forall> n \<in> Nat:
                r[Succ[n]] = iSucc[r[n]] \<and>
                r[-.Succ[n]] = iPred[r[-.n]])
            )"
        unfolding addint_def
        by auto
    have s1_4: "
        \<lbrakk>
        addint(m) \<in> [Int -> Int];
        addint(m)[0] = m;
        \<forall> n \<in> Nat:
            addint(m)[Succ[n]] = iSucc[addint(m)[n]] \<and>
            addint(m)[-.Succ[n]] = iPred[addint(m)[-.n]]
        \<rbrakk>
            \<Longrightarrow>
                \<forall> n \<in> Nat:
                    addint(m)[Succ[n]] = iSucc[addint(m)[n]] \<and>
                    addint(m)[-.Succ[n]] = iPred[addint(m)[-.n]]
            "
        by auto
    show ?thesis
        using mdom s1_1 s1_2 s1_3 s1_4
            primrec_intE[of
                "m" "Int"
                "\<lambda> n x. iSucc[x]"
                "\<lambda> n x. iPred[x]"
                "addint(m)"]
        by auto
    qed


theorem addint_succ_nat:
    assumes mdom: "m \<in> Int" and ndom: "n \<in> Nat"
    shows "m + Succ[n] = iSucc[m + n]"
    unfolding add_def
    using mdom ndom addint_succ[of "m"] spec by auto


theorem addint_succ_negnat:
    assumes mdom: "m \<in> Int" and ndom: "n \<in> Nat"
    shows "m + -.Succ[n] = iPred[m + -.n]"
    unfolding add_def
    using mdom ndom addint_succ[of "m"] spec by auto


theorem nat_add_1:
    assumes ndom: "n \\in Nat"
    shows "Succ[n] = n + 1"
    proof -
    have s1_1: "Succ[n] = iSucc[n]"
        proof -
        have s2_1: "n \\in Int"
            using ndom nat_in_int by auto
        have s2_2: "n \\in Nat"
            using ndom by auto
        show ?thesis
            unfolding iSucc_def
            using s2_1 s2_2 by auto
        qed
    also have s1_2: "... = iSucc[n + 0]"
        proof -
        have s2_1: "n \\in Int"
            using ndom nat_in_int by auto
        have s2_2: "n + 0 = n"
            using s2_1 add_0 by auto
        have s2_3: "n = n + 0"
            using s2_2[symmetric] by auto
        show ?thesis
            using s2_3 by auto
        qed
    also have s1_3: "... = n + Succ[0]"
        proof -
        have s2_1: "n \\in Int"
            using ndom nat_in_int by auto
        have s2_2: "0 \\in Nat"
            using zeroIsNat by auto
        show ?thesis
            using s2_1 s2_2 addint_succ_nat by auto
        qed
    also have s1_4: "... = n + 1"
        by auto  (* 1 is an abbreviation *)
    from calculation show ?thesis .
    qed


theorem nat_add_in_nat:
    assumes mdom: "m \\in Nat" and ndom: "n \\in Nat"
    shows "m + n \\in Nat"
    proof -
    have s1_1: "m + 0 \\in Nat"
        proof -
        have s2_1: "m + 0 = m"
            proof -
            have s3_1: "m \\in Int"
                using mdom nat_in_int by auto
            show ?thesis
                using s3_1 add_0 by auto
            qed
        have s2_2: "m \\in Nat"
            using mdom by auto
        show ?thesis
            using s2_1 s2_2 by auto
        qed
    have s1_2: "\<And> k.  \<lbrakk>
        k \\in Nat;
        m + k \\in Nat
        \<rbrakk> \<Longrightarrow>
            m + Succ[k] \\in Nat"
        proof -
        fix "k" :: "c"
        assume s1_2_kdom: "k \\in Nat"
        assume s1_2_induct: "m + k \\in Nat"
        have s2_1: "m + Succ[k] = iSucc[m + k]"
            proof -
            have s3_1: "m \\in Int"
                using mdom nat_in_int by auto
            have s3_2: "k \\in Nat"
                using s1_2_kdom by auto
            show ?thesis
                using s3_1 s3_2 addint_succ_nat by auto
            qed
        have s2_2: "iSucc[m + k] = Succ[m + k]"
            proof -
            have s3_1: "m + k \\in Nat"
                using s1_2_induct by auto
            have s3_2: "m + k \\in Int"
                using s1_2_induct nat_in_int by auto
            show ?thesis
                unfolding iSucc_def
                using s3_1 s3_2 by auto
            qed
        have s2_3: "Succ[m + k] \\in Nat"
            using s1_2_induct succIsNat by auto
        show "m + Succ[k] \\in Nat"
            using s2_1 s2_2 s2_3 by auto
        qed
    have s1_3: "\<forall> k \<in> Nat:  m + k \\in Nat"
        using s1_1 s1_2 natInduct by auto
    show ?thesis
        using s1_3 ndom spec by auto
    qed


theorem nat_0_succ:
    "\<forall> n \<in> Nat:
        n=0 \<or>
        (\<exists> m \<in> Nat:  n = Succ[m])"
    by (rule natInduct, auto)


theorem nat_add_0:
    assumes mdom: "m \\in Nat" and ndom: "n \\in Nat" and
        mn: "m + n = 0"
    shows "m = 0 \<and> n = 0"
    proof -
    have s1_1: "n \<noteq> 0 ==> FALSE"
        proof -
        assume s2_1: "n \<noteq> 0"
        have s2_2: "\<exists> k:  k \\in Nat \<and> n = Succ[k]"
            using ndom s2_1 nat_0_succ by auto
        def P \<equiv> "\<lambda> x.  x \\in Nat \<and> n = Succ[x]"
        def r \<equiv> "CHOOSE x:  P(x)"
        have s2_3: "r \\in Nat \<and> n = Succ[r]"
            proof -
            have s3_1: "\<exists> x:  P(x)"
                using s2_2 by (auto simp: P_def)
            have s3_2: "P(r)"
                using s3_1 chooseI_ex by (auto simp: r_def)
            show ?thesis
                using s3_2 by (auto simp: P_def)
            qed
        have s2_4: "m + n = m + Succ[r]"
            using s2_3 by auto
        have s2_5: "m + Succ[r] = iSucc[m + r]"
            proof -
            have s3_1: "m \\in Int"
                using mdom nat_in_int by auto
            have s3_2: "r \\in Nat"
                using s2_3 by auto
            show ?thesis
                using s3_1 s3_2 addint_succ_nat by auto
            qed
        have s2_6: "iSucc[m + r] = Succ[m + r]"
            proof -
            have s3_1: "m + r \\in Nat"
                using mdom s2_3 nat_add_in_nat by auto
            have s3_2: "m + r \\in Int"
                using s3_1 nat_in_int by auto
            show ?thesis
                unfolding iSucc_def
                using s3_1 s3_2 by auto
            qed
        have s2_7: "Succ[m + r] \<noteq> 0"
            proof -
            have s3_1: "m + r \\in Nat"
                using mdom s2_3 nat_add_in_nat by auto
            show ?thesis
                using s3_1 succNotZero by auto
            qed
        have s2_7: "m + n \<noteq> 0"
            using s2_4 s2_5 s2_6 s2_7 by auto
        show "FALSE"
            using s2_7 mn by auto
        qed
    have s1_2: "n = 0"
        using s1_1 by auto
    have s1_3: "m + 0 = 0"
        using mn s1_2 by auto
    have s1_4: "m = 0"
        using s1_3 mdom nat_in_int add_0 by auto
    show ?thesis
        using s1_2 s1_4 by auto
    qed


(*----------------------------------------------------------------------------*)
(* Typeness of multiplication and recursive properties. *)


theorem multType:
    assumes mdom: "m \<in> Int"
    shows "multint(m) \<in> [Int -> Int]"
    proof -
    have s1_1: "
        \<forall> n \<in> Nat:
        \<forall> x \<in> Int:
            x + m \<in> Int"
        using mdom addIsInt by auto
    have s1_2: "
        \<forall> n \<in> Nat:
        \<forall> x \<in> Int:
            x + -.m \<in> Int"
        proof -
        have s2_1: "-.m \<in> Int"
            using mdom neg_int_eq_int by auto
        show ?thesis
            using s2_1 addIsInt by auto
        qed
    have s1_3: "(CHOOSE f \<in> [Int -> Int]:
            f[0] = 0 \<and>
            (\<forall> n \<in> Nat:
                f[Succ[n]] = f[n] + m \<and>
                f[-.Succ[n]] = f[-.n] + -.m
        )) \<in> [Int -> Int]"
        using zero_in_int s1_1 s1_2
        by (rule bprimrecType_int[of "0"])
    show "multint(m) \<in> [Int -> Int]"
        unfolding multint_def
        using s1_3 by auto
    qed


theorem multIsInt:
    assumes "m \<in> Int" and "n \<in> Int"
    shows "mult(m, n) \<in> Int"
    unfolding mult_def
    using assms multType by blast


theorem multint_0:
    assumes mdom: "m \<in> Int"
    shows "multint(m)[0] = 0"
    proof -
    have s1_1: "
        \<forall> n \<in> Nat:
        \<forall> x \<in> Int:
            x + m \<in> Int"
        using mdom addIsInt by auto
    have s1_2: "
        \<forall> n \<in> Nat:
        \<forall> x \<in> Int:
            x + -.m \<in> Int"
        proof -
        have s2_1: "-.m \<in> Int"
            using mdom neg_int_eq_int by auto
        show ?thesis
            using s2_1 addIsInt by auto
        qed
    have s1_3: "
        multint(m) = (CHOOSE r \<in> [Int -> Int]:
            r[0] = 0 \<and>
            (\<forall> n \<in> Nat:
                    r[Succ[n]] = r[n] + m \<and>
                    r[-.Succ[n]] = r[-.n] + -.m)
            )"
        unfolding multint_def
        by auto
    have s1_4: "
        \<lbrakk>
        multint(m) \<in> [Int -> Int];
        multint(m)[0] = 0;
        \<forall> n \<in> Nat:
            multint(m)[Succ[n]] = multint(m)[n] + m \<and>
            multint(m)[-.Succ[n]] = multint(m)[-.n] + -.m
        \<rbrakk>
            \<Longrightarrow>
                multint(m)[0] = 0"
        by auto
    show ?thesis
        using mdom s1_1 s1_2 s1_3 s1_4
            primrec_intE[of
                "0" "Int"
                "\<lambda> n x.  x + m"
                "\<lambda> n x.  x + -.m"
                "multint(m)"]
        by auto
    qed


theorem mult_0:
    assumes "m \<in> Int"
    shows "m * 0 = 0"
    unfolding mult_def
    using assms multint_0 by auto


theorem multint_succ:
    assumes mdom: "m \<in> Int"
    shows "\<forall> n \<in> Nat:
        multint(m)[Succ[n]] = multint(m)[n] + m \<and>
        multint(m)[-.Succ[n]] = multint(m)[-.n] + -.m"
    proof -
    have s1_1: "
        \<forall> n \<in> Nat:
        \<forall> x \<in> Int:
            x + m \<in> Int"
        using mdom addIsInt by auto
    have s1_2: "
        \<forall> n \<in> Nat:
        \<forall> x \<in> Int:
            x + -.m \<in> Int"
        proof -
        have s2_1: "-.m \<in> Int"
            using mdom neg_int_eq_int by auto
        show ?thesis
            using s2_1 addIsInt by auto
        qed
    have s1_3: "
        multint(m) = (CHOOSE r \<in> [Int -> Int]:
            r[0] = 0 \<and>
            (\<forall> n \<in> Nat:
                    r[Succ[n]] = r[n] + m \<and>
                    r[-.Succ[n]] = r[-.n] + -.m)
            )"
        unfolding multint_def
        by auto
    have s1_4: "
        \<lbrakk>
        multint(m) \<in> [Int -> Int];
        multint(m)[0] = 0;
        \<forall> n \<in> Nat:
            multint(m)[Succ[n]] = multint(m)[n] + m \<and>
            multint(m)[-.Succ[n]] = multint(m)[-.n] + -.m
        \<rbrakk>
            \<Longrightarrow>
                \<forall> n \<in> Nat:
                    multint(m)[Succ[n]] = multint(m)[n] + m \<and>
                    multint(m)[-.Succ[n]] = multint(m)[-.n] + -.m
            "
        by auto
    show ?thesis
        using mdom s1_1 s1_2 s1_3 s1_4
            primrec_intE[of
                "0" "Int"
                "\<lambda> n x.  x + m"
                "\<lambda> n x.  x + -.m"
                "multint(m)"]
        by auto
    qed


theorem multint_succ_nat:
    assumes mdom: "m \<in> Int" and ndom: "n \<in> Nat"
    shows "m * Succ[n] = m * n + m"
    unfolding mult_def
    using mdom ndom multint_succ[of "m"] spec by auto


theorem multint_succ_negnat:
    assumes mdom: "m \<in> Int" and ndom: "n \<in> Nat"
    shows "m * -.Succ[n] = m * -.n + -.m"
    unfolding mult_def
    using mdom ndom multint_succ[of "m"] spec by auto


theorem nat_mult_in_nat:
    assumes mdom: "m \\in Nat" and ndom: "n \\in Nat"
    shows "m * n \\in Nat"
    proof -
    have s1_1: "m * 0 \\in Nat"
        proof -
        have s2_1: "m * 0 = 0"
            using mdom nat_in_int mult_0 by auto
        have s2_2: "0 \\in Nat"
            using zeroIsNat by auto
        show ?thesis
            using s2_1 s2_2 by auto
        qed
    have s1_2: "\<And> k.  \<lbrakk>
            k \\in Nat;
            m * k \\in Nat
        \<rbrakk> \<Longrightarrow>
            m * Succ[k] \\in Nat"
        proof -
        fix "k" :: "c"
        assume s1_2_kdom: "k \\in Nat"
        assume s1_2_induct: "m * k \\in Nat"
        have s2_1: "m * Succ[k] = m * k + m"
            using mdom s1_2_kdom multint_succ_nat by auto
        have s2_2: "m * k + m \\in Nat"
            using s1_2_induct mdom nat_add_in_nat by auto
        show "m * Succ[k] \\in Nat"
            using s2_1 s2_2 by auto
        qed
    have s1_3: "\<forall> k \<in> Nat:  m * k \\in Nat"
        using s1_1 s1_2 natInduct by auto
    show ?thesis
        using s1_3 ndom spec by auto
    qed


(*----------------------------------------------------------------------------*)
(* Commutativity of addition. *)


(*
THEOREM pred_irrefl ==
    ASSUME NEW n \in Nat \ {0}
    PROVE Pred[n] # n
PROOF
<1>1. Pred[n] \in Nat
    BY n \in Nat, Pred_in_nat
<1>2. Succ[Pred[n]] # Pred[n]
    BY <1>1, succIrrefl
<1>3. Succ[Pred[n]] = n
    BY n \in Nat \ {0}, Succ_Pred_nat
<1> QED
    BY <1>2, <1>3
*)
theorem pred_irrefl:
    assumes ndom: "n \\in Nat \<setminus> {0}"
    shows "Pred[n] \<noteq> n"
    proof -
    have s1_1: "Pred[n] \\in Nat"
        using ndom Pred_in_nat by auto
    have s1_2: "Succ[Pred[n]] \<noteq> Pred[n]"
        using s1_1 succIrrefl by auto
    have s1_3: "Succ[Pred[n]] = n"
        using ndom Succ_Pred_nat by auto
    show ?thesis
        using s1_2 s1_3 by auto
    qed


theorem ipred_plus_1:
    assumes hyp: "a \<in> Int"
    shows "iPred[a + 1] = a"
    proof -
    have s1_1: "iPred[a + 1] = iPred[a + Succ[0]]"
        by auto
    have s1_2: "... = iPred[iSucc[a + 0]]"
        proof -
        have s2_1: "a \<in> Int"
            using hyp by auto
        have s2_2: "0 \<in> Nat"
            using zeroIsNat by auto
        have s2_3: "a + Succ[0] = iSucc[a + 0]"
            using s2_1 s2_2 addint_succ_nat by auto
        show ?thesis
            using s2_3 by auto
        qed
    have s1_3: "... = iPred[iSucc[a]]"
        using hyp add_0 by auto
    have s1_4: "... = a"
        using hyp iSucciPredCommute spec by auto
    show ?thesis
        using s1_1 s1_2 s1_3 s1_4 by auto
    qed


(*
THEOREM AddCommutativeNatNat ==
    \A j \in Nat:  \A i \in Nat:
        j + i = i + j
PROOF
<1>1. \A i \in Nat:  0 + i = i + 0
    <2>1. 0 + 0 = 0 + 0
        <3>1. 0 + 0 = addint(0)[0]
            BY DEF +
        <3>2. @ = 0
            BY DEF addint
        <3> QED
            BY <3>1, <3>2

    <2>2. ASSUME NEW i \in Nat, 0 + i = i + 0
          PROVE 0 + Succ[i] = Succ[i] + 0

        <3>1. 0 + Succ[i] = iSucc[0 + i]
            BY DEF +
        <3>2. @ = iSucc[i + 0]
            BY <2>2
        <3>3. @ = iSucc[i]
            BY DEF +
        <3>4. @ = Succ[i]
            BY <2>2, i \in Nat
        <3>5. @ = Succ[i] + 0
            BY DEF +
        <3> QED
            BY <3>1, <3>2, <3>3, <3>4, <3>5
    <2> QED
        BY <2>1, <2>2, NatInduction

<1>2. ASSUME NEW j \in Nat,
            \A i \in Nat:  j + i = i + j
      PROVE \A i \in Nat:  Succ[j] + i = i + Succ[j]

    <2>1. Succ[j] + 0 = 0 + Succ[j]
        <3>1. Succ[j] + 0 = Succ[j]
            BY DEF +
        <3>2. @ = Succ[j + 0]
            BY DEF +
        <3>3. @ = Succ[0 + j]
            BY <1>2
        <3>4. @ = 0 + Succ[j]
            BY DEF +
        <3> QED
            BY <3>1, <3>2, <3>3, <3>4

    <2>2. ASSUME NEW i \in Nat,
                Succ[j] + i = i + Succ[j]
          PROVE Succ[j] + Succ[i] = Succ[i] + Succ[j]

        <3>1. Succ[j] + Succ[i] = iSucc[iSucc[j + i]]
            <4>1. Succ[j] + Succ[i] = iSucc[Succ[j] + i]
                <5>1. Succ[j] \in Int
                    BY <1>2, succIsNat, nat_in_int
                <5>2. Succ[i] \in Nat
                    BY <2>2, succIsNat
                <5> QED
                    BY <5>1, <5>2, addint_succ
            <4>2. @ = iSucc[i + Succ[j]]
                BY <2>2
            <4>3. @ = iSucc[iSucc[i + j]]
                <5>1. i \in Int
                    BY <2>2, nat_in_int
                <5>2. j \in Nat
                    BY <1>2
                <5> QED
                    BY <5>1, <5>2, addint_succ
            <4>4. @ = iSucc[iSucc[j + i]]
                BY <1>2, <2>2
            <4> QED
                BY <4>1, <4>2, <4>3, <4>4

        <3>2. Succ[i] + Succ[j] = iSucc[iSucc[j + i]]
            <4>1. Succ[i] + Succ[j] = iSucc[Succ[i] + j]
                <5>1. Succ[i] \in Int
                    BY <2>2, succIsNat, nat_in_int
                <5>2. Succ[j] \in Nat
                    BY <1>2, succIsNat
                <5> QED
                    BY <5>1, <5>2, addint_succ
            <4>2. @ = iSucc[j + Succ[i]]
                <5>1. Succ[i] \in Nat
                    BY <2>2, succIsNat
                <5> QED
                    BY <1>2, <5>1
            <4>3. @ = iSucc[iSucc[j + i]]
                <5>1. j \in Int
                    BY <1>2, nat_in_int
                <5>2. i \in Nat
                    BY <2>2
                <5> QED
                    BY <5>1, <5>2, addint_succ
            <4> QED
                BY <4>1, <4>2, <4>3

        <3> QED
            BY <3>1, <3>2
    <2> QED
        BY <2>1, <2>2, NatInduction
<1> QED
    BY <1>1, <1>2, NatInduction


THEOREM AddCommutative ==
    \A j \in Int:  \A i \in Int:
        j + i = i + j
PROOF
<1>1. \A j \in Nat:  \A i \in Int:
        j + i = i + j
    <2>1. \A j \in Nat:  \A i \in Nat:
            j + i = i + j
        \* The proof of step <2>1 is the same with the
        \* proof of the theorem `AddCommutativeNatNat`.
        <3>1. \A i \in Nat:  0 + i = i + 0
            <4>1. 0 + 0 = 0 + 0
                OBVIOUS
            <4>2. ASSUME NEW i \in Nat,
                    0 + i = i + 0
                  PROVE 0 + Succ[i] = Succ[i] + 0
                <5>1. 0 + Succ[i] = iSucc[0 + i]
                    <6>1. 0 \in Int
                        BY zero_in_int
                    <6>2. i \in Nat
                        BY <4>2
                    <6> QED
                        BY <6>1, <6>2, addint_succ
                            DEF addd
                <5>2. @ = iSucc[i + 0]
                    BY <4>2
                <5>3. @ = iSucc[i]
                    <6>1. i \in Int
                        BY <4>2, nat_in_int
                    <6> QED
                        BY <6>1 addint_0
                <5>4. @ = Succ[i]
                    BY <4>2 DEF iSucc
                <5>5. @ = Succ[i] + 0
                    <6>1. Succ[i] \in Nat
                        BY <4>2, succIsNat
                    <6>2. Succ[i] \in Int
                        BY <6>1, nat_in_int
                    <6> QED
                        BY <6>2, addint_0
                <5> QED
                    BY <5>1, <5>2, <5>3, <5>4, <5>5
            <4> QED
                BY <4>1, <4>2, NatInduction
        <3>2. ASSUME NEW j \in Nat,
                    \A i \in Nat:  j + i = i + j
              PROVE \A i \in Nat:  Succ[j] + i = i + Succ[j]
            <4>1. Succ[j] + 0 = 0 + Succ[j]
                <5>1. Succ[j] + 0 = Succ[j]
                    <6>1. Succ[j] \in Int
                        BY <3>2, succIsNat, nat_in_int
                    <6> QED
                        BY <6>1, addint_0
                <5>2. @ = iSucc[j]
                    BY <3>2, nat_in_int DEF iSucc
                <5>3. @ = iSucc[j + 0]
                    <6>1. j \in Int
                        BY <3>2, nat_in_int
                    <6>2. j + 0 = j
                        BY <6>1, add_0
                    <6> QED
                        BY <6>2
                <5>4. @ = iSucc[0 + j]
                    <6>1. j + 0 = 0 + j
                        BY <3>2, zeroIsNat
                    <6> QED
                        By <6>1
                <5>5. @ = 0 + Succ[j]
                    <6>1. 0 \in Int
                        BY zero_in_int
                    <6>2. j \in Nat
                        BY <3>2
                    <6> QED
                        BY <6>1, <6>2, addint_succ
                <5> QED
                    BY <5>1, <5>2, <5>3, <5>4, <5>5
            <4>2. ASSUME NEW i \in Nat,
                        Succ[j] + i = i + Succ[j]
                  PROVE Succ[j] + Succ[i] = Succ[i] + Succ[j]
                <5>1. Succ[j] + Succ[i] = iSucc[iSucc[j + i]]
                    <6>1. Succ[j] + Succ[i] = iSucc[Succ[j] + i]
                        <7>1. Succ[j] \in Int
                            BY <3>2, succIsNat, nat_in_int
                        <7>2. i \in Nat
                            BY <4>2
                        <7> QED
                            BY <7>1, <7>2, addint_succ
                    <6>2. @ = iSucc[i + Succ[j]]
                        BY <4>2
                    <6>3. @ = iSucc[iSucc[i + j]]
                        <7>1. i \in Int
                            BY <4>2, nat_in_int
                        <7>2. j \in Nat
                            BY <3>2
                        <7> QED
                            BY <7>1, <7>2, addint_succ
                    <6>4. @ = iSucc[iSucc[j + i]]
                        BY <3>2, <4>2
                    <6> QED
                        By <6>1, <6>2, <6>3, <6>4
                <5>2. Succ[i] + Succ[j] = iSucc[iSucc[j + i]]
                    <6>1. Succ[i] + Succ[j] = iSucc[Succ[i] + j]
                        <7>1. Succ[i] \in Int
                            BY <4>2, succIsNat, nat_in_int
                        <7>2. j \in Nat
                            BY <3>2, succIsNat
                        <7> QED
                            BY <7>1, <7>2, addint_succ
                    <6>2. @ = iSucc[j + Succ[i]]
                        <7>1. Succ[i] \in Nat
                            BY <4>2, succIsNat
                        <7> QED
                            BY <3>2, <7>1
                    <6>3. @ = iSucc[iSucc[j + i]]
                        <7>1. j \in Int
                            BY <3>2, nat_in_int
                        <7>2. i \in Nat
                            BY <4>2
                        <7> QED
                            BY <7>1, <7>2, addint_succ
                    <6> QED
                        BY <6>1, <6>2, <6>3
                <5> QED
                    BY <5>1, <5>2
            <4> QED
                BY <4>1, <4>2, NatInduction
        <3> QED
            BY <3>1, <3>2, NatInduction
    <2>2. \A j \in Nat:  \A i \in negNat:
            j + i = i + j
        <3>1. \A i \in negNat:  0 + i = i + 0
            <4>1. 0 + 0 = 0 + 0
                OBVIOUS
            <4>2. ASSUME NEW i \in negNat,
                        0 + i = i + 0
                  PROVE 0 + -.Succ[-.i] = -.Succ[-.i] + 0
                <5>1. 0 + -.Succ[-.i] = iPred[0 + i]
                    <6>1. 0 \in Int
                        BY zero_in_int
                    <6>2. -.i \in Nat
                        BY <4>2, minus_neg_nat_in_nat
                    <6>3. 0 + -.Succ[-.i] = iPred[0 + -.-.i]
                        BY <6>1, <6>2, addint_succ_negnat
                    <6>4. -.-.i = i
                        <7>1. i \in Int
                            BY <4>2, neg_nat_in_int
                        <7> QED
                            BY <7>1, minus_involutive
                    <6> QED
                        BY <6>3, <6>4
                <5>2. @ = iPred[i + 0]
                    BY <4>2
                <5>3. @ = iPred[i]
                    <6>1. i \in Int
                        BY <4>2, neg_nat_in_int
                    <6>2. i + 0 = i
                        BY <6>1, add_0
                    <6> QED
                        BY <6>2
                <5>4. @ = -.Succ[-.i]
                    <6>1. i \in Int
                        BY <4>2, neg_nat_in_int
                    <6>2. i \notin Nat \ {0}
                        BY <4>2, neg_nat_not_in_nat_setminus_0
                    <6> QED
                        BY <6>1, <6>2 DEF iPred
                <5>5. @ = -.Succ[-.i] + 0
                    <6>1. -.i \in Nat
                        BY <4>2, minus_neg_nat_in_nat
                    <6>2. Succ[-.i] \in Nat
                        BY <6>1, succIsNat
                    <6>3. -.Succ[-.i] \in Int
                        BY <6>2, minus_nat_in_int
                    <6> QED
                        BY <6>3, add_0
                <5> QED
                    BY <5>1, <5>2, <5>3, <5>4, <5>5
            <4> QED
                BY <4>1, <4>2, neg_nat_induction
        <3>2. ASSUME NEW j \in Nat,
                    \A i \in negNat:  j + i = i + j
              PROVE \A i \in negNat:  Succ[j] + i = i + Succ[j]
            <4>1. Succ[j] + 0 = 0 + Succ[j]
                <5>1. Succ[j] + 0 = Succ[j]
                    <6>1. Succ[j] \in Int
                        BY <3>2, succIsNat, nat_in_int
                    <6> QED
                        BY <6>1, add_0
                <5>2. @ = iSucc[j]
                    <6>1. j \in Int
                        BY <3>2, nat_in_int
                    <6>2. j \in Nat
                        BY <3>2
                    <6> QED
                        BY <6>1, <6>2 DEF iSucc
                <5>3. @ = iSucc[j + 0]
                    <6>1. j \in Int
                        BY <3>2, nat_in_int
                    <6>2. j + 0 = j
                        BY <6>1, add_0
                    <6> QED
                        BY <6>2
                <5>4. @ = iSucc[0 + j]
                    <6>1. 0 \in negNat
                        BY neg0 DEF negNat
                    <6> QED
                        BY <3>2, <6>1
                <5>5. @ = 0 + Succ[j]
                    <6>1. 0 \in Int
                        BY zero_in_int
                    <6>2. j \in Nat
                        BY <3>2
                    <6> QED
                        BY <6>1, <6>2, addint_succ_nat
                <5> QED
                    BY <5>1, <5>2, <5>3, <5>4, <5>5
            <4>2. ASSUME NEW i \in negNat,
                        Succ[j] + i = i + Succ[j]
                  PROVE Succ[j] + -.Succ[-.i] = -.Succ[-.i] + Succ[j]
                <5>1. Succ[j] + -.Succ[-.i] = iPred[iSucc[j + i]]
                    <6>1. Succ[j] + -.Succ[-.i] = iPred[Succ[j] + i]
                        <7>1. Succ[j] \in Int
                            BY <3>2, succIsNat, nat_in_int
                        <7>2. -.i \in Nat
                            BY <4>2, minus_neg_nat_in_nat
                        <7>3. -.-.i = i
                            <8>1. i \in Int
                                BY <4>2, neg_nat_in_int
                            <8> QED
                                BY <8>1, minus_involutive
                        <7>4. Succ[j] + -.Succ[-.i]
                                = iPred[Succ[j] + -.-.i]
                            BY <7>1, <7>2, addint_succ_negnat
                        <7> QED
                            BY <7>3, <7>4
                    <6>2. @ = iPred[i + Succ[j]]
                        BY <4>2
                    <6>3. @ = iPred[iSucc[i + j]]
                        <7>1. i \in Int
                            BY <4>2, neg_nat_in_int
                        <7>2. j \in Nat
                            BY <3>2
                        <7> QED
                            BY <7>1, <7>2, addint_succ_nat
                    <6>4. @ = iPred[iSucc[j + i]]
                        <7>1. i \in negNat
                            BY <4>2
                        <7>2. \A k \in negNat:  j + k = k + j
                            BY <3>2
                        <7>3. j + i = i + j
                            BY <7>1, <7>2, spec
                        <7> QED
                            BY <7>3
                    <6> QED
                        BY <6>1, <6>2, <6>3, <6>4
                <5>2. -.Succ[-.i] + Succ[j] = iPred[iSucc[j + i]]
                    <6>1. -.Succ[-.i] + Succ[j] = iSucc[-.Succ[-.i] + j]
                        <7>1. -.Succ[-.i] \in Int
                            BY <4>2, minus_neg_nat_in_nat, succIsNat,
                                minus_nat_in_int
                        <7>2. j \in Nat
                            BY <3>2
                        <7> QED
                            BY <7>1, <7>2, addint_succ_nat
                    <6>2. @ = iSucc[j + -.Succ[-.i]]
                        <7>1. -.Succ[-.i] \in negNat
                            BY <4>2, minus_neg_nat_in_nat, succIsNat,
                                minus_nat_in_neg_nat
                        <7>2. \A k \in negNat:  j + k = k + j
                            BY <3>2
                        <7>3. j + -.Succ[-.i] = -.Succ[-.i] + j
                            BY <7>1, <7>2, spec
                        <7> QED
                            BY <7>3
                    <6>3. @ = iSucc[iPred[j + i]]
                        <7>1. j \in Int
                            BY <3>2, nat_in_int
                        <7>2. -.i \in Nat
                            BY <4>2, minus_neg_nat_in_nat
                        <7>3. j + -.Succ[-.i] = iPred[j + -.-.i]
                            BY <7>1, <7>2, addint_succ_negnat
                        <7>4. -.-.i = i
                            <8>1. i \in Int
                                BY <4>2, neg_nat_in_int
                            <8> QED
                                BY <8>1, minus_involutive
                        <7> QED
                            BY <7>3, <7>4
                    <6>4. @ = iPred[iSucc[j + i]]
                        <7>1. j + i \in Int
                            <8>1. j \in Int
                                BY <3>2, nat_in_int
                            <8>2. i \in Int
                                BY <4>2, neg_nat_in_int
                            <8> QED
                                BY <8>1, <8>2, addIsInt
                        <7> QED
                            BY <7>1, iSucciPredCommute
                    <6> QED
                        BY <6>1, <6>2, <6>3, <6>4
                <5> QED
                    BY <5>1, <5>2
            <4> QED
                BY <4>1, <4>2, neg_nat_induction
        <3> QED
            BY <3>1, <3>2, NatInduction
    <2> QED
        BY <2>1, <2>2, int_union_nat_negnat
<1>2. \A j \in negNat:  \A i \in Int:
        j + i = i + j
    <2>1. \A j \in negNat:  \A i \in Nat:
            j + i = i + j
        <3>1. \A i \in Nat:  0 + i = i + 0
            <4>1. 0 + 0 = 0 + 0
                OBVIOUS
            <4>2. ASSUME
                    NEW i \in Nat,
                    0 + i = i + 0
                  PROVE 0 + Succ[i] = Succ[i] + 0
                \* The level 5 proof is the same as
                \* for step <1>1!<2>1!<3>1!<4>2 .
                <5>1. 0 + Succ[i] = iSucc[0 + i]
                    <6>1. 0 \in Int
                        BY zero_in_int
                    <6>2. i \in Nat
                        BY <4>2
                    <6> QED
                        BY <6>1, <6>2 DEF addint_succ_nat
                <5>2. @ = iSucc[i + 0]
                    BY <4>2
                <5>3. @ = iSucc[i]
                    <6>1. i \in Int
                        BY <4>2, nat_in_int
                    <6>2. i + 0 = i
                        BY <6>1, addint_0
                    <6> QED
                        BY <6>2
                <5>4. @ = Succ[i]
                    <6>1. i \in Nat
                        BY <4>2
                    <6>2. i \in Int
                        BY <4>2, nat_in_int
                    <6> QED
                        BY <6>1, <6>2 DEF iSucc
                <5>5. @ = Succ[i] + 0
                    <6>1. Succ[i] \in Nat
                        BY <4>2, succIsNat
                    <6>2. Succ[i] \in Int
                        BY <6>1, nat_in_int
                    <6> QED
                        BY <6>2, add_0
                <5> QED
                    BY <5>1, <5>2, <5>3, <5>4, <5>5
            <4> QED
                BY <4>1, <4>2, NatInduction
        <3>2. ASSUME
                NEW j \in negNat,
                \A i \in Nat:  j + i = i + j
              PROVE
                \A i \in Nat:
                    -.Succ[-.j] + i = i + -.Succ[-.j]
            <4>1. -.Succ[-.j] + 0 = 0 + -.Succ[-.j]
                <5>1. -.Succ[-.j] + 0 = -.Succ[-.j]
                    <6>1. -.Succ[-.j] \in Int
                        <7>1. -.j \in Nat
                            BY <3>2, minus_neg_nat_in_nat
                        <7>2. Succ[-.j] \in Nat
                            BY <7>1, succIsNat
                        <7> QED
                            BY <7>2, minus_nat_in_int
                    <6> QED
                        BY <6>1, add_0
                <5>2. @ = iPred[j]
                    <6>1. j \in Int
                        BY <3>2, neg_nat_in_int
                    <6>2. j \notin Nat \ {0}
                        BY <3>2, neg_nat_not_in_nat_setminus_0
                    <6> QED
                        BY <6>1, <6>2 DEF iPred
                <5>3. @ = iPred[j + 0]
                    <6>1. j \in Int
                        BY <3>2, neg_nat_in_int
                    <6>2. j + 0 = j
                        BY <6>1, add_0
                    <6> QED
                        BY <6>2
                <5>4. @ = iPred[0 + j]
                    <6>1. 0 \in Nat
                        BY zeroIsNat
                    <6>2. \A k \in Nat:  j + k = k + j
                        BY <3>2
                    <6>3. j + 0 = 0 + j
                        BY <6>1, <6>2
                    <6> QED
                        BY <6>3
                <5>5. @ = iPred[0 + -.-.j]
                    <6>1. j \in Int
                        BY <3>2, neg_nat_in_int
                    <6>2. -.-.j = j
                        BY <6>1, minus_involutive
                    <6> QED
                        BY <6>2
                <5>6. @ = 0 + -.Succ[-.j]
                    <6>1. 0 \in Int
                        BY zeroIsNat, nat_in_int
                    <6>2. -.j \in Nat
                        BY <3>2, minus_neg_nat_in_nat
                    <6> QED
                        BY <6>1, <6>2, addint_succ_negnat
                <5> QED
                    BY <5>1, <5>2, <5>3, <5>4, <5>5, <5>6
            <4>2. ASSUME
                    NEW i \in Nat,
                    -.Succ[-.j] + i = i + -.Succ[-.j]
                  PROVE
                    -.Succ[-.j] + Succ[i] = Succ[i] + -.Succ[-.j]
                <5>1. -.Succ[-.j] + Succ[i] = iSucc[iPred[j + i]]
                    <6>1. -.Succ[-.j] + Succ[i] =
                            iSucc[-.Succ[-.j] + i]
                        <7>1. -.Succ[-.j] \in Int
                            <8>1. j \in negNat
                                BY <3>2
                            <8>2. -.j \in Nat
                                BY <8>1, minus_neg_nat_in_nat
                            <8>3. Succ[-.j] \in Nat
                                BY <8>2, succIsNat
                            <8> QED
                                BY <8>3, minus_nat_in_int
                        <7>2. i \in Nat
                            BY <4>2
                        <7> QED
                            BY <7>1, <7>2, addint_succ_nat
                    <6>2. @ = iSucc[i + -.Succ[-.j]]
                        BY <4>2
                    <6>3. @ = iSucc[iPred[i + j]]
                        <7>1. i \in Int
                            BY <4>2, nat_in_int
                        <7>2. -.j \in Nat
                            BY <3>2, minus_neg_nat_in_nat
                        <7>3. -.-.j = j
                            BY <3>2, neg_nat_in_int, minus_involutive
                        <7> QED
                            BY <7>1, <7>2, <7>3, addint_succ_negnat
                    <6>4. @ = iSucc[iPred[j + i]]
                        <7>1. i \in Nat
                            BY <4>2
                        <7>2. j + i = i + j
                            BY <3>2, <7>1
                        <7> QED
                            BY <7>2
                    <6> QED
                        BY <6>1, <6>2, <6>3, <6>4
                <5>2. Succ[i] + -.Succ[-.j] = iSucc[iPred[j + i]]
                    <6>1. Succ[i] + -.Succ[-.j] =
                            iPred[Succ[i] + -.-.j]
                        <7>1. Succ[i] \in Int
                            BY <4>2, succIsNat, nat_in_int
                        <7>2. -.j \in Nat
                            BY <3>2, minus_neg_nat_in_nat
                        <7> QED
                            BY <7>1, <7>2, addint_succ_negnat
                    <6>2. @ = iPred[Succ[i] + j]
                        <7>1. j \in Int
                            BY <3>2, neg_nat_in_int
                        <7>2. -.-.j = j
                            BY <7>1, minus_involutive
                        <7> QED
                            BY <7>2
                    <6>3. @ = iPred[j + Succ[i]]
                        <7>1. Succ[i] \in Nat
                            BY <4>2, succIsNat
                        <7>2. \A k \in Nat:  j + k = k + j
                            BY <3>2
                        <7>3. j + Succ[i] = Succ[i] + j
                            BY <7>1, <7>2
                        <7> QED
                            BY <7>3
                    <6>4. @ = iPred[iSucc[j + i]]
                        <7>1. j \in Int
                            BY <3>2, neg_nat_in_int
                        <7>2. i \in Nat
                            BY <4>2
                        <7> QED
                            BY <7>1, <7>2, addint_succ_nat
                    <6>5. @ = iSucc[iPred[j + i]]
                        <7>1. j + i \in Int
                            <8>1. j \in Int
                                BY <3>2, neg_nat_in_int
                            <8>2. i \in Int
                                BY <4>2, nat_in_int
                            <8> QED
                                BY <8>1, <8>2, addIsInt
                        <7> QED
                            BY <7>1, iSucciPredCommute
                    <6> QED
                        BY <6>1, <6>2, <6>3, <6>4, <6>5
                <5> QED
                    BY <5>1, <5>2
            <4> QED
                BY <4>1, <4>2, NatInduction
        <3> QED
            BY <3>1, <3>2, neg_nat_induction
    <2>2. \A j \in negNat:  \A i \in negNat:
            j + i = i + j
        <3>1. \A i \in negNat:  0 + i = i + 0
            <4>1. 0 + 0 = 0 + 0
                OBVIOUS
            <4>2. ASSUME NEW i \in negNat, 0 + i = i + 0
                  PROVE 0 + -.Succ[-.i] = -.Succ[-.i] + 0
                <5>1. 0 + -.Succ[-.i] = iPred[i]
                    <6>1. 0 + -.Succ[-.i] = iPred[0 + -.-.i]
                        <7>1. 0 \in Int
                            BY zero_in_int
                        <7>2. -.i \in Nat
                            BY <4>2, minus_neg_nat_in_nat
                        <7> QED
                            BY <7>1, <7>2, addint_succ_negnat
                    <6>2. @ = iPred[0 + i]
                        <7>1. -.-.i = i
                            BY <4>2, neg_nat_in_int, minus_involutive
                        <7> QED
                            BY <7>1
                    <6>3. @ = iPred[i + 0]
                        BY <4>2
                    <6>4. @ = iPred[i]
                        <7>1. i \in Int
                            BY <4>2, neg_nat_in_int
                        <7>2. i + 0 = i
                            BY <7>1, add_0
                        <7> QED
                            BY <7>2
                    <6> QED
                        BY <6>1, <6>2, <6>3, <6>4
                <5>2. -.Succ[-.i] + 0 = iPred[i]
                    <6>1. -.Succ[-.i] + 0 = -.Succ[-.i]
                        <7>1. -.Succ[-.i] \in Int
                            <8>1. -.i \in Nat
                                BY <4>2, minus_neg_nat_in_nat
                            <8>2. Succ[-.i] \in Nat
                                BY <8>1, succIsNat
                            <8> QED
                                BY <8>2, minus_nat_in_int
                        <7> QED
                            BY <7>1, add_0
                    <6>2. @ = iPred[i]
                        <7>1. i \in Int
                            BY <4>2, neg_nat_in_int
                        <7>2. i \notin Nat \ {0}
                            BY <4>2, neg_nat_not_in_nat_setminus_0
                        <7> QED
                            BY <7>1, <7>2 DEF iPred
                    <6> QED
                        BY <6>1, <6>2
                <5> QED
                    BY <5>1, <5>2
            <4> QED
                BY <4>1, <4>2, neg_nat_induction
        <3>2. ASSUME NEW j \in negNat,
                \A i \in negNat:  j + i = i + j
              PROVE \A i \in negNat:
                        -.Succ[-.j] + i = i + -.Succ[-.j]
            <4>1. -.Succ[-.j] + 0 = 0 + -.Succ[-.j]
                <5>1. -.Succ[-.j] + 0 = iPred[j]
                    <6>1. -.Succ[-.j] + 0 = -.Succ[-.j]
                        <7>1. -.Succ[-.j] \in Int
                            <8>1. -.j \in Nat
                                BY <3>2, minus_neg_nat_in_nat
                            <8>2. Succ[-.j] \in Nat
                                BY <8>1, succIsNat
                            <8> QED
                                BY <8>2, minus_nat_in_int
                        <7> QED
                            BY <7>1, add_0
                    <6>2. @ = iPred[j]
                        <7>1. j \in Int
                            BY <3>2, neg_nat_in_int
                        <7>2. j \notin Nat \ {0}
                            BY <3>2, neg_nat_not_in_nat_setminus_0
                        <7> QED
                            BY <7>1, <7>2 DEF iPred
                    <6> QED
                        BY <6>1, <6>2
                <5>2. 0 + -.Succ[-.j] = iPred[j]
                    <6>1. 0 + -.Succ[-.j] = iPred[0 + -.-.j]
                        <7>1. 0 \in Int
                            BY zero_in_int
                        <7>2. -.j \in Nat
                            BY <3>2, minus_neg_nat_in_nat
                        <7> QED
                            BY <7>1, <7>2, addint_succ_negnat
                    <6>2. @ = iPred[0 + j]
                        <7>1. j \in Int
                            BY <3>2, neg_nat_in_int
                        <7>2. -.-.j = j
                            BY <7>1, minus_involutive
                        <7> QED
                            BY <7>1, <7>2
                    <6>3. @ = iPred[j + 0]
                        <7>1. 0 \in negNat
                            BY neg0 DEF negNat
                        <7>2. \A k \in negNat:  j + k = k + j
                            BY <3>2
                        <7>3. j + 0 = 0 + j
                            BY <7>1, <7>2, spec
                        <7> QED
                            BY <7>3
                    <6>4. @ = iPred[j]
                        <7>1. j \in Int
                            BY <3>2, neg_nat_in_int
                        <7> QED
                            BY <7>1, add_0
                    <6> QED
                        BY <6>1, <6>2, <6>3, <6>4
                <5> QED
                    BY <5>1, <5>2
            <4>2. ASSUME NEW i \in negNat,
                    -.Succ[-.j] + i = i + -.Succ[-.j]
                  PROVE -.Succ[-.j] + -.Succ[-.i] =
                        -.Succ[-.i] + -.Succ[-.j]
                <5>1. -.Succ[-.j] + -.Succ[-.i] = iPred[iPred[i + j]]
                    <6>1. -.Succ[-.j] + -.Succ[-.i] =
                            iPred[-.Succ[-.j] + -.-.i]
                        <7>1. -.Succ[-.j] \in Int
                            <8>1. -.j \in Nat
                                BY <3>2, minus_neg_nat_in_nat
                            <8>2. Succ[-.j] \in Nat
                                BY <8>1, succIsNat
                            <8> QED
                                BY <8>2, minus_nat_in_int
                        <7>2. -.i \in Nat
                            BY <4>2, minus_neg_nat_in_nat
                        <7> QED
                            BY <7>1, <7>2, addint_succ_negnat
                    <6>2. @ = iPred[-.Succ[-.j] + i]
                        <7>1. i \in Int
                            BY <4>2, neg_nat_in_int
                        <7>2. -.-.i = i
                            BY <7>1, minus_involutive
                        <7> QED
                            BY <7>1, <7>2
                    <6>3. @ = iPred[i + -.Succ[-.j]]
                        BY <4>2
                    <6>4. @ = iPred[iPred[i + -.-.j]]
                        <7>1. i \in Int
                            BY <4>2, neg_nat_in_int
                        <7>2. -.j \in Nat
                            BY <3>2, minus_neg_nat_in_nat
                        <7>3. i + -.Succ[-.j] = iPred[i + -.-.j]
                            BY <7>1, <7>2, addint_succ_negnat
                        <7> QED
                            BY <7>3
                    <6>5. @ = iPred[iPred[i + j]]
                        <7>1. j \in Int
                            BY <3>2, neg_nat_in_int
                        <7>2. -.-.j = j
                            BY <7>1, minus_involutive
                        <7> QED
                            BY <7>2
                    <6> QED
                        BY <6>1, <6>2, <6>3, <6>4, <6>5
                <5>2. -.Succ[-.i] + -.Succ[-.j] = iPred[iPred[i + j]]
                    <6>1. -.Succ[-.i] + -.Succ[-.j] =
                            iPred[-.Succ[-.i] + -.-.j]
                        <7>1. -.Succ[-.i] \in Int
                            <8>1. -.i \in Nat
                                BY <4>2, minus_neg_nat_in_nat
                            <8>2. Succ[-.i] \in Nat
                                BY <8>1, succIsNat
                            <8> QED
                                BY <8>2, minus_nat_in_int
                        <7>2. -.j \in Nat
                            BY <3>2, minus_neg_nat_in_nat
                        <7> QED
                            BY <7>1, <7>2, addint_succ_negnat
                    <6>2. @ = iPred[-.Succ[-.i] + j]
                        <7>1. -.-.j = j
                            <8>1. j \in Int
                                BY <3>2, neg_nat_in_int
                            <8> QED
                                BY <8>1, minus_involutive
                        <7> QED
                            BY <7>1
                    <6>3. @ = iPred[j + -.Succ[-.i]]
                        <7>1. -.Succ[-.i] \in negNat
                            <8>1. -.i \in Nat
                                BY <4>2, minus_neg_nat_in_nat
                            <8>2. Succ[-.i] \in Nat
                                BY <8>1, succIsNat
                            <8> QED
                                BY <8>2, minus_nat_in_neg_nat
                        <7>2. \A k \in negNat:  j + k = k + j
                            BY <3>2
                        <7>3. j + -.Succ[-.i] = -.Succ[-.i] + j
                            BY <7>1, <7>2
                        <7> QED
                            BY <7>3
                    <6>4. @ = iPred[iPred[j + -.-.i]]
                        <7>1. j \in Int
                            BY <3>2, neg_nat_in_int
                        <7>2. -.i \in Nat
                            BY <4>2, minus_neg_nat_in_nat
                        <7> QED
                            BY <7>1, <7>2, addint_succ_negnat
                    <6>5. @ = iPred[iPred[j + i]]
                        <7>1. -.-.i = i
                            <8>1. i \in Int
                                BY <4>2, neg_nat_in_int
                            <8> QED
                                BY <8>1, minus_involutive
                        <7> QED
                            BY <7>1
                    <6>6. @ = iPred[iPred[i + j]]
                        <7>1. i \in negNat
                            BY <4>2
                        <7>2. \A k \in negNat:  j + k = k + j
                            BY <3>2
                        <7>3. j + i = i + j
                            BY <7>1, <7>2, spec
                        <7> QED
                            BY <7>3
                    <6> QED
                        BY <6>1, <6>2, <6>3, <6>4,
                            <6>5, <6>6
                <5> QED
                    BY <5>1, <5>2
            <4> QED
                BY <4>1, <4>2, neg_nat_induction
        <3> QED
            BY <3>1, <3>2, neg_nat_induction
    <2> QED
        BY <2>1, <2>2, int_union_nat_negnat
<1> QED
    BY <1>1, <1>2

*)
theorem AddCommutative:
    "\<forall> j \<in> Int:  \<forall> i \<in> Int:
        j + i = i + j"
    proof -
    have s1_1: "\<forall> j \<in> Nat:  \<forall> i \<in> Int:
        j + i = i + j"
        proof -
        have s2_1: "\<forall> j \<in> Nat:
            \<forall> i \<in> Nat:
                j + i = i + j"
            proof -
            have s3_1: "\<forall> i \<in> Nat:
                0 + i = i + 0"
                proof -
                have s4_1: "0 + 0 = 0 + 0"
                    by auto
                have s4_2: "\<And> i.  \<lbrakk>
                    i \<in> Nat;
                    0 + i = i + 0
                    \<rbrakk>
                    \<Longrightarrow>
                        0 + Succ[i] = Succ[i] + 0"
                    proof -
                    fix "i" :: "c"
                    assume s4_2_asm1: "i \<in> Nat"
                    assume s4_2_asm2: "0 + i = i + 0"
                    have s5_1: "0 + Succ[i] = iSucc[0 + i]"
                        proof -
                        have s6_1: "0 \<in> Int"
                            using zero_in_int by auto
                        have s6_2: "i \<in> Nat"
                            using s4_2_asm1 by auto
                        show ?thesis
                            unfolding add_def
                            using s6_1 s6_2
                                addint_succ[of "0"]
                            by auto
                        qed
                    have s5_2: "iSucc[0 + i] = iSucc[i + 0]"
                        using s4_2_asm2 by auto
                    have s5_3: "iSucc[i + 0] = iSucc[i]"
                        proof -
                        have s6_1: "i \<in> Int"
                            using s4_2_asm1 nat_in_int
                            by auto
                        show ?thesis
                            unfolding add_def
                            using s6_1 addint_0[of "i"]
                            by auto
                        qed
                    have s5_4: "iSucc[i] = Succ[i]"
                        unfolding iSucc_def
                        using s4_2_asm1 by auto
                    have s5_5: "Succ[i] = Succ[i] + 0"
                        proof -
                        have s6_1: "Succ[i] \<in> Nat"
                            using s4_2_asm1 succIsNat by auto
                        have s6_2: "Succ[i] \<in> Int"
                            using s6_1 nat_in_int by auto
                        show ?thesis
                            unfolding add_def
                            using s6_2 addint_0 by auto
                        qed
                    show "0 + Succ[i] = Succ[i] + 0"
                        using s5_1 s5_2 s5_3 s5_4 s5_5
                        by auto
                    qed
                show ?thesis
                    using s4_1 s4_2
                        natInduct[of "\<lambda> i.  0 + i = i + 0"]
                    by auto
                qed
            have s3_2: "\<And> j.  \<lbrakk>
                j \<in> Nat;
                \<forall> i \<in> Nat:  j + i = i + j
                \<rbrakk>
                \<Longrightarrow>
                    \<forall> i \<in> Nat:
                        Succ[j] + i = i + Succ[j]"
                proof -
                fix "j" :: "c"
                assume s3_2_asm1: "j \<in> Nat"
                assume s3_2_asm2: "\<forall> i \<in> Nat:
                    j + i = i + j"
                have s4_1: "Succ[j] + 0 = 0 + Succ[j]"
                    proof -
                    have s5_1: "Succ[j] + 0 = Succ[j]"
                        proof -
                        have s6_1: "Succ[j] \<in> Int"
                            using s3_2_asm1 succIsNat
                                nat_in_int by auto
                        show ?thesis
                            using s6_1 add_0 by auto
                        qed
                    also have s5_2: "... = iSucc[j]"
                        unfolding iSucc_def
                        using s3_2_asm1 nat_in_int
                        by auto
                    also have s5_3: "... = iSucc[j + 0]"
                        proof -
                        have s6_1: "j \<in> Int"
                            using s3_2_asm1 nat_in_int by auto
                        have s6_2: "j + 0 = j"
                            using s6_1 add_0 by auto
                        show ?thesis
                            using s6_2 by auto
                        qed
                    also have s5_4: "... = iSucc[0 + j]"
                        proof -
                        have s6_1: "j + 0 = 0 + j"
                            using s3_2_asm2 zeroIsNat by auto
                        show ?thesis
                            using s6_1 by auto
                        qed
                    also have s5_5: "... = 0 + Succ[j]"
                        proof -
                        have s6_1: "0 \<in> Int"
                            using zero_in_int by auto
                        have s6_2: "j \<in> Nat"
                            using s3_2_asm1 by auto
                        have s6_3: "0 \<in> Int ==>
                            j \<in> Nat ==>
                            0 + Succ[j] = iSucc[0 + j]"
                            using addint_succ_nat
                            by auto
                        have s6_4: "
                            0 + Succ[j] = iSucc[0 + j]"
                            using s6_1 s6_2 s6_3 by auto
                        have s6_5: "iSucc[0 + j] = 0 + Succ[j]"
                            using s6_4 by auto
                        show ?thesis
                            using s6_5 by auto
                        qed
                    finally show ?thesis .
                    qed
                have s4_2: "\<And> i.  \<lbrakk>
                    i \<in> Nat;
                    Succ[j] + i = i + Succ[j]
                    \<rbrakk> \<Longrightarrow>
                        Succ[j] + Succ[i] = Succ[i] + Succ[j]"
                    proof -
                    fix "i" :: "c"
                    assume s4_2_asm1: "i \<in> Nat"
                    assume s4_2_asm2: "Succ[j] + i = i + Succ[j]"
                    have s5_1: "Succ[j] + Succ[i] = iSucc[iSucc[j + i]]"
                        proof -
                        have s6_1: "Succ[j] + Succ[i] = iSucc[Succ[j] + i]"
                            proof -
                            have s7_1: "Succ[j] \<in> Int"
                                using s3_2_asm1 succIsNat nat_in_int
                                by auto
                            have s7_2: "i \<in> Nat"
                                using s4_2_asm1 succIsNat by auto
                            show ?thesis
                                using s7_1 s7_2 addint_succ_nat
                                by auto
                            qed
                        also have s6_2: "... = iSucc[i + Succ[j]]"
                            using s4_2_asm2 by auto
                        also have s6_3: "... = iSucc[iSucc[i + j]]"
                            proof -
                            have s7_1: "i \<in> Int"
                                using s4_2_asm1 nat_in_int by auto
                            have s7_2: "j \<in> Nat"
                                using s3_2_asm1 by auto
                            show ?thesis
                                using s7_1 s7_2 addint_succ_nat
                                by auto
                            qed
                        also have s6_4: "... = iSucc[iSucc[j + i]]"
                            using s3_2_asm2 s4_2_asm1 spec by auto
                        finally show ?thesis
                            by auto
                        qed
                    have s5_2: "Succ[i] + Succ[j] = iSucc[iSucc[j + i]]"
                        proof -
                        have s6_1: "Succ[i] + Succ[j] = iSucc[Succ[i] + j]"
                            proof -
                            have s7_1: "Succ[i] \<in> Int"
                                using s4_2_asm1 succIsNat nat_in_int
                                by auto
                            have s7_2: "j \<in> Nat"
                                using s3_2_asm1 succIsNat by auto
                            show ?thesis
                                using s7_1 s7_2 addint_succ_nat by auto
                            qed
                        also have s6_2: "... = iSucc[j + Succ[i]]"
                            proof -
                            have s7_1: "Succ[i] \<in> Nat"
                                using s4_2_asm1 succIsNat by auto
                            show ?thesis
                                using s7_1 s3_2_asm2 by auto
                            qed
                        also have s6_3: "... = iSucc[iSucc[j + i]]"
                            proof -
                            have s7_1: "j \<in> Int"
                                using s3_2_asm1 nat_in_int
                                by auto
                            have s7_2: "i \<in> Nat"
                                using s4_2_asm1 by auto
                            show ?thesis
                                using s7_1 s7_2 addint_succ_nat
                                by auto
                            qed
                        finally show ?thesis
                            by auto
                        qed
                    show "Succ[j] + Succ[i] = Succ[i] + Succ[j]"
                        using s5_1 s5_2 by auto
                    qed
                show "\<forall> i \<in> Nat:  Succ[j] + i = i + Succ[j]"
                    using s4_1 s4_2 natInduct
                    by auto
                qed
            show ?thesis
                using s3_1 s3_2 natInduct by auto
            qed
        have s2_2: "\<forall> j \<in> Nat:
            \<forall> i \<in> negNat:  j + i = i + j"
            proof -
            have s3_1: "\<forall> i \<in> negNat:  0 + i = i + 0"
                proof -
                have s4_1: "0 + 0 = 0 + 0"
                    by auto
                have s4_2: "\<And> i.  \<lbrakk>
                    i \<in> negNat;
                    0 + i = i + 0
                    \<rbrakk> \<Longrightarrow>
                        0 + -.Succ[-.i] = -.Succ[-.i] + 0"
                    proof -
                    fix "i" :: "c"
                    assume s4_2_asm1: "i \<in> negNat"
                    assume s4_2_asm2: "0 + i = i + 0"
                    have s5_1: "0 + -.Succ[-.i] = iPred[0 + i]"
                        proof -
                        have s6_1: "0 \<in> Int"
                            using zero_in_int by auto
                        have s6_2: "-.i \<in> Nat"
                            using s4_2_asm1 minus_neg_nat_in_nat
                            by auto
                        have s6_3: "0 + -.Succ[-.i] = iPred[0 + -.-.i]"
                            using s6_1 s6_2 addint_succ_negnat
                            by auto
                        have s6_4: "-.-.i = i"
                            proof -
                            have s7_1: "i \<in> Int"
                                using s4_2_asm1 neg_nat_in_int by auto
                            show ?thesis
                                using s7_1 minus_involutive by auto
                            qed
                        show ?thesis
                            using s6_3 s6_4 by auto
                        qed
                    also have s5_2: "... = iPred[i + 0]"
                        using s4_2_asm2 by auto
                    also have s5_3: "... = iPred[i]"
                        proof -
                        have s6_1: "i \<in> Int"
                            using s4_2_asm1 neg_nat_in_int by auto
                        have s6_2: "i + 0 = i"
                            using s6_1 add_0 by auto
                        show ?thesis
                            using s6_2 by auto
                        qed
                    also have s5_4: "... = -.Succ[-.i]"
                        proof -
                        have s6_1: "i \<in> Int"
                            using s4_2_asm1 neg_nat_in_int by auto
                        have s6_2: "i \<notin> Nat \<setminus> {0}"
                            using s4_2_asm1 neg_nat_not_in_nat_setminus_0
                            by auto
                        show ?thesis
                            unfolding iPred_def
                            using s6_1 s6_2 by auto
                        qed
                    also have s5_5: "... = -.Succ[-.i] + 0"
                        proof -
                        have s6_1: "-.i \<in> Nat"
                            using s4_2_asm1 minus_neg_nat_in_nat by auto
                        have s6_2: "Succ[-.i] \<in> Nat"
                            using s6_1 succIsNat by auto
                        have s6_3: "-.Succ[-.i] \<in> Int"
                            using s6_2 minus_nat_in_int by auto
                        show ?thesis
                            using s6_3 add_0 by auto
                        qed
                    finally show "0 + -.Succ[-.i] = -.Succ[-.i] + 0"
                        by auto
                    qed
                show ?thesis
                    using s4_1 s4_2 neg_nat_induction by auto
                qed
            have s3_2: "\<And> j.  \<lbrakk>
                j \<in> Nat;
                \<forall> i \<in> negNat:  j + i = i + j
                \<rbrakk> \<Longrightarrow>
                    \<forall> i \<in> negNat:  Succ[j] + i = i + Succ[j]"
                proof -
                fix "j" :: "c"
                assume s3_2_asm1: "j \<in> Nat"
                assume s3_2_asm2: "\<forall> i \<in> negNat:
                    j + i = i + j"
                have s4_1: "Succ[j] + 0 = 0 + Succ[j]"
                    proof -
                    have s5_1: "Succ[j] + 0 = Succ[j]"
                        proof -
                        have s6_1: "Succ[j] \<in> Int"
                            using s3_2_asm1 succIsNat nat_in_int by auto
                        show ?thesis
                            using s6_1 add_0 by auto
                        qed
                    also have s5_2: "... = iSucc[j]"
                        proof -
                        have s6_1: "j \<in> Int"
                            using s3_2_asm1 nat_in_int by auto
                        have s6_2: "j \<in> Nat"
                            using s3_2_asm1 by auto
                        show ?thesis
                            unfolding iSucc_def
                            using s6_1 s6_2 by auto
                        qed
                    also have s5_3: "... = iSucc[j + 0]"
                        proof -
                        have s6_1: "j \<in> Int"
                            using s3_2_asm1 nat_in_int by auto
                        have s6_2: "j + 0 = j"
                            using s6_1 add_0 by auto
                        show ?thesis
                            using s6_2 by auto
                        qed
                    also have s5_4: "... = iSucc[0 + j]"
                        proof -
                        have s6_1: "0 \<in> negNat"
                            unfolding negNat_def
                            using neg0 by auto
                        show ?thesis
                            using s3_2_asm2 s6_1 by auto
                        qed
                    also have s5_5: "... = 0 + Succ[j]"
                        proof -
                        have s6_1: "0 \<in> Int"
                            using zero_in_int by auto
                        have s6_2: "j \<in> Nat"
                            using s3_2_asm1 by auto
                        show ?thesis
                            using s6_1 s6_2 addint_succ_nat by auto
                        qed
                    finally show ?thesis
                        by auto
                    qed
                have s4_2: "\<And> i.  \<lbrakk>
                    i \<in> negNat;
                    Succ[j] + i = i + Succ[j]
                    \<rbrakk> \<Longrightarrow>
                        Succ[j] + -.Succ[-.i] = -.Succ[-.i] + Succ[j]"
                    proof -
                    fix "i" :: "c"
                    assume s4_2_asm1: "i \<in> negNat"
                    assume s4_2_asm2: "Succ[j] + i = i + Succ[j]"
                    have s5_1: "Succ[j] + -.Succ[-.i] = iPred[iSucc[j + i]]"
                        proof -
                        have s6_1: "Succ[j] + -.Succ[-.i] =
                            iPred[Succ[j] + i]"
                            proof -
                            have s7_1: "Succ[j] \<in> Int"
                                using s3_2_asm1 succIsNat nat_in_int
                                by auto
                            have s7_2: "-.i \<in> Nat"
                                using s4_2_asm1 minus_neg_nat_in_nat
                                by auto
                            have s7_3: "-.-.i = i"
                                using s4_2_asm1 neg_nat_in_int
                                    minus_involutive by auto
                            have s7_4: "Succ[j] + -.Succ[-.i] =
                                iPred[Succ[j] + -.-.i]"
                                using s7_1 s7_2 addint_succ_negnat
                                by auto
                            show ?thesis
                                using s7_3 s7_4 by auto
                            qed
                        also have s6_2: "... = iPred[i + Succ[j]]"
                            using s4_2_asm2 by auto
                        also have s6_3: "... = iPred[iSucc[i + j]]"
                            proof -
                            have s7_1: "i \<in> Int"
                                using s4_2_asm1 neg_nat_in_int by auto
                            have s7_2: "j \<in> Nat"
                                using s3_2_asm1 by auto
                            show ?thesis
                                using s7_1 s7_2 addint_succ_nat by auto
                            qed
                        also have s6_4: "... = iPred[iSucc[j + i]]"
                            proof -
                            have s7_1: "i \<in> negNat"
                                using s4_2_asm1 by auto
                            have s7_2: "\<forall> k \<in> negNat:
                                j + k = k + j"
                                using s3_2_asm2 by auto
                            have s7_3: "j + i = i + j"
                                using s7_1 s7_2 spec by auto
                            show ?thesis
                                using s7_3 by auto
                            qed
                        finally show ?thesis
                            by auto
                        qed
                    have s5_2: "-.Succ[-.i] + Succ[j] = iPred[iSucc[j + i]]"
                        proof -
                        have s6_1: "-.Succ[-.i] + Succ[j] =
                            iSucc[-.Succ[-.i] + j]"
                            proof -
                            have s7_1: "-.Succ[-.i] \<in> Int"
                                using s4_2_asm1 minus_neg_nat_in_nat succIsNat
                                    minus_nat_in_int by auto
                            have s7_2: "j \<in> Nat"
                                using s3_2_asm1 by auto
                            show ?thesis
                                using s7_1 s7_2 addint_succ_nat by auto
                            qed
                        also have s6_2: "... = iSucc[j + -.Succ[-.i]]"
                            proof -
                            have s7_1: "-.Succ[-.i] \<in> negNat"
                                using s4_2_asm1 minus_neg_nat_in_nat succIsNat
                                    minus_nat_in_neg_nat by auto
                            have s7_2: "\<forall> k \<in> negNat:
                                    j + k = k + j"
                                using s3_2_asm2 by auto
                            have s7_3: "j + -.Succ[-.i] = -.Succ[-.i] + j"
                                using s7_1 s7_2 spec by auto
                            show ?thesis
                                using s7_3 by auto
                            qed
                        also have s6_3: "... = iSucc[iPred[j + i]]"
                            proof -
                            have s7_1: "j \<in> Int"
                                using s3_2_asm1 nat_in_int by auto
                            have s7_2: "-.i \<in> Nat"
                                using s4_2_asm1 minus_neg_nat_in_nat by auto
                            have s7_3: "j + -.Succ[-.i] = iPred[j + -.-.i]"
                                using s7_1 s7_2 addint_succ_negnat by auto
                            have s7_4: "-.-.i = i"
                                proof -
                                have s8_1: "i \<in> Int"
                                    using s4_2_asm1 neg_nat_in_int by auto
                                show ?thesis
                                    using s8_1 minus_involutive by auto
                                qed
                            show ?thesis
                                using s7_3 s7_4 by auto
                            qed
                        also have s6_4: "... = iPred[iSucc[j + i]]"
                            proof -
                            have s7_1: "j + i \<in> Int"
                                proof -
                                have s8_1: "j \<in> Int"
                                    using s3_2_asm1 nat_in_int by auto
                                have s8_2: "i \<in> Int"
                                    using s4_2_asm1 neg_nat_in_int by auto
                                show ?thesis
                                    using s8_1 s8_2 addIsInt by auto
                                qed
                            show ?thesis
                                using s7_1 iSucciPredCommute by auto
                            qed
                        finally show ?thesis
                            by auto
                        qed
                    show "Succ[j] + -.Succ[-.i] = -.Succ[-.i] + Succ[j]"
                        using s5_1 s5_2 by auto
                    qed
                show "\<forall> i \<in> negNat:  Succ[j] + i = i + Succ[j]"
                    using s4_1 s4_2 neg_nat_induction
                    by auto
                qed
            show ?thesis
                using s3_1 s3_2 natInduct by auto
            qed
        show ?thesis
            proof -
            have s3_1: "\<And> j.  \<And> i.
                j \<in> Nat => (
                    i \<in> Int => (
                        j + i = i + j))"
                proof auto
                fix "j" :: "c"
                fix "i" :: "c"
                assume s4_1: "j \<in> Nat"
                assume s4_2: "i \<in> Int"
                have s4_3: "i \<in> Nat ==> j + i = i + j"
                    proof -
                    assume s5_1: "i \<in> Nat"
                    show "j + i = i + j"
                        using s4_1 s5_1 s2_1 by auto
                    qed
                have s4_4: "i \<in> negNat ==> j + i = i + j"
                    proof -
                    assume s5_1: "i \<in> negNat"
                    show "j + i = i + j"
                        using s4_1 s5_1 s2_2 by auto
                    qed
                show "j + i = i + j"
                    using s4_2 s4_3 s4_4 int_union_nat_negnat by auto
                qed
            show ?thesis
                using s3_1 by auto
            qed
        qed
    have s1_2: "\<forall> j \<in> negNat:  \<forall> i \<in> Int:
        j + i = i + j"
        proof -
        have s2_1: "\<forall> j \<in> negNat:  \<forall> i \<in> Nat:
            j + i = i + j"
            proof -
            have s3_1: "\<forall> i \<in> Nat:  0 + i = i + 0"
                proof -
                have s4_1: "0 + 0 = 0 + 0"
                    by auto
                have s4_2: "\<And> i.  \<lbrakk>
                    i \<in> Nat;
                    0 + i = i + 0
                    \<rbrakk> \<Longrightarrow>
                        0 + Succ[i] = Succ[i] + 0
                    "
                    proof -
                    fix "i" :: "c"
                    assume s4_2_asm1: "i \<in> Nat"
                    assume s4_2_asm2: "0 + i = i + 0"
                    have s5_1: "0 + Succ[i] = iSucc[0 + i]"
                        proof -
                        have s6_1: "0 \<in> Int"
                            using zero_in_int by auto
                        have s6_2: "i \<in> Nat"
                            using s4_2_asm1 by auto
                        show ?thesis
                            using s6_1 s6_2 addint_succ_nat by auto
                        qed
                    also have s5_2: "... = iSucc[i + 0]"
                        using s4_2_asm2 by force
                    also have s5_3: "... = iSucc[i]"
                        proof -
                        have s6_1: "i \<in> Int"
                            using s4_2_asm1 nat_in_int by auto
                        have s6_2: "i + 0 = i"
                            using s6_1 add_0 by auto
                        show ?thesis
                            using s6_2 by force
                        qed
                    also have s5_4: "... = Succ[i]"
                        proof -
                        have s6_1: "i \<in> Nat"
                            using s4_2_asm1 by auto
                        have s6_2: "i \<in> Int"
                            using s4_2_asm1 nat_in_int by auto
                        show ?thesis
                            unfolding iSucc_def
                            using s6_1 s6_2 by auto
                        qed
                    also have s5_5: "... = Succ[i] + 0"
                        proof -
                        have s6_1: "Succ[i] \<in> Nat"
                            using s4_2_asm1 succIsNat by auto
                        have s6_2: "Succ[i] \<in> Int"
                            using s6_1 nat_in_int by auto
                        show ?thesis
                            using s6_2 add_0 by auto
                        qed
                    finally show "0 + Succ[i] = Succ[i] + 0"
                        (* . did not work *)
                        using s5_1 s5_2 s5_3 s5_4 s5_5 by auto
                    qed
                show ?thesis
                    using s4_1 s4_2 natInduct by auto
                qed
            have s3_2: "\<And> j.  \<lbrakk>
            j \<in> negNat;
            \<forall> i \<in> Nat:  j + i = i + j
                \<rbrakk> \<Longrightarrow>
                    \<forall> i \<in> Nat:
                        -.Succ[-.j] + i = i + -.Succ[-.j]
            "
                proof -
                fix "j" :: "c"
                assume s3_2_asm1: "j \<in> negNat"
                assume s3_2_asm2: "\<forall> i \<in> Nat:
                    j + i = i + j"
                have s4_1: "-.Succ[-.j] + 0 = 0 + -.Succ[-.j]"
                    proof -
                    have s5_1: "-.Succ[-.j] + 0 = -.Succ[-.j]"
                        proof -
                        have s6_1: "-.Succ[-.j] \<in> Int"
                            proof -
                            have s7_1: "-.j \<in> Nat"
                                using s3_2_asm1 minus_neg_nat_in_nat
                                by auto
                            have s7_2: "Succ[-.j] \<in> Nat"
                                using s7_1 succIsNat by auto
                            show ?thesis
                                using s7_2 minus_nat_in_int by auto
                            qed
                        show ?thesis
                            using s6_1 add_0 by auto
                        qed
                    also have s5_2: "... = iPred[j]"
                        proof -
                        have s6_1: "j \<in> Int"
                            using s3_2_asm1 neg_nat_in_int by auto
                        have s6_2: "j \<notin> Nat \<setminus> {0}"
                            using s3_2_asm1 neg_nat_not_in_nat_setminus_0
                            by auto
                        show ?thesis
                            unfolding iPred_def
                            using s6_1 s6_2 by auto
                        qed
                    also have s5_3: "... = iPred[j + 0]"
                        proof -
                        have s6_1: "j \<in> Int"
                            using s3_2_asm1 neg_nat_in_int by auto
                        have s6_2: "j + 0 = j"
                            using s6_1 add_0 by auto
                        show ?thesis
                            using s6_2 by auto
                        qed
                    also have s5_4: "... = iPred[0 + j]"
                        proof -
                        have s6_1: "0 \<in> Nat"
                            using zeroIsNat by auto
                        have s6_2: "\<forall> k \<in> Nat:
                            j + k = k + j"
                            using s3_2_asm2 by auto
                        have s6_3: "j + 0 = 0 + j"
                            using s6_1 s6_2 by auto
                        show ?thesis
                            using s6_3 by auto
                        qed
                    also have s5_5: "... = iPred[0 + -.-.j]"
                        proof -
                        have s6_1: "j \<in> Int"
                            using s3_2_asm1 neg_nat_in_int by auto
                        have s6_2: "-.-.j = j"
                            using s6_1 minus_involutive by auto
                        show ?thesis
                            using s6_2 by auto
                        qed
                    also have s5_6: "... = 0 + -.Succ[-.j]"
                        proof -
                        have s6_1: "0 \<in> Int"
                            using zeroIsNat nat_in_int by auto
                        have s6_2: "-.j \<in> Nat"
                            using s3_2_asm1 minus_neg_nat_in_nat by auto
                        show ?thesis
                            using s6_1 s6_2 addint_succ_negnat by auto
                        qed
                    finally show ?thesis .
                    qed
                have s4_2: "\<And> i.  \<lbrakk>
                        i \<in> Nat;
                        -.Succ[-.j] + i = i + -.Succ[-.j]
                    \<rbrakk> \<Longrightarrow>
                        -.Succ[-.j] + Succ[i] = Succ[i] + -.Succ[-.j]"
                    proof -
                    fix "i" :: "c"
                    assume s4_2_idom: "i \<in> Nat"
                    assume s4_2_induct: "-.Succ[-.j] + i = i + -.Succ[-.j]"
                    have s5_1: "-.Succ[-.j] + Succ[i] = iSucc[iPred[j + i]]"
                        proof -
                        have s6_1: "-.Succ[-.j] + Succ[i] =
                                iSucc[-.Succ[-.j] + i]"
                            proof -
                            have s7_1: "-.Succ[-.j] \<in> Int"
                                proof -
                                have s8_1: "j \<in> negNat"
                                    using s3_2_asm1 by auto
                                have s8_2: "-.j \<in> Nat"
                                    using s8_1 minus_neg_nat_in_nat by auto
                                have s8_3: "Succ[-.j] \<in> Nat"
                                    using s8_2 succIsNat by auto
                                show ?thesis
                                    using s8_3 minus_nat_in_int by auto
                                qed
                            have s7_2: "i \<in> Nat"
                                using s4_2_idom by auto
                            show ?thesis
                                using s7_1 s7_2 addint_succ_nat by auto
                            qed
                        also have s6_2: "... = iSucc[i + -.Succ[-.j]]"
                            using s4_2_induct by auto
                        also have s6_3: "... = iSucc[iPred[i + j]]"
                            proof -
                            have s7_1: "i \<in> Int"
                                using s4_2_idom nat_in_int by auto
                            have s7_2: "-.j \<in> Nat"
                                using s3_2_asm1 minus_neg_nat_in_nat by auto
                            have s7_3: "-.-.j = j"
                                using s3_2_asm1 neg_nat_in_int
                                    minus_involutive by auto
                            show ?thesis
                                using s7_1 s7_2 s7_3 addint_succ_negnat
                                by auto
                            qed
                        also have s6_4: "... = iSucc[iPred[j + i]]"
                            proof -
                            have s7_1: "i \<in> Nat"
                                using s4_2_idom by auto
                            have s7_2: "j + i = i + j"
                                using s3_2_asm2 s7_1 spec by auto
                            show ?thesis
                                using s7_2 by auto
                            qed
                        finally show ?thesis .
                        qed
                    have s5_2: "Succ[i] + -.Succ[-.j] = iSucc[iPred[j + i]]"
                        proof -
                        have s6_1: "Succ[i] + -.Succ[-.j] =
                            iPred[Succ[i] + -.-.j]"
                            proof -
                            have s7_1: "Succ[i] \<in> Int"
                                using s4_2_idom succIsNat nat_in_int by auto
                            have s7_2: "-.j \<in> Nat"
                                using s3_2_asm1 minus_neg_nat_in_nat by auto
                            show ?thesis
                                using s7_1 s7_2 addint_succ_negnat by auto
                            qed
                        also have s6_2: "... = iPred[Succ[i] + j]"
                            proof -
                            have s7_1: "j \<in> Int"
                                using s3_2_asm1 neg_nat_in_int by auto
                            have s7_2: "-.-.j = j"
                                using s7_1 minus_involutive by auto
                            show ?thesis
                                using s7_2 by auto
                            qed
                        also have s6_3: "... = iPred[j + Succ[i]]"
                            proof -
                            have s7_1: "Succ[i] \<in> Nat"
                                using s4_2_idom succIsNat by auto
                            have s7_2: "\<forall> k \<in> Nat:
                                j + k = k + j"
                                using s3_2_asm2 by auto
                            have s7_3: "j + Succ[i] = Succ[i] + j"
                                using s7_1 s7_2 by auto
                            show ?thesis
                                using s7_3 by auto
                            qed
                        also have s6_4: "... = iPred[iSucc[j + i]]"
                            proof -
                            have s7_1: "j \<in> Int"
                                using s3_2_asm1 neg_nat_in_int by auto
                            have s7_2: "i \<in> Nat"
                                using s4_2_idom by auto
                            show ?thesis
                                using s7_1 s7_2 addint_succ_nat by auto
                            qed
                        also have s6_5: "... = iSucc[iPred[j + i]]"
                            proof -
                            have s7_1: "j + i \<in> Int"
                                proof -
                                have s8_1: "j \<in> Int"
                                    using s3_2_asm1 neg_nat_in_int by auto
                                have s8_2: "i \<in> Int"
                                    using s4_2_idom nat_in_int by auto
                                show ?thesis
                                    using s8_1 s8_2 addIsInt by auto
                                qed
                            show ?thesis
                                using s7_1 iSucciPredCommute by auto
                            qed
                        finally show ?thesis .
                        qed
                    show "-.Succ[-.j] + Succ[i] = Succ[i] + -.Succ[-.j]"
                        using s5_1 s5_2 by auto
                    qed
                show "\<forall> i \<in> Nat:
                        -.Succ[-.j] + i = i + -.Succ[-.j]"
                    using s4_1 s4_2 natInduct by auto
                qed
            show ?thesis
                using s3_1 s3_2 neg_nat_induction by auto
            qed
        have s2_2: "\<forall> j \<in> negNat:  \<forall> i \<in> negNat:
            j + i = i + j"
            proof -
            have s3_1: "\<forall> i \<in> negNat:  0 + i = i + 0"
                proof -
                have s4_1: "0 + 0 = 0 + 0"
                    by auto
                have s4_2: "\<And> i.  \<lbrakk>
                        i \<in> negNat;
                        0 + i = i + 0
                    \<rbrakk> \<Longrightarrow>
                        0 + -.Succ[-.i] = -.Succ[-.i] + 0"
                    proof -
                    fix "i" :: "c"
                    assume s4_2_idom: "i \<in> negNat"
                    assume s4_2_induct: "0 + i = i + 0"
                    have s5_1: "0 + -.Succ[-.i] = iPred[i]"
                        proof -
                        have s6_1: "0 + -.Succ[-.i] = iPred[0 + -.-.i]"
                            proof -
                            have s7_1: "0 \<in> Int"
                                using zero_in_int by auto
                            have s7_2: "-.i \<in> Nat"
                                using s4_2_idom minus_neg_nat_in_nat by auto
                            show ?thesis
                                using s7_1 s7_2 addint_succ_negnat by auto
                            qed
                        also have s6_2: "... = iPred[0 + i]"
                            proof -
                            have s7_1: "-.-.i = i"
                                using s4_2_idom neg_nat_in_int
                                    minus_involutive by auto
                            show ?thesis
                                using s7_1 by auto
                            qed
                        also have s6_3: "... = iPred[i + 0]"
                            using s4_2_induct by auto
                        also have s6_4: "... = iPred[i]"
                            proof -
                            have s7_1: "i \<in> Int"
                                using s4_2_idom neg_nat_in_int by auto
                            have s7_2: "i + 0 = i"
                                using s7_1 add_0 by auto
                            show ?thesis
                                using s7_2 by auto
                            qed
                        finally show ?thesis .
                        qed
                    have s5_2: "-.Succ[-.i] + 0 = iPred[i]"
                        proof -
                        have s6_1: "-.Succ[-.i] + 0 = -.Succ[-.i]"
                            proof -
                            have s7_1: "-.Succ[-.i] \<in> Int"
                                proof -
                                have s8_1: "-.i \<in> Nat"
                                    using s4_2_idom minus_neg_nat_in_nat
                                    by auto
                                have s8_2: "Succ[-.i] \<in> Nat"
                                    using s8_1 succIsNat by auto
                                show ?thesis
                                    using s8_2 minus_nat_in_int by auto
                                qed
                            show ?thesis
                                using s7_1 add_0 by auto
                            qed
                        also have s6_2: "... = iPred[i]"
                            proof -
                            have s7_1: "i \<in> Int"
                                using s4_2_idom neg_nat_in_int by auto
                            have s7_2: "i \<notin> Nat \<setminus> {0}"
                                using s4_2_idom neg_nat_not_in_nat_setminus_0
                                by auto
                            show ?thesis
                                unfolding iPred_def
                                using s7_1 s7_2 by auto
                            qed
                        finally show ?thesis .
                        qed
                    show "0 + -.Succ[-.i] = -.Succ[-.i] + 0"
                        using s5_1 s5_2 by auto
                    qed
                show ?thesis
                    using s4_1 s4_2 neg_nat_induction by auto
                qed
            have s3_2: "\<And> j.  \<lbrakk>
                    j \<in> negNat;
                    \<forall> i \<in> negNat:  j + i = i + j
                \<rbrakk> \<Longrightarrow>
                    \<forall> i \<in> negNat:
                        -.Succ[-.j] + i = i + -.Succ[-.j]"
                proof -
                fix "j" :: "c"
                assume s3_2_jdom: "j \<in> negNat"
                assume s3_2_induct: "\<forall> i \<in> negNat:
                    j + i = i + j"
                have s4_1: "-.Succ[-.j] + 0 = 0 + -.Succ[-.j]"
                    proof -
                    have s5_1: "-.Succ[-.j] + 0 = iPred[j]"
                        proof -
                        have s6_1: "-.Succ[-.j] + 0 = -.Succ[-.j]"
                            proof -
                            have s7_1: "-.Succ[-.j] \<in> Int"
                                proof -
                                have s8_1: "-.j \<in> Nat"
                                    using s3_2_jdom minus_neg_nat_in_nat
                                    by auto
                                have s8_2: "Succ[-.j] \<in> Nat"
                                    using s8_1 succIsNat by auto
                                show ?thesis
                                    using s8_2 minus_nat_in_int by auto
                                qed
                            show ?thesis
                                using s7_1 add_0 by auto
                            qed
                        also have s6_2: "... = iPred[j]"
                            proof -
                            have s7_1: "j \<in> Int"
                                using s3_2_jdom neg_nat_in_int by auto
                            have s7_2: "j \<notin> Nat \<setminus> {0}"
                                using s3_2_jdom neg_nat_not_in_nat_setminus_0
                                by auto
                            show ?thesis
                                unfolding iPred_def
                                using s7_1 s7_2 by auto
                            qed
                        finally show ?thesis .
                        qed
                    have s5_2: "0 + -.Succ[-.j] = iPred[j]"
                        proof -
                        have s6_1: "0 + -.Succ[-.j] = iPred[0 + -.-.j]"
                            proof -
                            have s7_1: "0 \<in> Int"
                                using zero_in_int by auto
                            have s7_2: "-.j \<in> Nat"
                                using s3_2_jdom minus_neg_nat_in_nat
                                by auto
                            show ?thesis
                                using s7_1 s7_2 addint_succ_negnat by auto
                            qed
                        also have s6_2: "... = iPred[0 + j]"
                            proof -
                            have s7_1: "j \<in> Int"
                                using s3_2_jdom neg_nat_in_int by auto
                            have s7_2: "-.-.j = j"
                                using s7_1 minus_involutive by auto
                            show ?thesis
                                using s7_1 s7_2 by auto
                            qed
                        also have s6_3: "... = iPred[j + 0]"
                            proof -
                            have s7_1: "0 \<in> negNat"
                                unfolding negNat_def
                                using neg0 by auto
                            have s7_2: "\<forall> k \<in> negNat:
                                j + k = k + j"
                                using s3_2_induct by auto
                            have s7_3: "j + 0 = 0 + j"
                                using s7_1 s7_2 spec by auto
                            show ?thesis
                                using s7_3 by auto
                            qed
                        also have s6_4: "... = iPred[j]"
                            proof -
                            have s7_1: "j \<in> Int"
                                using s3_2_jdom neg_nat_in_int by auto
                            show ?thesis
                                using s7_1 add_0 by auto
                            qed
                        finally show ?thesis .
                        qed
                    show ?thesis
                        using s5_1 s5_2 by auto
                    qed
                have s4_2: "\<And> i.  \<lbrakk>
                        i \<in> negNat;
                        -.Succ[-.j] + i = i + -.Succ[-.j]
                    \<rbrakk> \<Longrightarrow>
                        -.Succ[-.j] + -.Succ[-.i] =
                        -.Succ[-.i] + -.Succ[-.j]"
                    proof -
                    fix "i" :: "c"
                    assume s4_2_idom: "i \<in> negNat"
                    assume s4_2_induct: "-.Succ[-.j] + i = i + -.Succ[-.j]"
                    have s5_1: "-.Succ[-.j] + -.Succ[-.i] =
                        iPred[iPred[i + j]]"
                        proof -
                        have s6_1: "-.Succ[-.j] + -.Succ[-.i] =
                                iPred[-.Succ[-.j] + -.-.i]"
                            proof -
                            have s7_1: "-.Succ[-.j] \<in> Int"
                                proof -
                                have s8_1: "-.j \<in> Nat"
                                    using s3_2_jdom minus_neg_nat_in_nat
                                    by auto
                                have s8_2: "Succ[-.j] \<in> Nat"
                                    using s8_1 succIsNat by auto
                                show ?thesis
                                    using s8_2 minus_nat_in_int by auto
                                qed
                            have s7_2: "-.i \<in> Nat"
                                using s4_2_idom minus_neg_nat_in_nat
                                by auto
                            have s7_3: "-.Succ[-.j] \<in> Int
                                ==>
                                -.i \<in> Nat
                                ==>
                                -.Succ[-.j] + -.Succ[-.i] =
                                        iPred[-.Succ[-.j] + -.-.i]"
                                using addint_succ_negnat[
                                    of "-.Succ[-.j]" "-.i"]
                                by auto
                            show ?thesis
                                by (rule s7_3, rule s7_1, rule s7_2)
                            qed
                        also have s6_2: "... = iPred[-.Succ[-.j] + i]"
                            proof -
                            have s7_1: "i \<in> Int"
                                using s4_2_idom neg_nat_in_int by auto
                            have s7_2: "-.-.i = i"
                                using s7_1 minus_involutive by auto
                            show ?thesis
                                using s7_1 s7_2 by auto
                            qed
                        also have s6_3: "... = iPred[i + -.Succ[-.j]]"
                            using s4_2_induct by auto
                        also have s6_4: "... = iPred[iPred[i + -.-.j]]"
                            proof -
                            have s7_1: "i \<in> Int"
                                using s4_2_idom neg_nat_in_int by auto
                            have s7_2: "-.j \<in> Nat"
                                using s3_2_jdom minus_neg_nat_in_nat by auto
                            have s7_3: "i + -.Succ[-.j] = iPred[i + -.-.j]"
                                using s7_1 s7_2 addint_succ_negnat by auto
                            show ?thesis
                                using s7_3 by auto
                            qed
                        also have s6_5: "... = iPred[iPred[i + j]]"
                            proof -
                            have s7_1: "j \<in> Int"
                                using s3_2_jdom neg_nat_in_int by auto
                            have s7_2: "-.-.j = j"
                                using s7_1 minus_involutive by auto
                            show ?thesis
                                using s7_2 by auto
                            qed
                        finally show ?thesis .
                        qed
                    have s5_2: "-.Succ[-.i] + -.Succ[-.j] =
                        iPred[iPred[i + j]]"
                        proof -
                        have s6_1: "-.Succ[-.i] + -.Succ[-.j] =
                                iPred[-.Succ[-.i] + -.-.j]"
                            proof -
                            have s7_1: "-.Succ[-.i] \<in> Int"
                                proof -
                                have s8_1: "-.i \<in> Nat"
                                    using s4_2_idom minus_neg_nat_in_nat
                                    by auto
                                have s8_2: "Succ[-.i] \<in> Nat"
                                    using s8_1 succIsNat by auto
                                show ?thesis
                                    using s8_2 minus_nat_in_int by auto
                                qed
                            have s7_2: "-.j \<in> Nat"
                                using s3_2_jdom minus_neg_nat_in_nat by auto
                            show ?thesis
                                using s7_1 s7_2 addint_succ_negnat by auto
                            qed
                        also have s6_2: "... = iPred[-.Succ[-.i] + j]"
                            proof -
                            have s7_1: "-.-.j = j"
                                proof -
                                have s8_1: "j \<in> Int"
                                    using s3_2_jdom neg_nat_in_int by auto
                                show ?thesis
                                    using s8_1 minus_involutive by auto
                                qed
                            show ?thesis
                                using s7_1 by auto
                            qed
                        also have s6_3: "... = iPred[j + -.Succ[-.i]]"
                            proof -
                            have s7_1: "-.Succ[-.i] \<in> negNat"
                                proof -
                                have s8_1: "-.i \<in> Nat"
                                    using s4_2_idom minus_neg_nat_in_nat
                                    by auto
                                have s8_2: "Succ[-.i] \<in> Nat"
                                    using s8_1 succIsNat by auto
                                show ?thesis
                                    using s8_2 minus_nat_in_neg_nat by auto
                                qed
                            have s7_2: "\<forall> k \<in> negNat:
                                j + k = k + j"
                                using s3_2_induct by auto
                            have s7_3: "j + -.Succ[-.i] = -.Succ[-.i] + j"
                                using s7_1 s7_2 by auto
                            show ?thesis
                                using s7_3 by auto
                            qed
                        also have s6_4: "... = iPred[iPred[j + -.-.i]]"
                            proof -
                            have s7_1: "j \<in> Int"
                                using s3_2_jdom neg_nat_in_int by auto
                            have s7_2: "-.i \<in> Nat"
                                using s4_2_idom minus_neg_nat_in_nat by auto
                            show ?thesis
                                using s7_1 s7_2 addint_succ_negnat by auto
                            qed
                        also have s6_5: "... = iPred[iPred[j + i]]"
                            proof -
                            have s7_1: "-.-.i = i"
                                proof -
                                have s8_1: "i \<in> Int"
                                    using s4_2_idom neg_nat_in_int by auto
                                show ?thesis
                                    using s8_1 minus_involutive by auto
                                qed
                            show ?thesis
                                using s7_1 by auto
                            qed
                        also have s6_6: "... = iPred[iPred[i + j]]"
                            proof -
                            have s7_1: "i \<in> negNat"
                                using s4_2_idom by auto
                            have s7_2: "\<forall> k \<in> negNat:
                                j + k = k + j"
                                using s3_2_induct by auto
                            have s7_3: "j + i = i + j"
                                using s7_1 s7_2 spec by auto
                            show ?thesis
                                using s7_3 by auto
                            qed
                        finally show ?thesis .
                        qed
                    show "-.Succ[-.j] + -.Succ[-.i] =
                        -.Succ[-.i] + -.Succ[-.j]"
                        using s5_1 s5_2 by auto
                    qed
                show "\<forall> i \<in> negNat:
                        -.Succ[-.j] + i = i + -.Succ[-.j]"
                    using s4_1 s4_2 neg_nat_induction by auto
                qed
            show ?thesis
                using s3_1 s3_2 neg_nat_induction by auto
            qed
        show ?thesis
            proof -
            have s3_1: "\<And> j.  \<And> i.
                j \<in> negNat => (
                    i \<in> Int => (
                        j + i = i + j))"
                proof auto
                fix "j" :: "c"
                fix "i" :: "c"
                assume s4_1: "j \<in> negNat"
                assume s4_2: "i \<in> Int"
                have s4_3: "i \<in> Nat ==> j + i = i + j"
                    proof -
                    assume s5_1: "i \<in> Nat"
                    show "j + i = i + j"
                        using s4_1 s5_1 s2_1 by auto
                    qed
                have s4_4: "i \<in> negNat ==> j + i = i + j"
                    proof -
                    assume s5_1: "i \<in> negNat"
                    show "j + i = i + j"
                        using s4_1 s5_1 s2_2 by auto
                    qed
                show "j + i = i + j"
                    using s4_2 s4_3 s4_4 int_union_nat_negnat by auto
                qed
            show ?thesis
                using s3_1 by auto
            qed
        qed
    show ?thesis
        using s1_1 s1_2 int_union_nat_negnat by auto
    qed


theorem AddCommutative_sequent:
    assumes mdom: "m \<in> Int" and ndom: "n \<in> Int"
    shows "m + n = n + m"
    using mdom ndom AddCommutative by auto


theorem add_0_left:
    assumes mdom: "m \<in> Int"
    shows "0 + m = m"
    proof -
    have s1_1: "m + 0 = m"
        using mdom add_0 by auto
    have s1_2: "m + 0 = 0 + m"
        using mdom zero_in_int AddCommutative_sequent by auto
    show ?thesis
        using s1_1 s1_2 by auto
    qed



(*----------------------------------------------------------------------------*)
(* Associativity of addition. *)


(*
THEOREM iSuccRightDistributesAdd ==
    ASSUME NEW a \in Int
    PROVE \A b \in Int:  iSucc[a + b] = a + iSucc[b]
<1>1. ASSUME NEW b \in Nat
      PROVE iSucc[a + b] = a + iSucc[b]
    <2>1. iSucc[a + b] = a + Succ[b]
        <3>1. a \in Int
            OBVIOUS
        <3>2. b \in Nat
            BY <1>1
        <3> QED
            BY <3>1, <3>2, addint_succ_nat
    <2>2. @ = a + iSucc[b]
        <3>1. b \in Nat
            BY <1>1
        <3>2. b \in Int
            BY <1>1, nat_in_int
        <3>3. iSucc[b] = Succ[b]
            BY <3>1, <3>2 DEF iSucc
        <3> QED
            BY <3>3
    <2> QED
        BY <2>1, <2>2
<1>2. \A b \in negNat:  iSucc[a + b] = a + iSucc[b]
    <2>1. iSucc[a + 0] = a + iSucc[0]
        <3>1. iSucc[a + 0] = a + Succ[0]
            <4>1. a \in Int
                OBVIOUS
            <4>2. 0 \in Nat
                BY zeroIsNat
            <4> QED
                BY <4>1, <4>2, addint_succ_nat
        <3>2. @ = a + iSucc[0]
            <4>1. 0 \in Nat
                BY zeroIsNat
            <4>2. 0 \in Int
                BY zeroIsNat, nat_in_int
            <4>3. iSucc[0] = Succ[0]
                BY <4>1, <4>2 DEF iSucc
            <4> QED
                BY <4>3
        <3> QED
            BY <3>1, <3>2
    <2>2. ASSUME NEW b \in negNat,
            iSucc[a + b] = a + iSucc[b]
          PROVE iSucc[a + -.Succ[-.b]] = a + iSucc[-.Succ[-.b]]
        <3>1. iSucc[a + -.Succ[-.b]] = iSucc[iPred[a + b]]
            <4>1. a \in Int
                OBVIOUS
            <4>2. -.b \in Nat
                BY <2>2, minus_neg_nat_in_nat
            <4>3. a + -.Succ[-.b] = iPred[a + -.-.b]
                BY <4>1, <4>2, addint_succ_negnat
            <4>4. -.-.b = b
                <5>1. b \in Int
                    BY <2>2, neg_nat_in_int
                <5> QED
                    BY <5>1, minus_involutive
            <4>5. a + -.Succ[-.b] = iPred[a + b]
                BY <4>3, <4>4
            <4> QED
                BY <4>5
        <3>2. @ = iPred[iSucc[a + b]]
            <4>1. a + b \in Int
                <5>1. a \in Int
                    OBVIOUS
                <5>2. b \in Int
                    BY <2>2, neg_nat_in_int
                <5> QED
                    BY <5>1, <5>2, addIsInt
            <4> QED
                BY <4>1, iSucciPredCommute
        <3>3. CASE b = 0
            <4>1. iPred[iSucc[a + b]] = a
                <5>1. iPred[iSucc[a + b]] = iPred[iSucc[a + 0]]
                    BY <3>3
                <5>2. @ = iPred[iSucc[a]]
                    <6>1. a + 0 = a
                        BY a \in Int, add_0
                    <6> QED
                        BY <6>1
                <5>3. @ = a
                    <6>1. a \in Int
                        OBVIOUS
                    <6> QED
                        BY <6>1, iSucciPredCommute, spec
                <5> QED
                    BY <5>1, <5>2, <5>3
            <4>2. a + iSucc[-.Succ[-.b]] = a
                <5>1. a + iSucc[-.Succ[-.b]] = a + iSucc[-.Succ[0]]
                    BY <3>3
                <5>2. @ = a + iSucc[-.1]
                    OBVIOUS  \* 1 is an abbreviation
                <5>3. @ = a + -.Pred[-.-.1]
                    <6>1. -.1 \in Int
                        BY oneIsNat, minus_nat_in_int
                    <6>2. -.1 \notin Nat
                        <7>1. 1 \in Nat \ {0}
                            BY oneIsNat succNotZero
                        <7> QED
                            BY <7>1, minus_nat_0_in_negnat_0,
                                neg_nat_0_not_in_nat
                    <6>3. iSucc[-.1] = -.Pred[-.-.1]
                        BY <6>1, <6>2 DEF iSucc
                    <6> QED
                        BY <6>3
                <5>4. @ = a + -.Pred[1]
                    <6>1. -.-.1 = 1
                        <7>1. 1 \in Int
                            BY oneIsNat nat_in_int
                        <7> QED
                            BY <7>1, minus_involutive
                    <6> QED
                        BY <6>1
                <5>5. @ = a + -.0
                    BY pred_1
                <5>6. @ = a + 0
                    BY neg0
                <5>7. @ = a
                    BY a \in Int, add_0
                <5> QED
                    BY <5>1, <5>2, <5>3, <5>4,
                        <5>5, <5>6, <5>7
            <4> QED
                BY <3>1, <3>2, <4>1, <4>2
        <3>4. CASE b # 0
            <4>1. iPred[iSucc[a + b]] =
                    iPred[a + iSucc[b]]
                BY <2>2
            <4>2. @ = a + -.Succ[-.iSucc[b]]
                <5>1. a \in Int
                    OBVIOUS
                <5>2. /\ -.iSucc[b] \in Nat
                      /\ iSucc[b] \in negNat
                    <6>1. b \in negNat \ {0}
                        BY <2>2, <3>4
                    <6>2. iSucc[b] = -.Pred[-.b]
                        <7>1. b \in Int
                            BY <6>1, neg_nat_in_int
                        <7>2. b \notin Nat
                            BY <6>1, neg_nat_0_not_in_nat
                        <7> QED
                            BY <7>1, <7>2 DEF iSucc
                    <6>3. Pred[-.b] \in Nat
                        <7>1. -.b \in Nat \ {0}
                            BY <6>1, minus_neg_nat_0_in_nat_0
                        <7> QED
                            BY <7>1, Pred_in_nat
                    <6>4. -.iSucc[b] \in Nat
                        <7>1. -.iSucc[b] = Pred[-.b]
                            <8>1. -.iSucc[b] = -.-.Pred[-.b]
                                BY <6>2
                            <8>2. Pred[-.b] \in Int
                                BY <6>3, nat_in_int
                            <8>3. -.-.Pred[-.b] = Pred[-.b]
                                BY <8>2, minus_involutive
                            <8> QED
                                BY <8>1, <8>3
                        <7> QED
                            BY <6>3, <7>1
                    <6>5. iSucc[b] \in negNat
                        BY <6>2, <6>3, minus_nat_in_neg_nat
                    <6> QED
                        BY <6>4, <6>5
                <5>3. a + -.Succ[-.iSucc[b]] =
                        iPred[a + -.-.iSucc[b]]
                    BY <5>1, <5>2, addint_succ_negnat
                <5>4. -.-.iSucc[b] = iSucc[b]
                    <6>1. iSucc[b] \in Int
                        BY <5>2, neg_nat_in_int
                    <6> QED
                        BY <6>1, minus_involutive
                <5> QED
                    BY <5>3, <5>4
            <4>3. @ = a + -.Succ[Pred[-.b]]
                <5>1. b \in Int
                    BY <2>2, neg_nat_in_int
                <5>2. b \notin Nat
                    <6>1. b \in negNat \ {0}
                        BY <2>2, <3>4
                    <6> QED
                        BY <6>1, neg_nat_0_not_in_nat
                <5>3. iSucc[b] = -.Pred[-.b]
                    BY <5>1, <5>2 DEF iSucc
                <5>4. -.iSucc[b] = -.-.Pred[-.b]
                    BY <5>3
                <5>5. -.-.Pred[-.b] = Pred[-.b]
                    <6>1. -.b \in Nat
                        BY <2>2, <3>4, minus_neg_nat_0_in_nat_0
                    <6>2. Pred[-.b] \in Nat
                        BY <6>1, Pred_in_nat
                    <6>3. Pred[-.b] \in Int
                        BY <6>2, nat_in_int
                    <6> QED
                        BY <6>3, minus_involutive
                <5>6. -.iSucc[b] = Pred[-.b]
                    BY <5>4, <5>5
                <5> QED
                    BY <5>6
            <4>4. @ = a + -.Pred[Succ[-.b]]
                <5>1. b \in negNat \ {0}
                    BY <2>2, <3>4
                <5>2. -.b \in Nat \ {0}
                    BY <5>1, minus_neg_nat_0_in_nat_0
                <5>3. Succ[Pred[-.b]] = Pred[Succ[-.b]]
                    BY <5>2, Succ_Pred_nat, Pred_Succ_nat
                <5> QED
                    BY <5>3
            <4>5. @ = a + -.Pred[-.-.Succ[-.b]]
                <5>1. -.b \in Nat
                    BY <2>2, minus_neg_nat_in_nat
                <5>2. Succ[-.b] \in Nat
                    BY <5>1, succIsNat
                <5>3. Succ[-.b] \in Int
                    BY <5>2, nat_in_int
                <5>4. -.-.Succ[-.b] = Succ[-.b]
                    BY <5>3, minus_involutive
                <5> QED
                    BY <5>4
            <4>6. @ = a + iSucc[-.Succ[-.b]]
                <5>1. -.b \in Nat
                    BY <2>2, minus_neg_nat_in_nat
                <5>2. Succ[-.b] \in Nat \ {0}
                    BY <5>1, succIsNat, succNotZero
                <5>3. -.Succ[-.b] \in negNat \ {0}
                    BY <5>2, minus_nat_0_in_negnat_0
                <5>4. -.Succ[-.b] \in Int
                    BY <5>3, neg_nat_in_int
                <5>5. -.Succ[-.b] \notin Nat
                    BY <5>3, neg_nat_0_not_in_nat
                <5> QED
                    BY <5>4, <5>5 DEF iSucc
            <4> QED
                BY <3>1, <3>2, <4>1, <4>2, <4>3,
                    <4>4, <4>5, <4>6
        <3> QED
            BY <3>3, <3>4
    <2> QED
        BY <2>1, <2>2, neg_nat_induction
<1> QED
    BY <1>1, <1>2
*)
theorem iSuccRightDistributesAdd:
    "\<forall> a \<in> Int:  \<forall> b \<in> Int:
        iSucc[a + b] = a + iSucc[b]"
    proof -
    {
    fix "a" :: "c"
    assume adom: "a \<in> Int"
    have s1_1: "\<forall> b \<in> Nat:  iSucc[a + b] = a + iSucc[b]"
        proof auto
        fix "b" :: "c"
        assume bdom: "b \<in> Nat"
        have s2_1: "iSucc[a + b] = a + Succ[b]"
            proof -
            have s3_1: "a \<in> Int"
                using adom by auto
            have s3_2: "b \<in> Nat"
                using bdom by auto
            show ?thesis
                using s3_1 s3_2 addint_succ_nat by auto
            qed
        also have s2_2: "... = a + iSucc[b]"
            proof -
            have s3_1: "b \<in> Nat"
                using bdom by auto
            have s3_2: "b \<in> Int"
                using bdom nat_in_int by auto
            have s3_3: "iSucc[b] = Succ[b]"
                unfolding iSucc_def
                using s3_1 s3_2 by auto
            show ?thesis
                using s3_3 by auto
            qed
        finally show "iSucc[a + b] = a + iSucc[b]" .
        qed
    have s1_2: "\<forall> b \<in> negNat:  iSucc[a + b] = a + iSucc[b]"
        proof -
        have s2_1: "iSucc[a + 0] = a + iSucc[0]"
            proof -
            have s3_1: "iSucc[a + 0] = a + Succ[0]"
                proof -
                have s4_1: "a \<in> Int"
                    using adom by auto
                have s4_2: "0 \<in> Nat"
                    using zeroIsNat by auto
                show ?thesis
                    using s4_1 s4_2 addint_succ_nat by auto
                qed
            have s3_2: "... = a + iSucc[0]"
                proof -
                have s4_1: "0 \<in> Nat"
                    using zeroIsNat by auto
                have s4_2: "0 \<in> Int"
                    using zeroIsNat nat_in_int by auto
                have s4_3: "iSucc[0] = Succ[0]"
                    unfolding iSucc_def
                    using s4_1 s4_2 by auto
                show ?thesis
                    using s4_3 by auto
                qed
            show ?thesis
                using s3_1 s3_2 by auto
            qed
        have s2_2: "\<And> b.  \<lbrakk>
            b \<in> negNat;
            iSucc[a + b] = a + iSucc[b]
            \<rbrakk> \<Longrightarrow>
                iSucc[a + -.Succ[-.b]] = a + iSucc[-.Succ[-.b]]"
            proof -
            fix "b" :: "c"
            assume s2_2_bdom: "b \<in> negNat"
            assume s2_2_induct: "iSucc[a + b] = a + iSucc[b]"
            have s3_1: "iSucc[a + -.Succ[-.b]] = iSucc[iPred[a + b]]"
                proof -
                have s4_1: "a \<in> Int"
                    using adom by auto
                have s4_2: "-.b \<in> Nat"
                    using s2_2_bdom minus_neg_nat_in_nat by auto
                have s4_3: "a + -.Succ[-.b] = iPred[a + -.-.b]"
                    using s4_1 s4_2 addint_succ_negnat by auto
                have s4_4: "-.-.b = b"
                    proof -
                    have s5_1: "b \<in> Int"
                        using s2_2_bdom neg_nat_in_int by auto
                    show ?thesis
                        using s5_1 minus_involutive by auto
                    qed
                have s4_5: "a + -.Succ[-.b] = iPred[a + b]"
                    using s4_3 s4_4 by auto
                show ?thesis
                    using s4_5 by auto
                qed
            have s3_2: "... = iPred[iSucc[a + b]]"
                proof -
                have s4_1: "a + b \<in> Int"
                    proof -
                    have s5_1: "a \<in> Int"
                        using adom by auto
                    have s5_2: "b \<in> Int"
                        using s2_2_bdom neg_nat_in_int by auto
                    show ?thesis
                        using s5_1 s5_2 addIsInt by auto
                    qed
                show ?thesis
                    using s4_1 iSucciPredCommute by auto
                qed
            have s3_3: "b = 0 ==>
                iSucc[a + -.Succ[-.b]] = a + iSucc[-.Succ[-.b]]"
                proof -
                assume s3_3_bdom: "b = 0"
                have s4_1: "iPred[iSucc[a + b]] = a"
                    proof -
                    have s5_1: "iPred[iSucc[a + b]] = iPred[iSucc[a + 0]]"
                        using s3_3_bdom by auto
                    also have s5_2: "... = iPred[iSucc[a]]"
                        proof -
                        have s6_1: "a + 0 = a"
                            using adom add_0 by auto
                        show ?thesis
                            using s6_1 by auto
                        qed
                    also have s5_3: "... = a"
                        using adom iSucciPredCommute spec by auto
                    finally show ?thesis .
                    qed
                have s4_2: "a + iSucc[-.Succ[-.b]] = a"
                    proof -
                    have s5_1: "a + iSucc[-.Succ[-.b]] =
                        a + iSucc[-.Succ[0]]"
                        using s3_3_bdom by auto
                    have s5_2: "... = a + iSucc[-.1]"
                        by auto
                    have s5_3: "... = a + -.Pred[-.-.1]"
                        (* `also` raises error:
                        empty result sequence
                        *)
                        proof -
                        have s6_1: "-.1 \<in> Int"
                            using oneIsNat minus_nat_in_int by auto
                        have s6_2: "-.1 \<notin> Nat"
                            proof -
                            have s7_1: "1 \<in> Nat \<setminus> {0}"
                                using oneIsNat succNotZero by auto
                            show ?thesis
                                using s7_1 minus_nat_0_in_negnat_0
                                    neg_nat_0_not_in_nat by auto
                            qed
                        have s6_3: "iSucc[-.1] = -.Pred[-.-.1]"
                            unfolding iSucc_def
                            using s6_1 s6_2 by auto
                        show ?thesis
                            using s6_3 by auto
                        qed
                    have s5_4: "... = a + -.Pred[1]"
                        proof -
                        have s6_1: "-.-.1 = 1"
                            proof -
                            have s7_1: "1 \<in> Int"
                                using oneIsNat nat_in_int by auto
                            show ?thesis
                                using s7_1 minus_involutive by auto
                            qed
                        show ?thesis
                            using s6_1 by auto
                        qed
                    have s5_5: "... = a + -.0"
                        using pred_1 by auto
                    have s5_6: "... = a + 0"
                        using neg0 by auto
                    have s5_7: "... = a"
                        using adom add_0 by auto
                    show ?thesis
                        using s5_1 s5_2 s5_3 s5_4 s5_5 s5_6 s5_7
                        by auto
                    qed
                show ?thesis
                    using s3_1 s3_2 s4_1 s4_2 by auto
                qed
            have s3_4: "b \<noteq> 0 ==>
                iSucc[a + -.Succ[-.b]] = a + iSucc[-.Succ[-.b]]"
                proof -
                assume s3_4_bdom: "b \<noteq> 0"
                have s4_1: "iPred[iSucc[a + b]] =
                        iPred[a + iSucc[b]]"
                    using s2_2_induct by auto
                also have s4_2: "... = a + -.Succ[-.iSucc[b]]"
                    proof -
                    have s5_1: "a \<in> Int"
                        using adom by auto
                    have s5_2: "-.iSucc[b] \<in> Nat \<and>
                                iSucc[b] \<in> negNat"
                        proof -
                        have s6_1: "b \<in> negNat \<setminus> {0}"
                            using s2_2_bdom s3_4_bdom by auto
                        have s6_2: "iSucc[b] = -.Pred[-.b]"
                            proof -
                            have s7_1: "b \<in> Int"
                                using s6_1 neg_nat_in_int by auto
                            have s7_2: "b \<notin> Nat"
                                using s6_1 neg_nat_0_not_in_nat by auto
                            show ?thesis
                                unfolding iSucc_def
                                using s7_1 s7_2 by auto
                            qed
                        have s6_3: "Pred[-.b] \<in> Nat"
                            proof -
                            have s7_1: "-.b \<in> Nat \<setminus> {0}"
                                using s6_1 minus_neg_nat_0_in_nat_0 by auto
                            show ?thesis
                                using s7_1 Pred_in_nat by auto
                            qed
                        have s6_4: "-.iSucc[b] \<in> Nat"
                            proof -
                            have s7_1: "-.iSucc[b] = Pred[-.b]"
                                proof -
                                have s8_1: "-.iSucc[b] = -.-.Pred[-.b]"
                                    using s6_2 by auto
                                have s8_2: "Pred[-.b] \<in> Int"
                                    using s6_3 nat_in_int by auto
                                have s8_3: "-.-.Pred[-.b] = Pred[-.b]"
                                    using s8_2 minus_involutive by auto
                                show ?thesis
                                    using s8_1 s8_3 by auto
                                qed
                            show ?thesis
                                using s6_3 s7_1 by auto
                            qed
                        have s6_5: "iSucc[b] \<in> negNat"
                            using s6_2 s6_3 minus_nat_in_neg_nat by auto
                        show ?thesis
                            using s6_4 s6_5 by auto
                        qed
                    have s5_3: "a + -.Succ[-.iSucc[b]] =
                        iPred[a + -.-.iSucc[b]]"
                        using s5_1 s5_2 addint_succ_negnat by auto
                    have s5_4: "-.-.iSucc[b] = iSucc[b]"
                        proof -
                        have s6_1: "iSucc[b] \<in> Int"
                            using s5_2 neg_nat_in_int by auto
                        show ?thesis
                            using s6_1 minus_involutive by auto
                        qed
                    show ?thesis
                        using s5_3 s5_4 by auto
                    qed
                also have s4_3: "... = a + -.Succ[Pred[-.b]]"
                    proof -
                    have s5_1: "b \<in> Int"
                        using s2_2_bdom neg_nat_in_int by auto
                    have s5_2: "b \<notin> Nat"
                        proof -
                        have s6_1: "b \<in> negNat \<setminus> {0}"
                            using s2_2_bdom s3_4_bdom by auto
                        show ?thesis
                            using s6_1 neg_nat_0_not_in_nat by auto
                        qed
                    have s5_3: "iSucc[b] = -.Pred[-.b]"
                        unfolding iSucc_def
                        using s5_1 s5_2 by auto
                    have s5_4: "-.iSucc[b] = -.-.Pred[-.b]"
                        using s5_3 by auto
                    have s5_5: "-.-.Pred[-.b] = Pred[-.b]"
                        proof -
                        have s6_1: "-.b \<in> Nat"
                            using s2_2_bdom s3_4_bdom
                                minus_neg_nat_0_in_nat_0
                            by auto
                        have s6_2: "Pred[-.b] \<in> Nat"
                            using s6_1 Pred_in_nat by auto
                        have s6_3: "Pred[-.b] \<in> Int"
                            using s6_2 nat_in_int by auto
                        show ?thesis
                            using s6_3 minus_involutive by auto
                        qed
                    have s5_6: "-.iSucc[b] = Pred[-.b]"
                        using s5_4 s5_5 by auto
                    show ?thesis
                        using s5_6 by auto
                    qed
                also have s4_4: "... = a + -.Pred[Succ[-.b]]"
                    proof -
                    have s5_1: "b \<in> negNat \<setminus> {0}"
                        using s2_2_bdom s3_4_bdom by auto
                    have s5_2: "-.b \<in> Nat \<setminus> {0}"
                        using s5_1 minus_neg_nat_0_in_nat_0 by auto
                    have s5_3: "Succ[Pred[-.b]] = Pred[Succ[-.b]]"
                        using s5_2 Succ_Pred_nat Pred_Succ_nat by auto
                    show ?thesis
                        using s5_3 by auto
                    qed
                also have s4_5: "... = a + -.Pred[-.-.Succ[-.b]]"
                    proof -
                    have s5_1: "-.b \<in> Nat"
                        using s2_2_bdom minus_neg_nat_in_nat by auto
                    have s5_2: "Succ[-.b] \<in> Nat"
                        using s5_1 succIsNat by auto
                    have s5_3: "Succ[-.b] \<in> Int"
                        using s5_2 nat_in_int by auto
                    have s5_4: "-.-.Succ[-.b] = Succ[-.b]"
                        using s5_3 minus_involutive by auto
                    show ?thesis
                        using s5_4 by auto
                    qed
                also have s4_6: "... = a + iSucc[-.Succ[-.b]]"
                    proof -
                    have s5_1: "-.b \<in> Nat"
                        using s2_2_bdom minus_neg_nat_in_nat by auto
                    have s5_2: "Succ[-.b] \<in> Nat \<setminus> {0}"
                        using s5_1 succIsNat succNotZero by auto
                    have s5_3: "-.Succ[-.b] \<in> negNat \<setminus> {0}"
                        using s5_2 minus_nat_0_in_negnat_0 by auto
                    have s5_4: "-.Succ[-.b] \<in> Int"
                        using s5_3 neg_nat_in_int by auto
                    have s5_5: "-.Succ[-.b] \<notin> Nat"
                        using s5_3 neg_nat_0_not_in_nat by auto
                    show ?thesis
                        unfolding iSucc_def
                        using s5_4 s5_5 by auto
                    qed
                finally show "iSucc[a + -.Succ[-.b]] =
                    a + iSucc[-.Succ[-.b]]"
                    using s3_1 s3_2 by auto
                qed
            show "iSucc[a + -.Succ[-.b]] = a + iSucc[-.Succ[-.b]]"
                using s3_3 s3_4 by blast
            qed
        show ?thesis
            using s2_1 s2_2 neg_nat_induction by auto
        qed
    have s1_3: "\<forall> b \<in> Int:  iSucc[a + b] = a + iSucc[b]"
        using s1_1 s1_2 int_union_nat_negnat by auto
    }
    from this show ?thesis
        by auto
    qed


theorem iSuccRightDistributesAdd_sequent:
    assumes adom: "a \\in Int" and bdom: "b \\in Int"
    shows "iSucc[a + b] = a + iSucc[b]"
    using adom bdom iSuccRightDistributesAdd by auto


(*
THEOREM iPredRightDistributesAdd ==
    ASSUME NEW a \in Int
    PROVE \A b \in Int:  iPred[a + b] = a + iPred[b]
PROOF
<1>1. iPred[a + 0] = a + iPred[0]
    <2>1. iPred[a + 0] = iPred[a + -.0]
        BY neg0
    <2>2. @ = a + -.Succ[0]
        <3>1. a \in Int
            OBVIOUS
        <3>2. 0 \in Nat
            BY zeroIsNat
        <3> QED
            BY <3>1, <3>2, addint_succ_negnat
    <2>3. @ = a + -.1
        OBVIOUS  \* 1 is an abbreviation
    <2>4. @ = a + iPred[0]
        BY ipred_0
    <2> QED
        BY <2>1, <2>2, <2>3, <2>4
<1>2. \A b \in Nat:  iPred[a + b] = a + iPred[b]
    <2>1. ASSUME NEW b \in Nat,
            iPred[a + b] = a + iPred[b]
          PROVE iPred[a + Succ[b]] = a + iPred[Succ[b]]
        <3>1. iPred[a + Succ[b]] = iPred[iSucc[a + b]]
            <4>1. a \in Int
                OBVIOUS
            <4>2. b \in Nat
                BY <2>1
            <4>3. a + Succ[b] = iSucc[a + b]
                BY <4>1, <4>2, addint_succ_nat
            <4> QED
                BY <4>3
        <3>2. @ = iSucc[iPred[a + b]]
            <4>1. a + b \in Int
                <5>1. a \in Int
                    OBVIOUS
                <5>2. b \in Int
                    BY <2>2, nat_in_int
                <5> QED
                    BY <5>1, <5>2, addIsInt
            <4> QED
                BY <4>1, iSucciPredCommute
        <3>3. @ = iSucc[a + iPred[b]]
            BY <2>1
        <3>4. @ = a + iSucc[iPred[b]]
            <4>1. b \in Int
                BY <2>1, nat_in_int
            <4>2. iPred[b] \in Int
                BY <4>1, iPred_type
            <4>3. a \in Int
                OBVIOUS
            <4> QED
                BY <4>2, <4>3, iSuccRightDistributesAdd
        <3>5. @ = a + iPred[iSucc[b]]
            <4>1. b \in Int
                BY <2>1, nat_in_int
            <4> QED
                BY <4>1, iSucciPredCommute
        <3>6. @ = a + iPred[Succ[b]]
            <4>1. b \in Nat
                BY <2>1
            <4>2. b \in Int
                BY <2>1, nat_in_int
            <4>3. iSucc[b] = Succ[b]
                BY <4>1, <4>2, nat_in_int DEF iSucc
            <4> QED
                BY <4>3
        <3> QED
            BY <3>1, <3>2, <3>3, <3>4, <3>5, <3>6
    <2> QED
        BY <2>1, <1>1, NatInduction
<1>3. \A b \in negNat \ {0}:  iPred[a + b] = a + iPred[b]
    <2>1. ASSUME NEW b \in negNat \ {0}
          PROVE iPred[a + b] = a + iPred[b]
        <3>1. iPred[a + b] = iPred[a + -.-.b]
            <4>1. b \in Int
                BY <2>1, neg_nat_in_int
            <4>2. -.-.b = b
                BY <4>1, minus_involutive
            <4> QED
                BY <4>2
        <3>2. @ = a + -.Succ[-.b]
            <4>1. a \in Int
                OBVIOUS
            <4>2. -.b \in Nat
                BY <2>1, minus_neg_nat_in_nat
            <4> QED
                BY <4>1, <4>2, addint_succ_negnat
        <3>3. @ = a + iPred[b]
            <4>1. b \in Int
                BY <2>1, neg_nat_in_int
            <4>2. b \notin Nat \ {0}
                BY <2>1, neg_nat_not_in_nat_setminus_0
            <4> QED
                BY <4>1, <4>2 DEF iPred
        <3> QED
            BY <3>1, <3>2, <3>3
    <2> QED
        BY <2>1
<1> QED
    BY <1>2, <1>3
*)
theorem iPredRightDistributesAdd:
    "\<forall> a \<in> Int:  \<forall> b \<in> Int:
        iPred[a + b] = a + iPred[b]"
    proof -
    {
    fix "a" :: "c"
    assume adom: "a \<in> Int"
    have s1_1: "iPred[a + 0] = a + iPred[0]"
        proof -
        have s2_1: "iPred[a + 0] = iPred[a + -.0]"
            using neg0 by auto
        also have s2_2: "... = a + -.Succ[0]"
            proof -
            have s3_1: "a \<in> Int"
                using adom by auto
            have s3_2: "0 \<in> Nat"
                using zeroIsNat by auto
            show ?thesis
                using s3_1 s3_2 addint_succ_negnat by auto
            qed
        also have s2_3: "... = a + -.1"
            by auto
        have s2_4: "... = a + iPred[0]"
            using ipred_0 by auto
            (* `also` raises an error here *)
        finally show ?thesis
            using s2_4 by auto
        qed
    have s1_2: "\<forall> b \<in> Nat:
        iPred[a + b] = a + iPred[b]"
        proof -
        have s2_1: "\<And> b.  \<lbrakk>
            b \<in> Nat;
            iPred[a + b] = a + iPred[b]
            \<rbrakk> \<Longrightarrow>
                iPred[a + Succ[b]] = a + iPred[Succ[b]]"
            proof -
            fix "b" :: "c"
            assume s2_1_bdom: "b \<in> Nat"
            assume s2_1_induct: "iPred[a + b] = a + iPred[b]"
            have s3_1: "iPred[a + Succ[b]] = iPred[iSucc[a + b]]"
                proof -
                have s4_1: "a \<in> Int"
                    using adom by auto
                have s4_2: "b \<in> Nat"
                    using s2_1_bdom by auto
                have s4_3: "a + Succ[b] = iSucc[a + b]"
                    using s4_1 s4_2 addint_succ_nat by auto
                show ?thesis
                    using s4_3 by auto
                qed
            also have s3_2: "... = iSucc[iPred[a + b]]"
                proof -
                have s4_1: "a + b \<in> Int"
                    proof -
                    have s5_1: "a \<in> Int"
                        using adom by auto
                    have s5_2: "b \<in> Int"
                        using s2_1_bdom nat_in_int by auto
                    show ?thesis
                        using s5_1 s5_2 addIsInt by auto
                    qed
                show ?thesis
                    using s4_1 iSucciPredCommute by auto
                qed
            also have s3_3: "... = iSucc[a + iPred[b]]"
                using s2_1_induct by auto
            also have s3_4: "... = a + iSucc[iPred[b]]"
                proof -
                have s4_1: "b \<in> Int"
                    using s2_1_bdom nat_in_int by auto
                have s4_2: "iPred[b] \<in> Int"
                    using s4_1 iPred_type by auto
                have s4_3: "a \<in> Int"
                    using adom by auto
                show ?thesis
                    using s4_2 s4_3 iSuccRightDistributesAdd
                    by auto
                qed
            also have s3_5: "... = a + iPred[iSucc[b]]"
                proof -
                have s4_1: "b \<in> Int"
                    using s2_1_bdom nat_in_int by auto
                show ?thesis
                    using s4_1 iSucciPredCommute by auto
                qed
            also have s3_6: "... = a + iPred[Succ[b]]"
                proof -
                have s4_1: "b \<in> Nat"
                    using s2_1_bdom by auto
                have s4_2: "b \<in> Int"
                    using s2_1_bdom nat_in_int by auto
                have s4_3: "iSucc[b] = Succ[b]"
                    unfolding iSucc_def
                    using s4_1 s4_2 by auto
                show ?thesis
                    using s4_3 by auto
                qed
            finally show "iPred[a + Succ[b]] = a + iPred[Succ[b]]" .
            qed
        show ?thesis
            using s1_1 s2_1 natInduct by auto
        qed
    have s1_3: "\<forall> b \<in> negNat \<setminus> {0}:
        iPred[a + b] = a + iPred[b]"
        proof -
        {
        fix "b" :: "c"
        assume s2_1_bdom: "b \<in> negNat \<setminus> {0}"
        {
            have s3_1: "iPred[a + b] = iPred[a + -.-.b]"
                proof -
                have s4_1: "b \<in> Int"
                    using s2_1_bdom neg_nat_in_int by auto
                have s4_2: "-.-.b = b"
                    using s4_1 minus_involutive by auto
                show ?thesis
                    using s4_2 by auto
                qed
            also have s3_2: "... = a + -.Succ[-.b]"
                proof -
                have s4_1: "a \<in> Int"
                    using adom by auto
                have s4_2: "-.b \<in> Nat"
                    using s2_1_bdom minus_neg_nat_in_nat by auto
                show ?thesis
                    using s4_1 s4_2 addint_succ_negnat by auto
                qed
            also have s3_3: "... = a + iPred[b]"
                proof -
                have s4_1: "b \<in> Int"
                    using s2_1_bdom neg_nat_in_int by auto
                have s4_2: "b \<notin> Nat \<setminus> {0}"
                    proof -
                    have s5_1: "b \<in> negNat"
                        using s2_1_bdom by auto
                    show ?thesis
                        using s5_1 neg_nat_not_in_nat_setminus_0
                        by auto
                    qed
                show ?thesis
                    unfolding iPred_def
                    using s4_1 s4_2 by auto
                qed
            finally have "iPred[a + b] = a + iPred[b]" .
        }
        from this have s2_2: "iPred[a + b] = a + iPred[b]"
            by auto
        }
        from this show ?thesis
            by auto
        qed
    have s1_4: "\<forall> b \<in> Int:
                    iPred[a + b] = a + iPred[b]"
        using s1_2 s1_3 int_union_nat_negnat_0 spec allI by auto
    }
    from this show ?thesis
        by auto
    qed


theorem iPredRightDistributesAdd_sequent:
    assumes mdom: "m \\in Int" and ndom: "n \\in Int"
    shows "iPred[m + n] = m + iPred[n]"
    using mdom ndom iPredRightDistributesAdd by auto


theorem isucc_eq_add_1:
    assumes idom: "i \\in Int"
    shows "iSucc[i] = i + 1"
    proof -
    have s1_1: "iSucc[i] = iSucc[i + 0]"
        using idom add_0 by auto
    also have s1_2: "... = i + iSucc[0]"
        proof -
        have s2_1: "0 \\in Int"
            using zeroIsNat nat_in_int by auto
        show ?thesis
            using idom s2_1 iSuccRightDistributesAdd_sequent
            by auto
        qed
    also have s1_3: "... = i + 1"
        proof -
        have s2_1: "iSucc[0] = Succ[0]"
            proof -
            have s3_1: "0 \\in Int"
                using zeroIsNat nat_in_int by auto
            have s3_2: "0 \\in Nat"
                using zeroIsNat by auto
            show ?thesis
                unfolding iSucc_def
                using s3_1 s3_2 by auto
            qed
        have s2_2: "Succ[0] = 1"
            by auto
        have s2_3: "iSucc[0] = 1"
            using s2_1 s2_2 by auto
        show ?thesis
            using s2_3 s1_2 by auto
        qed
    finally show ?thesis .
    qed


(*
THEOREM AddAssociative ==
    \A a \in Int:  \A b \in Int:  \A c \in Int:
        (a + b) + c = a + (b + c)
PROOF
<1>1. SUFFICES
        ASSUME NEW a \in Int, NEW b \in Int
        PROVE \A c \in Int:
            (a + b) + c = a + (b + c)
    BY <1>1
<1>2. (a + b) + 0 = a + (b + 0)
    <2>1. (a + b) + 0 = a + b
        <3>1. a + b \in Int
            BY <1>1, addIsInt
        <3> QED
            BY <3>1, add_0
    <2>2. @ = a + (b + 0)
        <3>1. b \in Int
            BY <1>1
        <3>2. b + 0 = b
            BY <3>1, add_0
        <3> QED
            BY <3>2
    <2> QED
        BY <2>1, <2>2
<1>3. ASSUME NEW c \in Nat,
        (a + b) + c = a + (b + c)
      PROVE (a + b) + Succ[c] = a + (b + Succ[c])
    <2>1. (a + b) + Succ[c] = iSucc[(a + b) + c]
        <3>1. a + b \in Int
            BY <1>1, addIsInt
        <3>2. c \in Nat
            BY <1>3
        <3> QED
            BY <3>1, <3>2, addint_succ_nat
    <2>2. @ = iSucc[a + (b + c)]
        BY <1>3  \* induction hypothesis
    <2>3. @ = a + iSucc[b + c]
        <3>1. a \in Int
            BY <1>1
        <3>2. b + c \in Int
            BY <1>1, <1>3, nat_in_int, addIsInt
        <3> QED
            BY <3>1, <3>2, iSuccRightDistributesAdd
    <2>4. @ = a + (b + iSucc[c])
        <3>1. b \in Int
            BY <1>1
        <3>2. c \in Int
            BY <1>3, nat_in_int
        <3> QED
            BY <3>1, <3>2, iSuccRightDistributesAdd
    <2>5. @ = a + (b + Succ[c])
        <3>1. c \in Nat
            BY <1>3
        <3>2. c \in Int
            BY <3>1, nat_in_int
        <3>3. iSucc[c] = Succ[c]
            BY <3>1, <3>2 DEF iSucc
        <3> QED
            BY <3>3
    <2> QED
        BY <2>1, <2>2, <2>3, <2>4, <2>5
<1>4. ASSUME NEW c \in negNat,
        (a + b) + c = a + (b + c)
      PROVE (a + b) + -.Succ[-.c] = a + (b + -.Succ[-.c])
    <2>1. (a + b) + -.Succ[-.c] = (a + b) + iPred[c]
        <3>1. c \in Int
            BY <1>4, neg_nat_in_int
        <3>2. c \notin Nat \ {0}
            BY <1>4, neg_nat_not_in_nat_setminus_0
        <3>3. iPred[c] = -.Succ[-.c]
            BY <3>1, <3>2 DEF iPred
        <3> QED
            BY <3>3
    <2>2. @ = iPred[(a + b) + c]
        <3>1. a + b \in Int
            BY <1>1, addIsInt
        <3>2. c \in Int
            BY <1>4, neg_nat_in_int
        <3>3 QED
            BY <3>1, <3>2, iPredRightDistributesAdd
    <2>3. @ = iPred[a + (b + c)]
        BY <1>4  \* induction hypothesis
    <2>4. @ = a + iPred[b + c]
        <3>1. a \in Int
            BY <1>1
        <3>2. b + c \in Int
            BY <1>1, <1>4, neg_nat_in_int, addIsInt
        <3> QED
            BY <3>1, <3>2, iPredRightDistributesAdd
    <2>5. @ = a + (b + iPred[c])
        <3>1. b \in Int
            BY <1>1
        <3>2. c \in Int
            BY <1>4, neg_nat_in_int
        <3> QED
            BY <3>1, <3>2, iPredRightDistributesAdd
    <2>6. @ = a + (b + -.Succ[-.c])
        <3>1. c \in Int
            BY <1>4, neg_nat_in_int
        <3>2. c \notin Nat \ {0}
            BY <1>4, neg_nat_not_in_nat_setminus_0
        <3>3. iPred[c] = -.Succ[-.c]
            BY <3>1, <3>2 DEF iPred
        <3> QED
            BY <3>3
    <2> QED
        BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6
<1>5. \A c \in Nat:  (a + b) + c = a + (b + c)
    BY <1>2, <1>3, NatInduction
<1>6. \A c \in negNat:  (a + b) + c = a + (b + c)
    BY <1>2, <1>4, neg_nat_induction
<1> QED
    BY <1>5, <1>6
*)
theorem AddAssociative:
    "\<forall> a \<in> Int:
    \<forall> b \<in> Int:
    \<forall> c \<in> Int:
        (a + b) + c = a + (b + c)"
    proof -
    {
    fix "a" :: "c"
    fix "b" :: "c"
    assume adom: "a \<in> Int"
    assume bdom: "b \<in> Int"
    have s1_2: "(a + b) + 0 = a + (b + 0)"
        proof -
        have s2_1: "(a + b) + 0 = a + b"
            proof -
            have s3_1: "a + b \<in> Int"
                using adom bdom addIsInt by auto
            show ?thesis
                using s3_1 add_0 by auto
            qed
        have s2_2: "... = a + (b + 0)"
            proof -
            have s3_1: "b \<in> Int"
                using bdom by auto
            have s3_2: "b + 0 = b"
                using s3_1 add_0 by auto
            show ?thesis
                using s3_2 by auto
            qed
        show ?thesis
            using s2_1 s2_2 by auto
        qed
    have s1_3: "\<And> c.  \<lbrakk>
            c \<in> Nat;
            (a + b) + c = a + (b + c)
        \<rbrakk> \<Longrightarrow>
            (a + b) + Succ[c] = a + (b + Succ[c])"
        proof -
        fix "c" :: "c"
        assume s1_3_cdom: "c \<in> Nat"
        assume s1_3_induct: "(a + b) + c = a + (b + c)"
        have s2_1: "(a + b) + Succ[c] = iSucc[(a + b) + c]"
            proof -
            have s3_1: "a + b \<in> Int"
                using adom bdom addIsInt by auto
            have s3_2: "c \<in> Nat"
                using s1_3_cdom by auto
            show ?thesis
                using s3_1 s3_2 addint_succ_nat by auto
            qed
        also have s2_2: "... = iSucc[a + (b + c)]"
            using s1_3_induct by auto
        also have s2_3: "... = a + iSucc[b + c]"
            proof -
            have s3_1: "a \<in> Int"
                using adom by auto
            have s3_2: "b + c \<in> Int"
                using bdom s1_3_cdom nat_in_int addIsInt by auto
            show ?thesis
                using s3_1 s3_2 iSuccRightDistributesAdd by auto
            qed
        also have s2_4: "... = a + (b + iSucc[c])"
            proof -
            have s3_1: "b \<in> Int"
                using bdom by auto
            have s3_2: "c \<in> Int"
                using s1_3_cdom nat_in_int by auto
            have s3_3: "iSucc[b + c] = b + iSucc[c]"
                using s3_1 s3_2 iSuccRightDistributesAdd by auto
            show ?thesis
                using s3_3 by auto
            qed
        also have s2_5: "... = a + (b + Succ[c])"
            proof -
            have s3_1: "c \<in> Nat"
                using s1_3_cdom by auto
            have s3_2: "c \<in> Int"
                using s1_3_cdom nat_in_int by auto
            have s3_3: "iSucc[c] = Succ[c]"
                unfolding iSucc_def
                using s3_1 s3_2 by auto
            show ?thesis
                using s3_3 by auto
            qed
        finally show "(a + b) + Succ[c] = a + (b + Succ[c])" .
        qed
    have s1_4: "\<And> c.  \<lbrakk>
            c \<in> negNat;
            (a + b) + c = a + (b + c)
        \<rbrakk> \<Longrightarrow>
            (a + b) + -.Succ[-.c] = a + (b + -.Succ[-.c])"
        proof -
        fix "c" :: "c"
        assume s1_4_cdom: "c \<in> negNat"
        assume s1_4_induct: "(a + b) + c = a + (b + c)"
        have s2_1: "(a + b) + -.Succ[-.c] = (a + b) + iPred[c]"
            proof -
            have s3_1: "c \<in> Int"
                using s1_4_cdom neg_nat_in_int by auto
            have s3_2: "c \<notin> Nat \<setminus> {0}"
                using s1_4_cdom neg_nat_not_in_nat_setminus_0 by auto
            have s3_3: "iPred[c] = -.Succ[-.c]"
                unfolding iPred_def
                using s3_1 s3_2 by auto
            show ?thesis
                using s3_3 by auto
            qed
        also have s2_2: "... = iPred[(a + b) + c]"
            proof -
            have s3_1: "a + b \<in> Int"
                using adom bdom addIsInt by auto
            have s3_2: "c \<in> Int"
                using s1_4_cdom neg_nat_in_int by auto
            show ?thesis
                using s3_1 s3_2 iPredRightDistributesAdd by force
            qed
        also have s2_3: "... = iPred[a + (b + c)]"
            using s1_4_induct by auto
        also have s2_4: "... = a + iPred[b + c]"
            proof -
            have s3_1: "a \<in> Int"
                using adom by auto
            have s3_2: "b + c \<in> Int"
                using bdom s1_4_cdom neg_nat_in_int addIsInt by auto
            show ?thesis
                using s3_1 s3_2 iPredRightDistributesAdd by auto
            qed
        also have s2_5: "... = a + (b + iPred[c])"
            proof -
            have s3_1: "b \<in> Int"
                using bdom by auto
            have s3_2: "c \<in> Int"
                using s1_4_cdom neg_nat_in_int by auto
            have s3_3: "iPred[b + c] = b + iPred[c]"
                using s3_1 s3_2 iPredRightDistributesAdd by force
            show ?thesis
                using s3_3 by auto
            qed
        also have s2_6: "... = a + (b + -.Succ[-.c])"
            proof -
            have s3_1: "c \<in> Int"
                using s1_4_cdom neg_nat_in_int by auto
            have s3_2: "c \<notin> Nat \<setminus> {0}"
                using s1_4_cdom neg_nat_not_in_nat_setminus_0 by auto
            have s3_3: "iPred[c] = -.Succ[-.c]"
                unfolding iPred_def
                using s3_1 s3_2 by auto
            show ?thesis
                using s3_3 by auto
            qed
        finally show "(a + b) + -.Succ[-.c] = a + (b + -.Succ[-.c])" .
        qed
    have s1_5: "\<forall> c \<in> Nat:
                    (a + b) + c = a + (b + c)"
        using s1_2 s1_3 natInduct by auto
    have s1_6: "\<forall> c \<in> negNat:
                    (a + b) + c = a + (b + c)"
        using s1_2 s1_4 neg_nat_induction by auto
    have "\<forall> c \<in> Int:
            (a + b) + c = a + (b + c)"
        using s1_5 s1_6 int_union_nat_negnat by auto
    }
    from this show ?thesis
        by auto
    qed


theorem AddAssociative_sequent:
    assumes adom: "a \\in Int" and bdom: "b \\in Int"
        and cdom: "c \\in Int"
    shows "(a + b) + c = a + (b + c)"
    using adom bdom cdom AddAssociative by auto


theorem AddLeftCommutativity:
    assumes adom: "a \\in Int" and bdom: "b \\in Int"
        and cdom: "c \\in Int"
    shows "b + (a + c) = a + (b + c)"
    proof -
    have s1_1: "(b + a) + c = (a + b) + c"
        using adom bdom by (simp only: AddCommutative_sequent)
    show ?thesis
        using adom bdom cdom s1_1 by (simp only: AddAssociative_sequent)
    qed


theorems add_ac_int[algebra_simps] =
    AddCommutative_sequent AddAssociative_sequent
    AddLeftCommutativity add_0 add_0_left


(* A test that the simplification rules work. *)
theorem
    assumes "a \\in Int" and "b \\in Int" and "c \\in Int"
    shows "a + (b + c) = (a + b) + c"
    using assms by (simp add: algebra_simps)


(*
THEOREM MinusSuccIsMinusOne ==
    ASSUME NEW n \in Nat
    PROVE -.Succ[n] = -.n + -.1
<1>1. -.Succ[n] = -.Succ[-.-.n]
    <2>1. -.-.n = n
        <3>1. n \in Nat
            OBVIOUS
        <3>2. n \in Int
            BY <3>1, nat_in_int
        <3> QED
            BY <3>2, minus_involutive
    <2> QED
        BY <2>1
<1>2. @ = iPred[-.n]
    <2>1. -.n \in Int
        <3>1. n \in Nat
            OBVIOUS
        <3> QED
            BY <3>1, minus_nat_in_int
    <2>2. -.n \notin Nat \ {0}
        <3>1. n \in Nat
            OBVIOUS
        <3>2. -.n \in negNat
            BY <3>1, minus_nat_in_neg_nat
        <3> QED
            BY <3>2, neg_nat_not_in_nat_setminus_0
    <2> QED
        BY <2>1, <2>2 DEF iPred
<1>3. @ = iPred[-.n + 0]
    <2>1. -.n \in Int
        <3>1. n \in Nat
            OBVIOUS
        <3> QED
            BY <3>1, minus_nat_in_int
    <2>2. -.n + 0 = -.n
        BY <2>1, add_0
    <2> QED
        BY <2>2
<1>4. @ = -.n + iPred[0]
    <2>1. -.n \in Int
        <3>1. n \in Nat
            OBVIOUS
        <3> QED
            BY <3>1, minus_nat_in_int
    <2>2. 0 \in Int
        BY zero_in_int
    <2> QED
        BY <2>1, <2>2, iPredRightDistributesAdd
<1>5. @ = -.n + -.Succ[-.0]
    <2>1. 0 \in Int
        BY zero_in_int
    <2>2. 0 \notin Nat \ {0}
        OBVIOUS
    <2> QED
        BY <2>1, <2>2 DEF iPred
<1>6. @ = -.n + -.Succ[0]
    BY neg0
<1>7. @ = -.n + -.1
    OBVIOUS  \* 1 is an abbreviation
<1> QED
    BY <1>1, <1>2, <1>3, <1>4,
        <1>5, <1>6, <1>7
*)
theorem MinusSuccIsMinusOne:
    assumes ndom: "n \<in> Nat"
    shows "-.Succ[n] = -.n + -.1"
    proof -
    have s1_1: "-.Succ[n] = -.Succ[-.-.n]"
        proof -
        have s2_1: "-.-.n = n"
            proof -
            have s3_1: "n \<in> Int"
                using ndom nat_in_int by auto
            show ?thesis
                using s3_1 minus_involutive by auto
            qed
        show ?thesis
            using s2_1 by auto
        qed
    also have s1_2: "... = iPred[-.n]"
        proof -
        have s2_1: "-.n \<in> Int"
            using ndom minus_nat_in_int by auto
        have s2_2: "-.n \<notin> Nat \<setminus> {0}"
            proof -
            have s3_1: "-.n \<in> negNat"
                using ndom minus_nat_in_neg_nat by auto
            show ?thesis
                using s3_1 neg_nat_not_in_nat_setminus_0 by fast
            qed
        show ?thesis
            unfolding iPred_def
            using s2_1 s2_2 by auto
        qed
    also have s1_3: "... = iPred[-.n + 0]"
        proof -
        have s2_1: "-.n \<in> Int"
            proof -
            have s3_1: "n \<in> Nat"
                using ndom by auto
            show ?thesis
                using s3_1 minus_nat_in_int by auto
            qed
        have s2_2: "-.n + 0 = -.n"
            using s2_1 add_0 by auto
        show ?thesis
            using s2_2 by auto
        qed
    also have s1_4: "... = -.n + iPred[0]"
        proof -
        have s2_1: "-.n \<in> Int"
            proof -
            have s3_1: "n \<in> Nat"
                using ndom by auto
            show ?thesis
                using s3_1 minus_nat_in_int by auto
            qed
        have s2_2: "0 \<in> Int"
            using zero_in_int by auto
        show ?thesis
            using s2_1 s2_2 iPredRightDistributesAdd by fast
        qed
    also have s1_5: "... = -.n + -.Succ[-.0]"
        proof -
        have s2_1: "0 \<in> Int"
            using zero_in_int by auto
        have s2_2: "0 \<notin> Nat \<setminus> {0}"
            by auto
        show ?thesis
            unfolding iPred_def
            using s2_1 s2_2 by auto
        qed
    also have s1_6: "... = -.n + -.Succ[0]"
        using neg0 by auto
    also have s1_7: "... = -.n + -.1"
        by auto
    from calculation show ?thesis
        by auto
    qed


theorem SuccMinusIsPlusOne:
    assumes idom: "i \\in negNat"
    shows "Succ[-.i] = -.i + 1"
    proof -
    have s1_1: "-.i \\in Nat"
        using idom minus_neg_nat_in_nat by auto
    have s1_2: "-.i \\in Int"
        using s1_1 nat_in_int by auto
    have s1_3: "Succ[-.i] = iSucc[-.i]"
        unfolding iSucc_def
        using s1_1 s1_2 by auto
    also have s1_4: "... = iSucc[-.i + 0]"
        using s1_2 add_0 by auto
    also have s1_5: "... = -.i + Succ[0]"
        using s1_2 zeroIsNat addint_succ_nat by auto
    also have s1_6: "... = -.i + 1"
        by auto  (* 1 is an abbreviation *)
    from calculation show ?thesis .
    qed


(*----------------------------------------------------------------------------*)
(* Properties of addition and difference. *)


(*
THEOREM AddNegCancels ==
    \A i \in Int:  i + -.i = 0
PROOF
<1>1. 0 + -.0 = 0
    <2>1. 0 + -.0 = 0 + 0
        BY neg0
    <2>2. @ = 0
        BY zero_in_int, add_0
    <2> QED
        BY <2>1, <2>2
<1>2. ASSUME NEW i \in Nat, i + -.i = 0
      PROVE Succ[i] + -.Succ[i] = 0
    <2>1. Succ[i] + -.Succ[i] = -.Succ[i] + Succ[i]
        <3>1. Succ[i] \in Int
            BY <1>2, succIsNat, nat_in_int
        <3>2. -.Succ[i] \in Int
            BY <3>1, neg_int_eq_int
        <3> QED
            BY <3>1, <3>2, AddCommutative
    <2>2. @ = iSucc[-.Succ[i] + i]
        <3>1. -.Succ[i] \in Int
            BY <1>2, succIsNat, minus_nat_in_int
        <3>2. i \in Nat
            BY <1>2
        <3> QED
            BY <3>1, <3>2, addint_succ_nat
    <2>3. @ = iSucc[i + -.Succ[i]]
        <3>1. i \in Int
            BY <1>2, nat_in_int
        <3>2. -.Succ[i] \in Int
            BY <1>2, succIsNat, minus_nat_in_int
        <3>3. -.Succ[i] + i = i + -.Succ[i]
            BY <3>1, <3>2, AddCommutative
        <3> QED
            BY <3>3
    <2>4. @ = iSucc[iPred[i + -.i]]
        <3>1. i \in Int
            BY <1>2, nat_in_int
        <3>2. i \in Nat
            BY <1>2
        <3> QED
            BY <3>1, <3>2, addint_succ_negnat
    <2>5. @ = iSucc[iPred[0]]
        BY <1>2
    <2>6. @ = iSucc[-.1]
        BY ipred_0
    <2>7. @ = 0
        BY isucc_minus_1
    <2> QED
        BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7
<1>3. ASSUME NEW i \in negNat, i + -.i = 0
      PROVE -.Succ[-.i] + -.(-.Succ[-.i]) = 0
    <2>1. -.Succ[-.i] + -.(-.Succ[-.i])
            = -.Succ[-.i] + Succ[-.i]
        <3>1. Succ[-.i] \in Int
            BY <1>3, minus_neg_nat_in_nat,
                succIsNat, nat_in_int
        <3> QED
            BY <3>1, minus_involutive
    <2>2. @ = iSucc[-.Succ[-.i] + -.i]
        <3>1. -.Succ[-.i] \in Int
            BY <1>3, minus_neg_nat_in_nat,
                succIsNat, minus_nat_in_int
        <3>2. -.i \in Nat
            BY <1>3, minus_neg_nat_in_nat
        <3> QED
            BY <3>1, <3>2, addint_succ_nat
    <2>3. @ = iSucc[-.i + -.Succ[-.i]]
        <3>1. -.Succ[-.i] \in Int
            BY <1>3, minus_neg_nat_in_nat,
                succIsNat, minus_nat_in_int
        <3>2. -.i \in Int
            BY <1>3, minus_negnat_in_int
        <3>3. -.Succ[-.i] + -.i = -.i + -.Succ[-.i]
            BY <3>1, <3>2, AddCommutative
        <3> QED
            BY <3>3
    <2>4. @ = iSucc[iPred[-.i + -.-.i]]
        <3>1. -.i \in Int
            BY <1>3, minus_negnat_in_int
        <3>2. -.i \in Nat
            BY <1>3, minus_neg_nat_in_nat
        <3>3. -.i + -.Succ[-.i] = iPred[-.i + -.-.i]
            BY <3>1, <3>2, addint_succ_negnat
        <3> QED
            BY <3>3
    <2>5. @ = iSucc[iPred[-.i + i]]
        <3>1. -.-.i = i
            BY <1>3, neg_nat_in_int, minus_involutive
        <3> QED
            BY <3>1
    <2>6. @ = iSucc[iPred[i + -.i]]
        <3>1. -.i \in Int
            BY <1>3, minus_negnat_in_int
        <3>2. i \in Int
            BY <1>3, neg_nat_in_int
        <3>3. -.i + i = i + -.i
            BY <3>1, <3>2, AddCommutative
        <3> QED
            BY <3>3
    <2>7. @ = iSucc[iPred[0]]
        BY <1>3  \* induction hypothesis
    <2>8. @ = iSucc[-.1]
        BY ipred_0
    <2>9. @ = 0
        BY isucc_minus_1
    <2> QED
        BY <2>1, <2>2, <2>3, <2>4, <2>5,
            <2>6, <2>7, <2>8, <2>9
<1>4. \A i \in Nat:  i + -.i = 0
    BY <1>1, <1>2, NatInduction
<1>5. \A i \in negNat:  i + -.i = 0
    BY <1>1, <1>3, neg_nat_induction
<1> QED
    BY <1>4, <1>5, int_union_nat_negnat
*)
theorem AddNegCancels:
    "\<forall> i \<in> Int:  i + -.i = 0"
    proof -
    have s1_1: "0 + -.0 = 0"
        proof -
        have s2_1: "0 + -.0 = 0 + 0"
            using neg0 by auto
        also have s2_2: "... = 0"
            using zero_in_int add_0 by auto
        finally show ?thesis .
        qed
    have s1_2: "\<And> i.  \<lbrakk>
            i \\in Nat;
            i + -.i = 0
        \<rbrakk> \<Longrightarrow>
            Succ[i] + -.Succ[i] = 0"
        proof -
        fix "i" :: "c"
        assume s1_2_idom: "i \\in Nat"
        assume s1_2_induct: "i + -.i = 0"
        have s2_1: "Succ[i] + -.Succ[i] = -.Succ[i] + Succ[i]"
            proof -
            have s3_1: "Succ[i] \\in Int"
                using s1_2_idom succIsNat nat_in_int by auto
            have s3_2: "-.Succ[i] \\in Int"
                using s3_1 neg_int_eq_int by auto
            show ?thesis
                using s3_1 s3_2 AddCommutative by fast
            qed
        also have s2_2: "... = iSucc[-.Succ[i] + i]"
            proof -
            have s3_1: "-.Succ[i] \\in Int"
                using s1_2_idom succIsNat minus_nat_in_int by auto
            have s3_2: "i \\in Nat"
                using s1_2_idom by auto
            show ?thesis
                using s3_1 s3_2 by (rule addint_succ_nat)
            qed
        also have s2_3: "... = iSucc[i + -.Succ[i]]"
            proof -
            have s3_1: "i \\in Int"
                using s1_2_idom nat_in_int by auto
            have s3_2: "-.Succ[i] \\in Int"
                using s1_2_idom succIsNat minus_nat_in_int
                by auto
            have s3_3: "-.Succ[i] + i = i + -.Succ[i]"
                using s3_1 s3_2 AddCommutative by auto
            show ?thesis
                using s3_3 by auto
            qed
        also have s2_4: "... = iSucc[iPred[i + -.i]]"
            proof -
            have s3_1: "i \\in Int"
                using s1_2_idom nat_in_int by auto
            have s3_2: "i \\in Nat"
                using s1_2_idom by auto
            show ?thesis
                using s3_1 s3_2 addint_succ_negnat by auto
            qed
        also have s2_5: "... = iSucc[iPred[0]]"
            using s1_2_induct by auto
        also have s2_6: "... = iSucc[-.1]"
            using ipred_0 by auto
        also have s2_7: "... = 0"
            using isucc_minus_1 by auto
        finally show "Succ[i] + -.Succ[i] = 0" .
        qed
    have s1_3: "\<And> i.  \<lbrakk>
            i \\in negNat;
            i + -.i = 0
        \<rbrakk> \<Longrightarrow>
            -.Succ[-.i] + -.-.Succ[-.i] = 0"
        proof -
        fix "i" :: "c"
        assume s1_3_idom: "i \\in negNat"
        assume s1_3_induct: "i + -.i = 0"
        have s2_1: "-.Succ[-.i] + -.(-.Succ[-.i])
                = -.Succ[-.i] + Succ[-.i]"
            proof -
            have s3_1: "Succ[-.i] \\in Int"
                using s1_3_idom minus_neg_nat_in_nat
                    succIsNat nat_in_int by auto
            show ?thesis
                using s3_1 minus_involutive by auto
            qed
        also have s2_2: "... = iSucc[-.Succ[-.i] + -.i]"
            proof -
            have s3_1: "-.Succ[-.i] \\in Int"
                using s1_3_idom minus_neg_nat_in_nat
                    succIsNat minus_nat_in_int by auto
            have s3_2: "-.i \\in Nat"
                using s1_3_idom minus_neg_nat_in_nat by auto
            show ?thesis
                using s3_1 s3_2 by (rule addint_succ_nat)
            qed
        also have s2_3: "... = iSucc[-.i + -.Succ[-.i]]"
            proof -
            have s3_1: "-.Succ[-.i] \\in Int"
                using s1_3_idom minus_neg_nat_in_nat
                    succIsNat minus_nat_in_int by auto
            have s3_2: "-.i \\in Int"
                using s1_3_idom minus_negnat_in_int by auto
            have s3_3: "-.Succ[-.i] + -.i = -.i + -.Succ[-.i]"
                using s3_1 s3_2 AddCommutative by auto
            show ?thesis
                using s3_3 by auto
            qed
        also have s2_4: "... = iSucc[iPred[-.i + -.-.i]]"
            proof -
            have s3_1: "-.i \\in Int"
                using s1_3_idom minus_negnat_in_int by auto
            have s3_2: "-.i \\in Nat"
                using s1_3_idom minus_neg_nat_in_nat by auto
            have s3_3: "-.i + -.Succ[-.i] = iPred[-.i + -.-.i]"
                using s3_1 s3_2 addint_succ_negnat by auto
            show ?thesis
                using s3_3 by auto
            qed
        also have s2_5: "... = iSucc[iPred[-.i + i]]"
            proof -
            have s3_1: "-.-.i = i"
                using s1_3_idom neg_nat_in_int minus_involutive
                by auto
            show ?thesis
                using s3_1 by auto
            qed
        also have s2_6: "... = iSucc[iPred[i + -.i]]"
            proof -
            have s3_1: "-.i \\in Int"
                using s1_3_idom minus_negnat_in_int by auto
            have s3_2: "i \\in Int"
                using s1_3_idom neg_nat_in_int by auto
            have s3_3: "-.i + i = i + -.i"
                using s3_1 s3_2 AddCommutative by fast
            show ?thesis
                using s3_3 by auto
            qed
        also have s2_7: "... = iSucc[iPred[0]]"
            using s1_3_induct by auto
        also have s2_8: "... = iSucc[-.1]"
            using ipred_0 by auto
        also have s2_9: "... = 0"
            using isucc_minus_1 by auto
        finally show "-.Succ[-.i] + -.-.Succ[-.i] = 0" .
        qed
    have s1_4: "\<forall> i \<in> Nat:  i + -.i = 0"
        using s1_1 s1_2 natInduct by auto
    have s1_5: "\<forall> i \<in> negNat:  i + -.i = 0"
        using s1_1 s1_3 neg_nat_induction by auto
    show ?thesis
        using s1_4 s1_5 int_union_nat_negnat by auto
    qed


theorem AddNegCancels_sequent:
    assumes idom: "i \\in Int"
    shows "i + -.i = 0"
    using idom AddNegCancels spec by auto


theorem AddNegCancels_left:
    assumes idom: "i \\in Int"
    shows "-.i + i = 0"
    proof -
    have s1_1: "i + -.i = 0"
        using idom AddNegCancels_sequent by auto
    have s1_2: "i + -.i = -.i + i"
        proof -
        have s2_1: "-.i \\in Int"
            using idom neg_int_eq_int by auto
        show ?thesis
            using idom s2_1 AddCommutative_sequent by auto
        qed
    show ?thesis
        using s1_1 s1_2 by auto
    qed


(*
THEOREM a_plus_b_minus_a_eq_b ==
    ASSUME NEW a \in Int, NEW b \in Int
    PROVE a + (b - a) = b
PROOF
<1>1. a + (b - a) = a + (b + -.a)
    BY DEF diff
<1>2. @ = a + (-.a + b)
    <2>1. b \in Int
        OBVIOUS
    <2>2. -.a \in Int
        BY a \in Int, neg_int_eq_int
    <2>3. b + -.a = -.a + b
        BY <2>1, <2>2, AddCommutative
    <2> QED
        BY <2>3
<1>3. @ = (a + -.a) + b
    <2>1. a \in Int
        OBVIOUS
    <2>2. -.a \in Int
        BY a \in Int, neg_int_eq_int
    <2>3. b \in Int
        OBVIOUS
    <2> QED
        BY <2>1, <2>2, <2>3, AddAssociative
<1>4. @ = 0 + b
    <2>1. a \in Int
        OBVIOUS
    <2>2. a + -.a = 0
        BY <2>1, AddNegCancels
    <2> QED
        BY <2>2
<1>5. @ = b
    BY add_0_left
<1> QED
    BY <1>1, <1>2, <1>3, <1>4, <1>5
*)
theorem a_plus_b_minus_a_eq_b:
    assumes adom: "a \\in Int" and bdom: "b \\in Int"
    shows "a + (b - a) = b"
    proof -
    have s1_1: "a + (b - a) = a + (b + -.a)"
        unfolding diff_def by auto
    also have s1_2: "... = a + (-.a + b)"
        proof -
        have s2_1: "b \\in Int"
            using bdom by auto
        have s2_2: "-.a \\in Int"
            using adom neg_int_eq_int by auto
        have s2_3: "b + -.a = -.a + b"
            using s2_1 s2_2 AddCommutative by auto
        show ?thesis
            using s2_3 by auto
        qed
    also have s1_3: "... = (a + -.a) + b"
        proof -
        have s2_1: "a \\in Int"
            using adom by auto
        have s2_2: "-.a \\in Int"
            using adom neg_int_eq_int by auto
        have s2_3: "b \\in Int"
            using bdom by auto
        have s2_4: "a \\in Int ==> -.a \\in Int ==> b \\in Int
            ==> (a + -.a) + b = a + (-.a + b)"
            using AddAssociative_sequent by blast
        have s2_5: "(a + -.a) + b = a + (-.a + b)"
            using s2_1 s2_2 s2_3 s2_4 by auto
        show ?thesis
            by (rule s2_5[symmetric])
        qed
    also have s1_4: "... = 0 + b"
        proof -
        have s2_1: "a \\in Int"
            using adom by auto
        have s2_2: "a + -.a = 0"
            using s2_1 AddNegCancels by auto
        show ?thesis
            using s2_2 by auto
        qed
    also have s1_5: "... = b"
        using bdom add_0_left by auto
    finally show ?thesis .
    qed


(*
THEOREM MinusDistributesAdd ==
    \A a \in Int:  \A b \in Int:
        -.(a + b) = (-.a) + (-.b)
PROOF
<1>1. SUFFICES ASSUME NEW a \in Int
               PROVE \A b \in Int:
                        -.(a + b) = (-.a) + (-.b)
    BY <1>1
<1>2. -.(a + 0) = (-.a) + (-.0)
    <2>1. -.(a + 0) = -.a
        <3>1. a + 0 = a
            BY <1>1, add_0
        <3> QED
            BY <3>1
    <2>2. -.a + -.0 = -.a
        <3>1. -.a + -.0 = -.a + 0
            BY neg0
        <3>2. @ = -.a
            <4>1. -.a \in Int
                BY <1>1, neg_int_eq_int
            <4> QED
                BY <4>1, add_0
        <3> QED
            BY <3>1, <3>2
    <2> QED
        BY <2>1, <2>2
<1>3. ASSUME NEW b \in Nat,
        -.(a + b) = (-.a) + (-.b)
      PROVE
        -.(a + Succ[b]) = (-.a) + (-.Succ[b])
    <2>1. -.(a + Succ[b]) = -.iSucc[a + b]
        <3>1. a \in Int
            BY <1>1
        <3>2. b \in Nat
            BY <1>3
        <3>3. a + Succ[b] = iSucc[a + b]
            BY <3>1, <3>2, addint_succ_nat
        <3> QED
            BY <3>3
    <2>2. @ = -. iSucc[-.((-.a) + (-.b))]
        <3>1. a + b = -.(-.a + -.b)
            <4>1. -.-.(a + b) = -.(-.a + -.b)
                BY <1>3
            <4>2. -.-.(a + b) = a + b
                <5>1. a + b \in Int
                    <6>1. a \in Int
                        BY <1>1
                    <6>2. b \in Int
                        BY <1>3, nat_in_int
                    <6> QED
                        BY <6>1, <6>2, addIsInt
                <5> QED
                    BY <5>1, minus_involutive
            <4> QED
                BY <4>1, <4>2
        <3> QED
            BY <3>1
    <2>3. @ = iPred[-.a + -.b]
        <3>1. -.a + -.b \in Int
            <4>1. -.a \in Int
                BY <1>1, neg_int_eq_int
            <4>2. -.b \in Int
                BY <1>3, minus_nat_in_int
            <4> QED
                BY <4>1, <4>2, addIsInt
        <3> QED
            BY <3>1, iSuccMinusFlip
    <2>4. @ = -.a + iPred[-.b]
        <3>1. -.a \in Int
            BY <1>1, neg_int_eq_int
        <3>2. -.b \in Int
            BY <1>3, minus_nat_in_int
        <3> QED
            BY <3>1, <3>2, iPredRightDistributesAdd
    <2>5. @ = -.a + -.Succ[b]
        <3>1. iPred[-.b] = -.Succ[-.-.b]
            <4>1. -.b \in Int
                BY <1>3, minus_nat_in_int
            <4>2. -.b \notin Nat \ {0}
                <5>1. -.b \in negNat
                    BY <1>3, minus_nat_in_neg_nat
                <5> QED
                    BY <5>1, neg_nat_not_in_nat_setminus_0
            <4> QED
                BY <4>1, <4>2 DEF iPred
        <3>2. @ = -.Succ[b]
            <4>1. -.-.b = b
                BY <1>3, nat_in_int, minus_involutive
            <4> QED
                BY <4>1
        <3> QED
            BY <3>1, <3>2
    <2> QED
        BY <2>1, <2>2, <2>3, <2>4, <2>5
<1>4. ASSUME NEW b \in negNat,
        -.(a + b) = (-.a) + (-.b)
      PROVE
        -.(a + -.Succ[-.b]) = (-.a) + (-.-.Succ[-.b])
    <2>1. -.(a + -.Succ[-.b]) = -. iPred[a + b]
        <3>1. a + -.Succ[-.b] = iPred[a + -.-.b]
            <4>1. a \in Int
                BY <1>1
            <4>2. -.b \in Nat
                BY <1>4, minus_neg_nat_in_nat
            <4> QED
                BY <4>1, <4>2, addint_succ_negnat
        <3>2. a + -.Succ[-.b] = iPred[a + b]
            <4>1. -.-.b = b
                BY <1>4, neg_nat_in_int, minus_involutive
            <4> QED
                BY <3>1, <4>1
        <3> QED
            BY <3>2
    <2>2. @ = -. iPred[-.((-.a) + (-.b))]
        <3>1. a + b = -.(-.a + -.b)
            <4>1. -.(a + b) = (-.a) + (-.b)
                BY <1>4
            <4>2. -.-.(a + b) = -.(-.a + -.b)
                BY <4>1
            <4>3. -.-.(a + b) = a + b
                <5>1. a + b \in Int
                    <6>1. a \in Int
                        BY <1>1
                    <6>2. b \in Int
                        BY <1>4, neg_nat_in_int
                    <6> QED
                        BY <6>1, <6>2, addIsInt
                <5> QED
                    BY <5>1, minus_involutive
            <4> QED
                BY <4>2, <4>3
        <3> QED
            BY <3>1
    <2>3. @ = iSucc[-.a + -.b]
        <3>1. -.a + -.b \in Int
            <4>1. -.a \in Int
                BY a \in Int, neg_int_eq_int
            <4>2. -.b \in Int
                BY <1>4, minus_negnat_in_int
            <4> QED
                BY <4>1, <4>2, addIsInt
        <3> QED
            BY <3>1, iPredMinusFlip
    <2>4. @ = -.a + iSucc[-.b]
        <3>1. -.a \in Int
            BY a \in Int, neg_int_eq_int
        <3>2. -.b \in Int
            BY <1>4, minus_negnat_in_int
        <3> QED
            BY <3>1, <3>2, iSuccRightDistributesAdd
    <2>5. @ = -.a + Succ[-.b]
        <3>1. -.b \in Nat
            BY <1>4, minus_neg_nat_in_nat
        <3>2. -.b \in Int
            BY <3>1, nat_in_int
        <3> QED
            BY <3>1, <3>2 DEF iSucc
    <2>6. @ = -.a + (-.-.Succ[-.b])
        <3>1. -.b \in Nat
            BY <1>4, minus_neg_nat_in_nat
        <3>2. Succ[-.b] \in Nat
            BY <3>1, succIsNat
        <3>3. Succ[-.b] \in Int
            BY <3>2, nat_in_int
        <3>4. -.-.Succ[-.b] = Succ[-.b]
            BY <3>3, minus_involutive
        <3> QED
            BY <3>4
    <2> QED
        BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6
<1>5. \A b \in Nat:  -.(a + b) = (-.a) + (-.b)
    BY <1>2, <1>3, NatInduction
<1>6. \A b \in negNat:  -.(a + b) = (-.a) + (-.b)
    BY <1>2, <1>4, neg_nat_induction
<1> QED
    BY <1>5, <1>6, int_union_nat_negnat
*)
theorem MinusDistributesAdd:
    "\<forall> a \<in> Int:  \<forall> b \<in> Int:
        -.(a + b) = (-.a) + (-.b)"
    proof -
    {
    fix "a" :: "c"
    assume adom: "a \\in Int"
    have s1_2: "-.(a + 0) = (-.a) + (-.0)"
        proof -
        have s2_1: "-.(a + 0) = -.a"
            proof -
            have s3_1: "a + 0 = a"
                using adom add_0 by auto
            show ?thesis
                using s3_1 by auto
            qed
        have s2_2: "-.a + -.0 = -.a"
            proof -
            have s3_1: "-.a + -.0 = -.a + 0"
                using neg0 by auto
            also have s3_2: "... = -.a"
                proof -
                have s4_1: "-.a \\in Int"
                    using adom neg_int_eq_int by auto
                show ?thesis
                    using s4_1 add_0 by auto
                qed
            finally show ?thesis .
            qed
        show ?thesis
            using s2_1 s2_2 by auto
        qed
    have s1_3: "\<And> b.  \<lbrakk>
        b \\in Nat;
        -.(a + b) = -.a + -.b
        \<rbrakk> \<Longrightarrow>
            -.(a + Succ[b]) = (-.a) + (-.Succ[b])"
        proof -
        fix "b" :: "c"
        assume s1_3_bdom: "b \\in Nat"
        assume s1_3_induct: "-.(a + b) = -.a + -.b"
        have s2_1: "-.(a + Succ[b]) = -.iSucc[a + b]"
            proof -
            have s3_1: "a \\in Int"
                using adom by auto
            have s3_2: "b \\in Nat"
                using s1_3_bdom by auto
            have s3_3: "a + Succ[b] = iSucc[a + b]"
                using s3_1 s3_2 addint_succ_nat by auto
            show ?thesis
                using s3_3 by auto
            qed
        also have s2_2: "... = -. iSucc[-.((-.a) + (-.b))]"
            proof -
            have s3_1: "a + b = -.(-.a + -.b)"
                proof -
                have s4_1: "-.-.(a + b) = -.(-.a + -.b)"
                    using s1_3_induct by auto
                have s4_2: "-.-.(a + b) = a + b"
                    proof -
                    have s5_1: "a + b \\in Int"
                        proof -
                        have s6_1: "a \\in Int"
                            using adom by auto
                        have s6_2: "b \\in Int"
                            using s1_3_bdom nat_in_int by auto
                        show ?thesis
                            using s6_1 s6_2 addIsInt by auto
                        qed
                    show ?thesis
                        using s5_1 minus_involutive by auto
                    qed
                show ?thesis
                    using s4_1 s4_2 by auto
                qed
            show ?thesis
                using s3_1 by auto
            qed
        also have s2_3: "... = iPred[-.a + -.b]"
            proof -
            have s3_1: "-.a + -.b \\in Int"
                proof -
                have s4_1: "-.a \\in Int"
                    using adom neg_int_eq_int by auto
                have s4_2: "-.b \\in Int"
                    using s1_3_bdom minus_nat_in_int by auto
                show ?thesis
                    using s4_1 s4_2 addIsInt by auto
                qed
            show ?thesis
                using s3_1 iSuccMinusFlip by auto
            qed
        also have s2_4: "... = -.a + iPred[-.b]"
            proof -
            have s3_1: "-.a \\in Int"
                using adom neg_int_eq_int by auto
            have s3_2: "-.b \\in Int"
                using s1_3_bdom minus_nat_in_int by auto
            show ?thesis
                using s3_1 s3_2 iPredRightDistributesAdd by auto
            qed
        also have s2_5: "... = -.a + -.Succ[b]"
            proof -
            have s3_1: "iPred[-.b] = -.Succ[-.-.b]"
                proof -
                have s4_1: "-.b \\in Int"
                    using s1_3_bdom minus_nat_in_int by auto
                have s4_2: "-.b \<notin> Nat \<setminus> {0}"
                    proof -
                    have s5_1: "-.b \\in negNat"
                        using s1_3_bdom minus_nat_in_neg_nat by auto
                    show ?thesis
                        using s5_1 neg_nat_not_in_nat_setminus_0 by fast
                    qed
                show ?thesis
                    unfolding iPred_def
                    using s4_1 s4_2 by auto
                qed
            also have s3_2: "... = -.Succ[b]"
                proof -
                have s4_1: "-.-.b = b"
                    using s1_3_bdom nat_in_int minus_involutive by auto
                show ?thesis
                    using s4_1 by auto
                qed
            finally have s3_3: "iPred[-.b] = -.Succ[b]" .
            show ?thesis
                using s3_3 by auto
            qed
        finally show "-.(a + Succ[b]) = (-.a) + (-.Succ[b])" .
        qed
    have s1_4: "\<And> b.  \<lbrakk>
        b \\in negNat;
        -.(a + b) = -.a + -.b
        \<rbrakk> \<Longrightarrow>
            -.(a + -.Succ[-.b]) = (-.a) + (-.-.Succ[-.b])"
        proof -
        fix "b" :: "c"
        assume s1_4_bdom: "b \\in negNat"
        assume s1_4_induct: "-.(a + b) = -.a + -.b"
        have s2_1: "-.(a + -.Succ[-.b]) = -. iPred[a + b]"
            proof -
            have s3_1: "a + -.Succ[-.b] = iPred[a + -.-.b]"
                proof -
                have s4_1: "a \\in Int"
                    using adom by auto
                have s4_2: "-.b \\in Nat"
                    using s1_4_bdom minus_neg_nat_in_nat by auto
                show ?thesis
                    using s4_1 s4_2 addint_succ_negnat by auto
                qed
            have s3_2: "a + -.Succ[-.b] = iPred[a + b]"
                proof -
                have s4_1: "-.-.b = b"
                    using s1_4_bdom neg_nat_in_int minus_involutive
                    by auto
                show ?thesis
                    using s3_1 s4_1 by auto
                qed
            show ?thesis
                using s3_2 by auto
            qed
        also have s2_2: "... = -. iPred[-.((-.a) + (-.b))]"
            proof -
            have s3_1: "a + b = -.(-.a + -.b)"
                proof -
                have s4_1: "-.(a + b) = (-.a) + (-.b)"
                    using s1_4_induct by auto
                have s4_2: "-.-.(a + b) = -.(-.a + -.b)"
                    using s4_1 by auto
                have s4_3: "-.-.(a + b) = a + b"
                    proof -
                    have s5_1: "a + b \\in Int"
                        proof -
                        have s6_1: "a \\in Int"
                            using adom by auto
                        have s6_2: "b \\in Int"
                            using s1_4_bdom neg_nat_in_int by auto
                        show ?thesis
                            using s6_1 s6_2 addIsInt by auto
                        qed
                    show ?thesis
                        using s5_1 minus_involutive by auto
                    qed
                show ?thesis
                    using s4_2 s4_3 by auto
                qed
            show ?thesis
                using s3_1 by auto
            qed
        also have s2_3: "... = iSucc[-.a + -.b]"
            proof -
            have s3_1: "-.a + -.b \\in Int"
                proof -
                have s4_1: "-.a \\in Int"
                    using adom neg_int_eq_int by auto
                have s4_2: "-.b \\in Int"
                    using s1_4_bdom minus_negnat_in_int by auto
                show ?thesis
                    using s4_1 s4_2 addIsInt by auto
                qed
            show ?thesis
                using s3_1 iPredMinusFlip by auto
            qed
        also have s2_4: "... = -.a + iSucc[-.b]"
            proof -
            have s3_1: "-.a \\in Int"
                using adom neg_int_eq_int by auto
            have s3_2: "-.b \\in Int"
                using s1_4_bdom minus_negnat_in_int by auto
            show ?thesis
                using s3_1 s3_2 iSuccRightDistributesAdd by auto
            qed
        also have s2_5: "... = -.a + Succ[-.b]"
            proof -
            have s3_1: "-.b \\in Nat"
                using s1_4_bdom minus_neg_nat_in_nat by auto
            have s3_2: "-.b \\in Int"
                using s3_1 nat_in_int by auto
            show ?thesis
                unfolding iSucc_def
                using s3_1 s3_2 by auto
            qed
        also have s2_6: "... = -.a + (-.-.Succ[-.b])"
            proof -
            have s3_1: "-.b \\in Nat"
                using s1_4_bdom minus_neg_nat_in_nat by auto
            have s3_2: "Succ[-.b] \\in Nat"
                using s3_1 succIsNat by auto
            have s3_3: "Succ[-.b] \\in Int"
                using s3_2 nat_in_int by auto
            have s3_4: "-.-.Succ[-.b] = Succ[-.b]"
                using s3_3 minus_involutive by auto
            show ?thesis
                using s3_4 by auto
            qed
        finally show "-.(a + -.Succ[-.b]) = (-.a) + (-.-.Succ[-.b])" .
        qed
    have s1_5: "\<forall> b \<in> Nat:  -.(a + b) = (-.a) + (-.b)"
        using s1_2 s1_3 natInduct by auto
    have s1_6: "\<forall> b \<in> negNat:  -.(a + b) = (-.a) + (-.b)"
        using s1_2 s1_4 neg_nat_induction by auto
    have s1_7: "\<forall> b \<in> Int:  -.(a + b) = (-.a) + (-.b)"
        using s1_5 s1_6 int_union_nat_negnat by auto
    }
    from this show ?thesis
        by auto
    qed


theorem MinusDistributesAdd_sequent:
    assumes adom: "a \\in Int" and bdom: "b \\in Int"
    shows "-.(a + b) = (-.a) + (-.b)"
    using adom bdom MinusDistributesAdd by auto


(*
THEOREM MinusDiff ==
    ASSUME NEW a \in Int, NEW b \in Int
    PROVE -.(a - b) = b - a
PROOF
<1>1. -.(a - b) = -.(a + -.b)
    BY DEF diff
<1>2. @ = (-.a) + (-.-.b)
    <2>1. a \in Int
        OBVIOUS
    <2>2. -.b \in Int
        BY b \in Int, neg_int_eq_int
    <2> QED
        BY <2>1, <2>2, MinusDistributesAdd
<1>3. @ = (-.a) + b
    BY b \in Int, minus_involutive
<1>4. @ = b + (-.a)
    <2>1. -.a \in Int
        BY a \in Int, neg_int_eq_int
    <2>2. b \in Int
        OBVIOUS
    <2> QED
        BY <2>1, <2>2, AddCommutative
<1>5. @ = b - a
    BY DEF diff
<1> QED
    BY <1>1, <1>2, <1>3, <1>4, <1>5
*)
theorem MinusDiff:
    assumes adom: "a \\in Int" and bdom: "b \\in Int"
    shows "-.(a - b) = b - a"
    proof -
    have s1_1: "-.(a - b) = -.(a + -.b)"
        unfolding diff_def by auto
    also have s1_2: "... = -.a + -.-.b"
        proof -
        have s2_1: "a \\in Int"
            using adom by auto
        have s2_2: "-.b \\in Int"
            using bdom neg_int_eq_int by auto
        show ?thesis
            using s2_1 s2_2 MinusDistributesAdd by auto
        qed
    also have s1_3: "... = -.a + b"
        using bdom minus_involutive by auto
    also have s1_4: "... = b + -.a"
        proof -
        have s2_1: "-.a \\in Int"
            using adom neg_int_eq_int by auto
        have s2_2: "b \\in Int"
            using bdom by auto
        show ?thesis
            using s2_1 s2_2 AddCommutative by auto
        qed
    also have s1_5: "... = b - a"
        unfolding diff_def by auto
    finally show ?thesis .
    qed


(*----------------------------------------------------------------------------*)
(* Commutativity of multiplication. *)

(*
THEOREM MultCommutative ==
    \A i, j \in Int:  i * j = j * i
PROOF
<1>1. \A i \in Int:  i * 0 = 0 * i
    <2>1. 0 * 0 = 0 * 0
        OBVIOUS
    <2>2. ASSUME NEW i \in Nat, i * 0 = 0 * i
          PROVE Succ[i] * 0 = 0 * Succ[i]
        <3>1. 0 * Succ[i] = 0 * i + 0
            <4>1. 0 \in Int
                BY zero_in_int
            <4>2. i \in Nat
                BY <2>2
            <4> QED
                BY <4>1, <4>2, multint_succ_nat
        <3>2. @ = 0 * i
            <4>1. 0 * i \in Int
                <5>1 0 \in Int
                    BY zero_in_int
                <5>2. i \in Int
                    BY <2>2, nat_in_int
                <5> QED
                    BY <5>1, <5>2, multIsInt
            <4> QED
                BY <4>1, add_0
        <3>3. @ = i * 0
            BY <2>2
        <3>4. @ = 0
            <4>1. i \in Int
                BY <2>2, nat_in_int
            <4> QED
                BY <4>1, mult_0
        <3>5. @ = Succ[i] * 0
            <4>1. Succ[i] \in Int
                BY <2>2, succIsNat, nat_in_int
            <4> QED
                BY <4>1, mult_0
        <3> QED
            BY <3>1, <3>2, <3>3, <3>4, <3>5
    <2>3. ASSUME NEW i \in negNat, i * 0 = 0 * i
          PROVE -.Succ[-.i] * 0 = 0 * -.Succ[-.i]
        <3>1. -.Succ[-.i] * 0 = 0
            <4>1. -.Succ[-.i] \in Int
                BY <2>3, minus_succ_minus_negnat_in_int
            <4> QED
                BY <4>1, mult_0
        <3>2. 0 * -.Succ[-.i] = 0
            <4>1. 0 * -.Succ[-.i] = 0 * -.-.i + -.0
                <5>1. 0 \in Int
                    BY zero_in_int
                <5>2. -.i \in Nat
                    BY <2>3, minus_neg_nat_in_nat
                <5> QED
                    BY <5>1, <5>2, multint_succ_negnat
            <4>2. @ = 0 * i + -.0
                <5>1. -.-.i = i
                    BY <2>3, neg_nat_in_int, minus_involutive
                <5> QED
                    BY <5>1
            <4>3. @ = 0 * i + 0
                BY neg0
            <4>4. @ = 0 * i
                <5>1. 0 * i \in Int
                    <6>1. 0 \in Int
                        BY zero_in_int
                    <6>2. i \in Int
                        BY <2>3, neg_nat_in_int
                    <6> QED
                        BY <6>1, <6>2, multIsInt
                <5> QED
                    BY <5>1, add_0
            <4>5. @ = i * 0
                BY <2>3  \* induction hypothesis
            <4>6. @ = 0
                <5>1. i \in Int
                    BY <2>3, neg_nat_in_int
                <5> QED
                    BY <5>1, mult_0
            <4> QED
                BY <4>1, <4>2, <4>3, <4>4,
                    <4>5, <4>6
        <3> QED
            BY <3>1, <3>2
    <2>4. \A i \in Nat:  i * 0 = 0 * i
        BY <2>1, <2>2, NatInduction
    <2>5. \A i \in negNat:  i * 0 = 0 * i
        BY <2>1, <2>3, neg_nat_induction
    <2> QED
        BY <2>4, <2>5, int_union_nat_negnat
<1>2. ASSUME NEW j \in Nat,
            \A i \in Int:  i * j = j * i
      PROVE \A i \in Int:  i * Succ[j] = Succ[j] * i
    <2>1. 0 * Succ[j] = Succ[j] * 0
        <3>1. 0 * Succ[j] = 0
            <4>1. 0 * Succ[j] = 0 * j + 0
                <5>1. 0 \in Int
                    BY zero_in_int
                <5>2. j \in Nat
                    BY <1>2
                <5> QED
                    BY <5>1, <5>2, multint_succ_nat
            <4>2. @ = 0 * j
                <5>1. 0 * j \in Int
                    <6>1. 0 \in Int
                        BY zero_in_int
                    <6>2. j \in Int
                        BY <1>2, nat_in_int
                    <6> QED
                        BY <6>1, <6>2, multIsInt
                <5> QED
                    BY <5>1, add_0
            <4>3. @ = j * 0
                BY <1>2, zero_in_int, spec
            <4>4. @ = 0
                <5>1. j \in Int
                    BY <1>2, nat_in_int
                <5> QED
                    BY <5>1, mult_0
            <4> QED
                BY <4>1, <4>2, <4>3, <4>4
        <3>2. Succ[j] * 0 = 0
            <4>1. Succ[j] \in Int
                BY <1>2, succIsNat, nat_in_int
            <4> QED
                BY <4>1, mult_0
        <3> QED
            BY <3>1, <3>2
    <2>2. ASSUME NEW i \in Nat,
                i * Succ[j] = Succ[j] * i
          PROVE Succ[i] * Succ[j] = Succ[j] * Succ[i]
        <3>1. Succ[i] * Succ[j] = i * j + ((i + j) + 1)
            <4>1. Succ[i] * Succ[j] = Succ[i] * j + Succ[i]
                <5>1. Succ[i] \in Int
                    BY <2>2, succIsNat, nat_in_int
                <5>2. j \in Nat
                    BY <1>2
                <5> QED
                    BY <5>1, <5>2, multint_succ_nat
            <4>2. @ = j * Succ[i] + Succ[i]
                <5>1. Succ[i] \in Int
                    BY <2>2, succIsNat, nat_in_int
                <5>2. \A k \in Int:  k * j = j * k
                    BY <1>2  \* induction hypothesis
                <5>3. Succ[i] * j = j * Succ[i]
                    BY <5>1, <5>2, spec
                <5> QED
                    BY <5>3
            <4>3. @ = (j * i + j) + Succ[i]
                <5>1. j \in Int
                    BY <1>2, nat_in_int
                <5>2. i \in Nat
                    BY <2>2
                <5>3. j * Succ[i] = j * i + j
                    BY <5>1, <5>2, multint_succ_nat
                <5> QED
                    BY <5>3
            <4>4. @ = (i * j + j) + Succ[i]
                <5>1. i \in Int
                    BY <2>2, nat_in_int
                <5>2. \A k \in Int:  k * j = j * k
                    BY <1>2  \* induction hypothesis
                <5>3. i * j = j * i
                    BY <5>1, <5>2, spec
                <5> QED
                    BY <5>3
            <4>5. @ = (i * j + j) + (i + 1)
                <5>1. i \in Nat
                    BY <2>2
                <5>2. Succ[i] = i + 1
                    BY <5>1, nat_add_1
                <5> QED
                    BY <5>2
            <4>6. @ = i * j + (j + (i + 1))
                <5>1. i * j \in Int
                    BY <1>2, <2>2, nat_in_int, multIsInt
                <5>2. j \in Int
                    BY <1>2, nat_in_int
                <5>3. i + 1 \in Int
                    BY <2>2, oneIsNat, nat_in_int, addIsInt
                <5> QED
                    BY <5>1, <5>2, <5>3, AddAssociative
            <4>7. @ = i * j + ((j + i) + 1)
                <5>1. j \in Int
                    BY <1>2, nat_in_int
                <5>2. i \in Int
                    BY <2>2, nat_in_int
                <5>3. 1 \in Int
                    BY oneIsNat, nat_in_int
                <5>4. j + (i + 1) = (j + i) + 1
                    BY <5>1, <5>2, <5>3, AddAssociative
                <5> QED
                    BY <5>4
            <4>8. @ = i * j + ((i + j) + 1)
                <5>1. j \in Int
                    BY <1>2, nat_in_int
                <5>2. i \in Int
                    BY <2>2, nat_in_int
                <5>3. j + i = i + j
                    BY <5>1, <5>2, AddCommutative
                <5> QED
                    BY <5>3
            <4> QED
                BY <4>1, <4>2, <4>3, <4>4, <4>5,
                    <4>6, <4>7, <4>8
        <3>2. Succ[j] * Succ[i] = i * j + ((i + j) + 1)
            <4>1. Succ[j] * Succ[i] = Succ[j] * i + Succ[j]
                <5>1. Succ[j] \in Int
                    BY <1>2, succIsNat, nat_in_int
                <5>2. i \in Nat
                    BY <2>2
                <5> QED
                    BY <5>1, <5>2, multint_succ_nat
            <4>2. @ = i * Succ[j] + Succ[j]
                BY <2>2  \* induction hypothesis
            <4>3. @ = (i * j + i) + Succ[j]
                <5>1. i \in Int
                    BY <2>2, nat_in_int
                <5>2. j \in Nat
                    BY <1>2
                <5>3. i * Succ[j] = i * j + i
                    BY <5>1, <5>2, multint_succ_nat
                <5> QED
                    BY <5>3
            <4>4. @ = (i * j + i) + (j + 1)
                <5>1. j \in Nat
                    BY <1>2
                <5>2. Succ[j] = j + 1
                    BY <5>1, nat_add_1
                <5> QED
                    BY <5>2
            <4>5. @ = i * j + (i + (j + 1))
                <5>1. i * j \in Int
                    BY <1>2, <2>2, nat_in_int, multIsInt
                <5>2. i \in Int
                    BY <2>2, nat_in_int
                <5>3. j + 1 \in Int
                    BY <1>2, oneIsNat, nat_in_int, addIsInt
                <5> QED
                    BY <5>1, <5>2, <5>3, AddAssociative
            <4>6. @ = i * j + ((i + j) + 1)
                <5>1. i \in Int
                    BY <2>2, nat_in_int
                <5>2. j \in Int
                    BY <1>2, nat_in_int
                <5>3. 1 \in Int
                    BY oneIsNat, nat_in_int
                <5>4. i + (j + 1) = (i + j) + 1
                    BY <5>1, <5>2, <5>3, AddAssociative
                <5> QED
                    BY <5>4
            <4> QED
                BY <4>1, <4>2, <4>3, <4>4, <4>5, <4>6
        <3> QED
            BY <3>1, <3>2
    <2>3. ASSUME NEW i \in negNat,
                i * Succ[j] = Succ[j] * i
          PROVE -.Succ[-.i] * Succ[j] = Succ[j] * -.Succ[-.i]
        <3>1. -.Succ[-.i] * Succ[j] =
                i * j + ((i + -.j) + -.1)
            <4>1. -.Succ[-.i] * Succ[j] =
                    -.Succ[-.i] * j + -.Succ[-.i]
                <5>1. -.Succ[-.i] \in Int
                    BY <2>3, minus_negnat_succ_in_negnat, neg_nat_in_int
                <5>2. j \in Nat
                    BY <1>2
                <5> QED
                    BY <5>1, <5>2, multint_succ_nat
            <4>2. @ = j * -.Succ[-.i] + -.Succ[-.i]
                <5>1. -.Succ[-.i] \in Int
                    BY <2>3, minus_negnat_succ_in_negnat, neg_nat_in_int
                <5>2. \A k \in Int:  k * j = j * k
                    BY <1>2  \* induction hypothesis
                <5>3. -.Succ[-.i] * j = j * -.Succ[-.i]
                    BY <5>1, <5>2, spec
                <5> QED
                    BY <5>3
            <4>3. @ = (j * -.-.i + -.j) + -.Succ[-.i]
                <5>1. j \in Int
                    BY <1>2, nat_in_int
                <5>2. -.i \in Nat
                    BY <2>3, minus_neg_nat_in_nat
                <5>3. j * -.Succ[-.i] = j * -.-.i + -.j
                    BY <5>1, <5>2, multint_succ_negnat
                <5> QED
                    BY <5>3
            <4>4. @ = (j * i + -.j) + -.Succ[-.i]
                <5>1. i \in Int
                    BY <2>3, neg_nat_in_int
                <5>2. -.-.i = i
                    BY <5>1, minus_involutive
                <5> QED
                    BY <5>2
            <4>5. @ = (i * j + -.j) + -.Succ[-.i]
                <5>1. i \in Int
                    BY <2>3, neg_nat_in_int
                <5>2. \A k \in Int:  k * j = j * k
                    BY <1>2  \* induction hypothesis
                <5>3. i * j = j * i
                    BY <5>1, <5>2, spec
                <5> QED
                    BY <5>3
            <4>6. @ = (i * j + -.j) + (i + -.1)
                <5>1. -.i \in Nat
                    BY <2>3, minus_neg_nat_in_nat
                <5>2. -.Succ[-.i] = -.-.i + -.1
                    BY <5>1, MinusSuccIsMinusOne
                <5>3. -.-.i = i
                    BY <2>3, neg_nat_in_int, minus_involutive
                <5>4. -.Succ[-.i] = i + -.1
                    BY <5>2, <5>3
                <5> QED
                    BY <5>4
            <4>7. @ = i * j + (-.j + (i + -.1))
                <5>1. i * j \in Int
                    BY <1>2, nat_in_int, <2>3, neg_nat_in_int,
                        multIsInt
                <5>2. -.j \in Int
                    BY <1>2, minus_nat_in_int
                <5>3. i + -.1 \in Int
                    BY <2>3, minus_one_in_negnat,
                        neg_nat_in_int, addIsInt
                <5> QED
                    BY <5>1, <5>2, <5>3, AddAssociative
            <4>8. @ = i * j + ((-.j + i) + -.1)
                <5>1. -.j \in Int
                    BY <1>2, minus_nat_in_int
                <5>2. i \in Int
                    BY <2>3, neg_nat_in_int
                <5>3. -.1 \in Int
                    BY minus_one_in_negnat, neg_nat_in_int
                <5>4. -.j + (i + -.1) = (-.j + i) + -.1
                    BY <5>1, <5>2, <5>3, AddAssociative
                <5> QED
                    BY <5>4
            <4>9. @ = i * j + ((i + -.j) + -.1)
                <5>1. -.j \in Int
                    BY <1>2, minus_nat_in_int
                <5>2. i \in Int
                    BY <2>3, neg_nat_in_int
                <5>3. -.j + i = i + -.j
                    BY <5>1, <5>2, AddCommutative
                <5> QED
                    BY <5>3
            <4> QED
                BY <4>1, <4>2, <4>3, <4>4,
                    <4>5, <4>6, <4>7, <4>8, <4>9
        <3>2. Succ[j] * -.Succ[-.i] =
                i * j + ((i + -.j) + -.1)
            <4>1. Succ[j] * -.Succ[-.i] =
                    Succ[j] * -.-.i + -.Succ[j]
                <5>1. Succ[j] \in Int
                    BY <1>2, succIsNat, nat_in_int
                <5>2. -.i \in Nat
                    BY <2>3, minus_neg_nat_in_nat
                <5> QED
                    BY <5>1, <5>2, multint_succ_negnat
            <4>2. @ = Succ[j] * i + -.Succ[j]
                <5>1. i \in Int
                    BY <2>3, neg_nat_in_int
                <5>2. -.-.i = i
                    BY <5>1, minus_involutive
                <5> QED
                    BY <5>2
            <4>3. @ = i * Succ[j] + -.Succ[j]
                BY <2>3  \* induction hypothesis
            <4>4. @ = (i * j + i) + -.Succ[j]
                <5>1. i \in Int
                    BY <2>3, neg_nat_in_int
                <5>2. j \in Nat
                    BY <1>2
                <5>3. i * Succ[j] = i * j + i
                    BY <5>1, <5>2, multint_succ_nat
                <5> QED
                    BY <5>3
            <4>5. @ = (i * j + i) + (-.j + -.1)
                <5>1. j \in Nat
                    BY <1>2
                <5>2. -.Succ[j] = -.j + -.1
                    BY <5>1, MinusSuccIsMinusOne
                <5> QED
                    BY <5>2
            <4>6. @ = i * j + (i + (-.j + -.1))
                <5>1. i * j \in Int
                    <6>1. i \in Int
                        BY <2>3, neg_nat_in_int
                    <6>2. j \in Int
                        BY <1>2, nat_in_int
                    <6> QED
                        BY <6>1, <6>2, multIsInt
                <5>2. i \in Int
                    BY <2>3, neg_nat_in_int
                <5>3. -.j + -.1 \in Int
                    <6>1. -.j \in Int
                        BY <1>2, minus_nat_in_int
                    <6>2. -.1 \in Int
                        BY minus_one_in_negnat, neg_nat_in_int
                    <6> QED
                        BY <6>1, <6>2, addIsInt
                <5> QED
                    BY <5>1, <5>2, <5>3, AddAssociative
            <4>7. @ = i * j + ((i + -.j) + -.1)
                <5>1. i \in Int
                    BY <2>3, neg_nat_in_int
                <5>2. -.j \in Int
                    BY <1>2, minus_nat_in_int
                <5>3. -.1 \in Int
                    BY minus_one_in_negnat, neg_nat_in_int
                <5>4. i + (-.j + -.1) = (I + -.j) + -.1
                    BY <5>1, <5>2, <5>3, AddAssociative
                <5> QED
                    BY <5>4
            <4> QED
                BY <4>1, <4>2, <4>3, <4>4, <4>5,
                    <4>6, <4>7
        <3> QED
            BY <3>1, <3>2
    <2> QED
        BY <2>1, <2>2, <2>3, NatInduction, neg_nat_induction,
            int_union_nat_negnat
<1>3. ASSUME NEW j \in negNat,
            \A i \in Int:  i * j = j * i
      PROVE \A i \in Int:  i * -.Succ[-.j] = -.Succ[-.j] * i
    <2>1. 0 * -.Succ[-.j] = -.Succ[-.j] * 0
        <3>1. 0 * -.Succ[-.j] = 0 * -.-.j + -.0
            <4>1. 0 \in Int
                BY zeroIsNat nat_in_int
            <4>2. -.j \in Nat
                BY <1>3, minus_neg_nat_in_nat
            <4> QED
                BY <4>1, <4>2, multint_succ_negnat
        <3>2. @ = 0 * -.-.j
            <4>1. 0 * -.-.j \in Int
                <5>1. 0 \in Int
                    BY zeroIsNat nat_in_int
                <5>2. -.-.j \in Int
                    BY <1>3, neg_nat_in_int, minus_involutive
                <5> QED
                    BY <5>1, <5>2, multIsInt
            <4>2. 0 * -.-.j + 0 = 0 * -.-.j
                BY <4>1, add_0
            <4> QED
                BY <4>2, neg0
        <3>3. @ = 0 * j
            <4>1. j \in Int
                BY <1>3, neg_nat_in_int
            <4> QED
                BY <4>1, minus_involutive
        <3>4. @ = j * 0
            <4>1. 0 \in Int
                BY zeroIsNat, nat_in_int
            <4>2. \A k \in Int:  k * j = j * k
                BY <1>3  \* induction hypothesis
            <4> QED
                BY <4>1, <4>2, spec
        <3>5. @ = 0
            <4>1. j \in Int
                BY <1>3, neg_nat_in_int
            <4> QED
                BY <4>1, mult_0
        <3>6. @ = -.Succ[-.j] * 0
            <4>1. -.Succ[-.j] \in Int
                BY <1>3, minus_negnat_succ_in_negnat, neg_nat_in_int
            <4> QED
                BY <4>1, mult_0
        <3> QED
            BY <3>1, <3>2, <3>3, <3>4, <3>5, <3>6
    <2>2. ASSUME NEW i \in Nat,
                i * -.Succ[-.j] = -.Succ[-.j] * i
          PROVE Succ[i] * -.Succ[-.j] = -.Succ[-.j] * Succ[i]
        <3>1. Succ[i] * -.Succ[-.j] = i * j + ((-.i + j) + -.1)
            <4>1. Succ[i] * -.Succ[-.j] =
                    Succ[i] * -.-.j + -.Succ[i]
                <5>1. Succ[i] \in Int
                    BY <2>2, succIsNat, nat_in_int
                <5>2. -.j \in Nat
                    BY <1>3, minus_neg_nat_in_nat
                <5> QED
                    BY <5>1, <5>2, multint_succ_negnat
            <4>2. @ = Succ[i] * j + -.Succ[i]
                <5>1. j \in Int
                    BY <1>3, neg_nat_in_int
                <5>2. -.-.j = j
                    BY <5>1, minus_involutive
                <5> QED
                    BY <5>2
            <4>3. @ = j * Succ[i] + -.Succ[i]
                <5>1. Succ[i] \in Int
                    BY <2>2, succIsNat, nat_in_int
                <5>2. \A k \in Int:  k * j = j * k
                    BY <1>3  \* induction hypothesis
                <5>3. Succ[i] * j = j * Succ[i]
                    BY <5>1, <5>2, spec
                <5> QED
                    BY <5>3
            <4>4. @ = (j * i + j) + -.Succ[i]
                <5>1. j \in Int
                    BY <1>3, neg_nat_in_int
                <5>2. i \in Nat
                    BY <2>2
                <5>3. j * Succ[i] = j * i + j
                    BY <5>1, <5>2, multint_succ_nat
                <5> QED
                    BY <5>3
            <4>5. @ = (i * j + j) + -.Succ[i]
                <5>1. i \in Int
                    BY <2>2, nat_in_int
                <5>2. \A k \in Int:  k * j = j * k
                    BY <1>3  \* induction hypothesis
                <5>3. i * j = j * i
                    BY <5>1, <5>2, spec
                <5> QED
                    BY <5>3
            <4>6. @ = i * j + (j + -.Succ[i])
                <5>1. i * j \in Int
                    <6>1. i \in Int
                        BY <2>2, nat_in_int
                    <6>2. j \in Int
                        BY <1>3, neg_nat_in_int
                    <6> QED
                        BY <6>1, <6>2, multIsInt
                <5>2. j \in Int
                    BY <1>3, neg_nat_in_int
                <5>3. -.Succ[i] \in Int
                    BY <2>2, succIsNat, minus_nat_in_int
                <5> QED
                    BY <5>1, <5>2, <5>3, AddAssociative
            <4>7. @ = i * j + (j + (-.i + -.1))
                <5>1. i \in Nat
                    BY <2>2
                <5>2. -.Succ[i] = -.i + -.1
                    BY <5>1, MinusSuccIsMinusOne
                <5> QED
                    BY <5>2
            <4>8. @ = i * j + ((j + -.i) + -.1)
                <5>1. j \in Int
                    BY <1>3, neg_nat_in_int
                <5>2. -.i \in Int
                    BY <2>2, minus_nat_in_int
                <5>3. -.1 \in Int
                    BY minus_one_in_int
                <5>4. j + (-.i + -.1) = (j + -.i) + -.1
                    BY <5>1, <5>2, <5>3, AddAssociative
                <5> QED
                    BY <5>4
            <4>9. @ = i * j + ((-.i + j) + -.1)
                <5>1. j \in Int
                    BY <1>3, neg_nat_in_int
                <5>2. -.i \in Int
                    BY <2>2, minus_nat_in_int
                <5>3. j + -.i = -.i + j
                    BY <5>1, <5>2, AddCommutative
                <5> QED
                    BY <5>3
            <4> QED
                BY <4>1, <4>2, <4>3, <4>4, <4>5,
                    <4>6, <4>7, <4>8, <4>9
        <3>2. -.Succ[-.j] * Succ[i] = i * j + ((-.i + j) + -.1)
            <4>1. -.Succ[-.j] * Succ[i] =
                    -.Succ[-.j] * i + -.Succ[-.j]
                <5>1. -.Succ[-.j] \in Int
                    BY <1>3, minus_negnat_succ_in_negnat,
                        neg_nat_in_int
                <5>2. i \in Nat
                    BY <2>2
                <5> QED
                    BY <5>1, <5>2, multint_succ_nat
            <4>2. @ = i * -.Succ[-.j] + -.Succ[-.j]
                BY <2>2  \* induction hypothesis
            <4>3. @ = (i * -.-.j + -.i) + -.Succ[-.j]
                <5>1. i \in Int
                    BY <2>2, nat_in_int
                <5>2. -.j \in Nat
                    BY <1>3, minus_neg_nat_in_nat
                <5>3. i * -.Succ[-.j] = i * -.-.j + -.i
                    BY <5>1, <5>2, multint_succ_negnat
                <5> QED
                    BY <5>3
            <4>4. @ = (i * j + -.i) + -.Succ[-.j]
                <5>1. j \in Int
                    BY <1>3, neg_nat_in_int
                <5>2. -.-.j = j
                    BY <5>1, minus_involutive
                <5> QED
                    BY <5>2
            <4>5. @ = (i * j + -.i) + (-.-.j + -.1)
                <5>1. -.j \in Nat
                    BY <1>3, minus_neg_nat_in_nat
                <5>2. -.Succ[-.j] = -.-.j + -.1
                    BY <5>1, MinusSuccIsMinusOne
                <5> QED
                    BY <5>2
            <4>6. @ = (i * j + -.i) + (j + -.1)
                <5>1. j \in Int
                    BY <1>3, neg_nat_in_int
                <5>2. -.-.j = j
                    BY <5>1, minus_involutive
                <5> QED
                    BY <5>2
            <4>7. @ = i * j + (-.i + (j + -.1))
                <5>1. i * j \in Int
                    <6>1. i \in Int
                        BY <2>2, nat_in_int
                    <6>2. j \in Int
                        BY <1>3, neg_nat_in_int
                    <6> QED
                        BY <6>1, <6>2, multIsInt
                <5>2. -.i \in Int
                    BY <2>2, minus_nat_in_int
                <5>3. j + -.1 \in Int
                    <6>1. j \in Int
                        BY <1>3, neg_nat_in_int
                    <6>2. -.1 \in Int
                        BY minus_one_in_int
                    <6> QED
                        BY <6>1, <6>2, addIsInt
                <5> QED
                    BY <5>1, <5>2, <5>3, AddAssociative
            <4>8. @ = i * j + ((-.i + j) + -.1)
                <5>1. -.i \in Int
                    BY <2>2, minus_nat_in_int
                <5>2. j \in Int
                    BY <1>3, neg_nat_in_int
                <5>3. -.1 \in Int
                    BY minus_one_in_int
                <5>4. -.i + (j + -.1) = (-.i + j) + -.1
                    BY <5>1, <5>2, <5>3, AddAssociative
                <5> QED
                    BY <5>4
            <4> QED
                BY <4>1, <4>2, <4>3, <4>4, <4>5,
                    <4>6, <4>7, <4>8
        <3> QED
            BY <3>1, <3>2
    <2>3. ASSUME NEW i \in negNat,
                i * -.Succ[-.j] = -.Succ[-.j] * i
          PROVE -.Succ[-.i] * -.Succ[-.j] = -.Succ[-.j] * -.Succ[-.i]
        <3>1. -.Succ[-.i] * -.Succ[-.j] =
                    i * j + ((-.i + -.j) + 1)
            <4>1. -.Succ[-.i] * -.Succ[-.j] =
                    -.Succ[-.i] * -.-.j + -.-.Succ[-.i]
                <5>1. -.Succ[-.i] \in Int
                    BY <2>3, minus_negnat_succ_in_negnat,
                        neg_nat_in_int
                <5>2. -.j \in Nat
                    BY <1>3, minus_neg_nat_in_nat
                <5> QED
                    BY <5>1, <5>2, multint_succ_negnat
            <4>2. @ = -.Succ[-.i] * j + -.-.Succ[-.i]
                <5>1. j \in Int
                    BY <1>3, neg_nat_in_int
                <5>2. -.-.j = j
                    BY <5>1, minus_involutive
                <5> QED
                    BY <5>2
            <4>3. @ = -.Succ[-.i] * j + Succ[-.i]
                <5>1. Succ[-.i] \in Int
                    BY <2>3, negnat_succ_in_nat, nat_in_int
                <5>2. -.-.Succ[-.i] = Succ[-.i]
                    BY <5>1, minus_involutive
                <5> QED
                    BY <5>2
            <4>4. @ = j * -.Succ[-.i] + Succ[-.i]
                <5>1. -.Succ[-.i] \in Int
                    BY <2>3, minus_negnat_succ_in_negnat, neg_nat_in_int
                <5>2. \A k \in Int:  k * j = j * k
                    BY <1>3  \* induction hypothesis
                <5>3. -.Succ[-.i] * j = j * -.Succ[-.i]
                    BY <5>1, <5>2, spec
                <5> QED
                    BY <5>3
            <4>5. @ = (j * -.-.i + -.j) + Succ[-.i]
                <5>1. j \in Int
                    BY <1>3, neg_nat_in_int
                <5>2. -.i \in Nat
                    BY <2>3, minus_neg_nat_in_nat
                <5>3. j * -.Succ[-.i] = j * -.-.i + -.j
                    BY <5>1, <5>2, multint_succ_negnat
                <5> QED
                    BY <5>3
            <4>6. @ = (j * i + -.j) + Succ[-.i]
                <5>1. i \in Int
                    BY <2>3, neg_nat_in_int
                <5>2. -.-.i = i
                    BY <5>1, minus_involutive
                <5> QED
                    BY <5>2
            <4>7. @ = (i * j + -.j) + Succ[-.i]
                <5>1. i \in Int
                    BY <2>3, neg_nat_in_int
                <5>2. \A k \in Int:  k * j = j * k
                    BY <1>3  \* induction hypothesis
                <5>3. i * j = j * i
                    BY <5>1, <5>2, spec
                <5> QED
                    BY <5>3
            <4>8. @ = (i * j + -.j) + (-.i + 1)
                <5>1. i \in negNat
                    BY <2>3
                <5>2. Succ[-.i] = -.i + 1
                    BY <5>1, SuccMinusIsPlusOne
                <5> QED
                    BY <5>2
            <4>9. @ = i * j + (-.j + (-.i + 1))
                <5>1. i * j \in Int
                    <6>1. i \in Int
                        BY <2>3, neg_nat_in_int
                    <6>2. j \in Int
                        BY <1>3, neg_nat_in_int
                    <6> QED
                        BY <6>1, <6>2, multIsInt
                <5>2. -.j \in Int
                    BY <1>3, minus_negnat_in_int
                <5>3. -.i + 1 \in Int
                    <6>1. -.i \in Int
                        BY <2>3, minus_negnat_in_int
                    <6>2. 1 \in Int
                        BY oneIsNat, nat_in_int
                    <6> QED
                        BY <6>1, <6>2, addIsInt
                <5> QED
                    BY <5>1, <5>2, <5>3, AddAssociative
            <4>10. @ = i * j + ((-.j + -.i) + 1)
                <5>1. -.j \in Int
                    BY <1>3, minus_negnat_in_int
                <5>2. -.i \in Int
                    BY <2>3, minus_negnat_in_int
                <5>3. 1 \in Int
                    BY oneIsNat, nat_in_int
                <5>4. -.j + (-.i + 1) = (-.j + -.i) + 1
                    BY <5>1, <5>2, <5>3, AddAssociative
                <5> QED
                    BY <5>4
            <4>11. @ = i * j + ((-.i + -.j) + 1)
                <5>1. -.j \in Int
                    BY <1>3, minus_negnat_in_int
                <5>2. -.i \in Int
                    BY <2>3, minus_negnat_in_int
                <5>3. -.j + -.i = -.i + -.j
                    BY <5>1, <5>2, AddCommutative
                <5> QED
                    BY <5>3
            <4> QED
                BY <4>1, <4>2, <4>3, <4>4, <4>5,
                    <4>6, <4>7, <4>8, <4>9,
                    <4>10, <4>11
        <3>2. -.Succ[-.j] * -.Succ[-.i] =
                i * j + ((-.i + -.j) + 1)
            <4>1. -.Succ[-.j] * -.Succ[-.i] =
                    -.Succ[-.j] * -.-.i + -.-.Succ[-.j]
                <5>1. -.Succ[-.j] \in Int
                    BY <1>3, minus_succ_minus_negnat_in_int
                <5>2. -.i \in Nat
                    BY <2>3, minus_neg_nat_in_nat
                <5> QED
                    BY <5>1, <5>2, multint_succ_negnat
            <4>2. @ = -.Succ[-.j] * i + -.-.Succ[-.j]
                <5>1. i \in Int
                    BY <2>3, neg_nat_in_int
                <5>2. -.-.i = i
                    BY <5>1, minus_involutive
                <5> QED
                    BY <5>2
            <4>3. @ = -.Succ[-.j] * i + Succ[-.j]
                <5>1. Succ[-.j] \in Int
                    BY <1>3, negnat_succ_in_nat, nat_in_int
                <5>2. -.-.Succ[-.j] = Succ[-.j]
                    BY <5>1, minus_involutive
                <5> QED
                    BY <5>2
            <4>4. @ = i * -.Succ[-.j] + Succ[-.j]
                BY <2>3  \* induction hypothesis
            <4>5. @ = (i * -.-.j + -.i) + Succ[-.j]
                <5>1. i \in Int
                    BY <2>3, neg_nat_in_int
                <5>2. -.j \in Nat
                    BY <1>3, minus_neg_nat_in_nat
                <5>3. i * -.Succ[-.j] = i * -.-.j + -.i
                    BY <5>1, <5>2, multint_succ_negnat
                <5> QED
                    BY <5>3
            <4>6. @ = (i * j + -.i) + Succ[-.j]
                <5>1. j \in Int
                    BY <1>3, neg_nat_in_int
                <5>2. -.-.j = j
                    BY <5>1, minus_involutive
                <5> QED
                    BY <5>2
            <4>7. @ = i * j + (-.i + Succ[-.j])
                <5>1. i * j \in Int
                    <6>1. i \in Int
                        BY <2>3, neg_nat_in_int
                    <6>2. j \in Int
                        BY <1>3, neg_nat_in_int
                    <6> QED
                        BY <6>1, <6>2, multIsInt
                <5>2. -.i \in Int
                    BY <2>3, minus_negnat_in_int
                <5>3. Succ[-.j] \in Int
                    BY <1>3, negnat_succ_in_nat, nat_in_int
                <5> QED
                    BY <5>1, <5>2, <5>3, AddAssociative
            <4>8. @ = i * j + (-.i + (-.j + 1))
                <5>1. Succ[-.j] = -.j + 1
                    BY <1>3, SuccMinusIsPlusOne
                <5> QED
                    BY <5>1
            <4>9. @ = i * j + ((-.i + -.j) + 1)
                <5>1. -.i \in Int
                    BY <2>3, minus_negnat_in_int
                <5>2. -.j \in Int
                    BY <1>3, minus_negnat_in_int
                <5>3. 1 \in Int
                    BY oneIsNat, nat_in_int
                <5>4. -.i + (-.j + 1) = (-.i + -.j) + 1
                    BY <5>1, <5>2, <5>3, AddAssociative
                <5> QED
                    BY <5>4
            <4> QED
                BY <4>1, <4>2, <4>3, <4>4, <4>5,
                    <4>6, <4>7, <4>8, <4>9
        <3> QED
            BY <3>1, <3>2
    <2> QED
        BY <2>1, <2>2, NatInduction, neg_nat_induction,
            int_union_nat_negnat
<1> QED
    BY <1>1, <1>2, <1>3, NatInduction, neg_nat_induction,
        int_union_nat_negnat
*)
theorem MultCommutative:
    "\<forall> i \<in> Int:  \<forall> j \<in> Int:
        i * j = j * i"
    proof -
    have s1_1: "\<forall> i \<in> Int:  i * 0 = 0 * i"
        proof -
        have s2_1: "0 * 0 = 0 * 0"
            by auto
        have s2_2: "\<And> i.  \<lbrakk>
                i \\in Nat;
                i * 0 = 0 * i
            \<rbrakk> \<Longrightarrow>
                Succ[i] * 0 = 0 * Succ[i]"
            proof -
            fix "i" :: "c"
            assume s2_2_idom: "i \\in Nat"
            assume s2_2_induct: "i * 0 = 0 * i"
            have s3_1: "0 * Succ[i] = 0 * i + 0"
                proof -
                have s4_1: "0 \\in Int"
                    using zero_in_int by auto
                have s4_2: "i \\in Nat"
                    using s2_2_idom by auto
                show ?thesis
                    using s4_1 s4_2 multint_succ_nat by auto
                qed
            also have s3_2: "... = 0 * i"
                proof -
                have s4_1: "0 * i \\in Int"
                    proof -
                    have s5_1: "0 \\in Int"
                        using zero_in_int by auto
                    have s5_2: "i \\in Int"
                        using s2_2_idom nat_in_int by auto
                    show ?thesis
                        using s5_1 s5_2 multIsInt by auto
                    qed
                show ?thesis
                    using s4_1 add_0 by auto
                qed
            also have s3_3: "... = i * 0"
                using s2_2_induct by auto
            also have s3_4: "... = 0"
                proof -
                have s4_1: "i \\in Int"
                    using s2_2_idom nat_in_int by auto
                show ?thesis
                    using s4_1 mult_0 by auto
                qed
            also have s3_5: "... = Succ[i] * 0"
                proof -
                have s4_1: "Succ[i] \\in Int"
                    using s2_2_idom succIsNat nat_in_int by auto
                show ?thesis
                    using s4_1 mult_0 by auto
                qed
            finally show "Succ[i] * 0 = 0 * Succ[i]" by auto
            qed
        have s2_3: "\<And> i.  \<lbrakk>
                i \\in negNat;
                i * 0 = 0 * i
            \<rbrakk> \<Longrightarrow>
                -.Succ[-.i] * 0 = 0 * -.Succ[-.i]"
            proof -
            fix "i" :: "c"
            assume s2_3_idom: "i \\in negNat"
            assume s2_3_induct: "i * 0 = 0 * i"
            have s3_1: "-.Succ[-.i] * 0 = 0"
                proof -
                have s4_1: "-.Succ[-.i] \\in Int"
                    using s2_3_idom minus_succ_minus_negnat_in_int by auto
                show ?thesis
                    using s4_1 mult_0 by auto
                qed
            have s3_2: "0 * -.Succ[-.i] = 0"
                proof -
                have s4_1: "0 * -.Succ[-.i] = 0 * -.-.i + -.0"
                    proof -
                    have s5_1: "0 \\in Int"
                        using zero_in_int by auto
                    have s5_2: "-.i \\in Nat"
                        using s2_3_idom minus_neg_nat_in_nat by auto
                    show ?thesis
                        using s5_1 s5_2 multint_succ_negnat by auto
                    qed
                also have s4_2: "... = 0 * i + -.0"
                    proof -
                    have s5_1: "-.-.i = i"
                        using s2_3_idom neg_nat_in_int
                            minus_involutive by auto
                    show ?thesis
                        using s5_1 by auto
                    qed
                also have s4_3: "... = 0 * i + 0"
                    using neg0 by auto
                also have s4_4: "... = 0 * i"
                    proof -
                    have s5_1: "0 * i \\in Int"
                        proof -
                        have s6_1: "0 \\in Int"
                            using zero_in_int by auto
                        have s6_2: "i \\in Int"
                            using s2_3_idom neg_nat_in_int by auto
                        show ?thesis
                            using s6_1 s6_2 multIsInt by auto
                        qed
                    show ?thesis
                        using s5_1 add_0 by auto
                    qed
                also have s4_5: "... = i * 0"
                    using s2_3_induct by auto
                also have s4_6: "... = 0"
                    proof -
                    have s5_1: "i \\in Int"
                        using s2_3_idom neg_nat_in_int by auto
                    show ?thesis
                        using s5_1 mult_0 by auto
                    qed
                finally show ?thesis .
                qed
            show "-.Succ[-.i] * 0 = 0 * -.Succ[-.i]"
                using s3_1 s3_2 by auto
            qed
        have s2_4: "\<forall> i \<in> Nat:  i * 0 = 0 * i"
            using s2_1 s2_2 natInduct by auto
        have s2_5: "\<forall> i \<in> negNat:  i * 0 = 0 * i"
            using s2_1 s2_3 neg_nat_induction by auto
        show ?thesis
            using s2_4 s2_5 int_union_nat_negnat by auto
        qed
    have s1_2: "\<And> j.  \<lbrakk>
            j \\in Nat;
            \<forall> i \<in> Int:  i * j = j * i
        \<rbrakk> \<Longrightarrow>
            \<forall> i \<in> Int:  i * Succ[j] = Succ[j] * i"
        proof -
        fix "j" :: "c"
        assume s1_2_jdom: "j \\in Nat"
        assume s1_2_induct: "\<forall> i \<in> Int:  i * j = j * i"
        have s2_1: "0 * Succ[j] = Succ[j] * 0"
            proof -
            have s3_1: "0 * Succ[j] = 0"
                proof -
                have s4_1: "0 * Succ[j] = 0 * j + 0"
                    proof -
                    have s5_1: "0 \\in Int"
                        using zero_in_int by auto
                    have s5_2: "j \\in Nat"
                        using s1_2_jdom by auto
                    show ?thesis
                        using s5_1 s5_2 multint_succ_nat by auto
                    qed
                also have s4_2: "... = 0 * j"
                    proof -
                    have s5_1: "0 * j \\in Int"
                        proof -
                        have s6_1: "0 \\in Int"
                            using zero_in_int by auto
                        have s6_2: "j \\in Int"
                            using s1_2_jdom nat_in_int by auto
                        show ?thesis
                            using s6_1 s6_2 multIsInt by auto
                        qed
                    show ?thesis
                        using s5_1 add_0 by auto
                    qed
                also have s4_3: "... = j * 0"
                    proof -
                    have s5_1: "0 \\in Int"
                        using zero_in_int by auto
                    have s5_2: "\<forall> k \<in> Int:  k * j = j * k"
                        using s1_2_induct by auto
                    show ?thesis
                        using s5_1 s5_2 spec by fast
                    qed
                also have s4_4: "... = 0"
                    proof -
                    have s5_1: "j \\in Int"
                        using s1_2_jdom nat_in_int by auto
                    show ?thesis
                        using s5_1 mult_0 by auto
                    qed
                finally show ?thesis .
                qed
            have s3_2: "Succ[j] * 0 = 0"
                proof -
                have s4_1: "Succ[j] \\in Int"
                    using s1_2_jdom succIsNat nat_in_int by auto
                show ?thesis
                    using s4_1 mult_0 by auto
                qed
            show ?thesis
                using s3_1 s3_2 by auto
            qed
        have s2_2: "\<And> i.  \<lbrakk>
                i \\in Nat;
                i * Succ[j] = Succ[j] * i
            \<rbrakk> \<Longrightarrow>
                Succ[i] * Succ[j] = Succ[j] * Succ[i]"
            proof -
            fix "i" :: "c"
            assume s2_2_idom: "i \\in Nat"
            assume s2_2_induct: "i * Succ[j] = Succ[j] * i"
            have s3_1: "Succ[i] * Succ[j] = i * j + ((i + j) + 1)"
                proof -
                have s4_1: "Succ[i] * Succ[j] = Succ[i] * j + Succ[i]"
                    proof -
                    have s5_1: "Succ[i] \\in Int"
                        using s2_2_idom succIsNat nat_in_int by auto
                    have s5_2: "j \\in Nat"
                        using s1_2_jdom by auto
                    show ?thesis
                        using s5_1 s5_2 multint_succ_nat by auto
                    qed
                also have s4_2: "... = j * Succ[i] + Succ[i]"
                    proof -
                    have s5_1: "Succ[i] \\in Int"
                        using s2_2_idom succIsNat nat_in_int by auto
                    have s5_2: "\<forall> k \<in> Int:
                        k * j = j * k"
                        using s1_2_induct by auto
                    have s5_3: "Succ[i] * j = j * Succ[i]"
                        using s5_1 s5_2 spec by fast
                    show ?thesis
                        using s5_3 by auto
                    qed
                also have s4_3: "... = (j * i + j) + Succ[i]"
                    proof -
                    have s5_1: "j \\in Int"
                        using s1_2_jdom nat_in_int by auto
                    have s5_2: "i \\in Nat"
                        using s2_2_idom by auto
                    have s5_3: "j * Succ[i] = j * i + j"
                        using s5_1 s5_2 multint_succ_nat by auto
                    show ?thesis
                        using s5_3 by auto
                    qed
                also have s4_4: "... = (i * j + j) + Succ[i]"
                    proof -
                    have s5_1: "i \\in Int"
                        using s2_2_idom nat_in_int by auto
                    have s5_2: "\<forall> k \<in> Int:
                        k * j = j * k"
                        using s1_2_induct by auto
                    have s5_3: "i * j = j * i"
                        using s5_1 s5_2 spec by fast
                    show ?thesis
                        using s5_3 by auto
                    qed
                also have s4_5: "... = (i * j + j) + (i + 1)"
                    proof -
                    have s5_1: "i \\in Nat"
                        using s2_2_idom by auto
                    have s5_2: "Succ[i] = i + 1"
                        using s5_1 nat_add_1 by fast
                    show ?thesis
                        using s5_2 by auto
                    qed
                also have s4_6: "... = i * j + (j + (i + 1))"
                    proof -
                    have s5_1: "i * j \\in Int"
                        proof -
                        have s6_1: "i \\in Int"
                            using s2_2_idom nat_in_int by auto
                        have s6_2: "j \\in Int"
                            using s1_2_jdom nat_in_int by auto
                        show ?thesis
                            using s6_1 s6_2 multIsInt by auto
                        qed
                    have s5_2: "j \\in Int"
                        using s1_2_jdom nat_in_int by auto
                    have s5_3: "i + 1 \\in Int"
                        proof -
                        have s6_1: "i \\in Int"
                            using s2_2_idom nat_in_int by auto
                        have s6_2: "1 \\in Nat"
                            using oneIsNat nat_in_int by auto
                        show ?thesis
                            using s6_1 s6_2 addIsInt by auto
                        qed
                    show ?thesis
                        using s5_1 s5_2 s5_3
                            AddAssociative_sequent by auto
                    qed
                also have s4_7: "... = i * j + ((j + i) + 1)"
                    proof -
                    have s5_1: "j \\in Int"
                        using s1_2_jdom nat_in_int by auto
                    have s5_2: "i \\in Int"
                        using s2_2_idom nat_in_int by auto
                    have s5_3: "1 \\in Int"
                        using oneIsNat nat_in_int by auto
                    have s5_4: "j + (i + 1) = (j + i) + 1"
                        using s5_1 s5_2 s5_3
                            AddAssociative_sequent by auto
                    show ?thesis
                        using s5_4 by auto
                    qed
                also have s4_8: "... = i * j + ((i + j) + 1)"
                    proof -
                    have s5_1: "j \\in Int"
                        using s1_2_jdom nat_in_int by auto
                    have s5_2: "i \\in Int"
                        using s2_2_idom nat_in_int by auto
                    have s5_3: "j + i = i + j"
                        using s5_1 s5_2 AddCommutative_sequent by auto
                    show ?thesis
                        using s5_3 by auto
                    qed
                finally show ?thesis .
                qed
            have s3_2: "Succ[j] * Succ[i] = i * j + ((i + j) + 1)"
                proof -
                have s4_1: "Succ[j] * Succ[i] = Succ[j] * i + Succ[j]"
                    proof -
                    have s5_1: "Succ[j] \\in Int"
                        using s1_2_jdom succIsNat nat_in_int by auto
                    have s5_2: "i \\in Nat"
                        using s2_2_idom by auto
                    show ?thesis
                        using s5_1 s5_2 multint_succ_nat by auto
                    qed
                also have s4_2: "... = i * Succ[j] + Succ[j]"
                    using s2_2_induct by auto
                also have s4_3: "... = (i * j + i) + Succ[j]"
                    proof -
                    have s5_1: "i \\in Int"
                        using s2_2_idom nat_in_int by auto
                    have s5_2: "j \\in Nat"
                        using s1_2_jdom by auto
                    have s5_3: "i * Succ[j] = i * j + i"
                        using s5_1 s5_2 multint_succ_nat by auto
                    show ?thesis
                        using s5_3 by auto
                    qed
                also have s4_4: "... = (i * j + i) + (j + 1)"
                    proof -
                    have s5_1: "j \\in Nat"
                        using s1_2_jdom by auto
                    have s5_2: "Succ[j] = j + 1"
                        using s5_1 nat_add_1 by fast
                    show ?thesis
                        using s5_2 by auto
                    qed
                also have s4_5: "... = i * j + (i + (j + 1))"
                    proof -
                    have s5_1: "i * j \\in Int"
                        using s1_2_jdom s2_2_idom nat_in_int multIsInt by auto
                    have s5_2: "i \\in Int"
                        using s2_2_idom nat_in_int by auto
                    have s5_3: "j + 1 \\in Int"
                        using s1_2_jdom oneIsNat nat_in_int addIsInt by auto
                    show ?thesis
                        using s5_1 s5_2 s5_3 AddAssociative_sequent by auto
                    qed
                also have s4_6: "... = i * j + ((i + j) + 1)"
                    proof -
                    have s5_1: "i \\in Int"
                        using s2_2_idom nat_in_int by auto
                    have s5_2: "j \\in Int"
                        using s1_2_jdom nat_in_int by auto
                    have s5_3: "1 \\in Int"
                        using oneIsNat nat_in_int by auto
                    have s5_4: "i + (j + 1) = (i + j) + 1"
                        using s5_1 s5_2 s5_3
                            AddAssociative_sequent by auto
                    show ?thesis
                        using s5_4 by auto
                    qed
                finally show ?thesis .
                qed
            show "Succ[i] * Succ[j] = Succ[j] * Succ[i]"
                using s3_1 s3_2 by auto
            qed
        have s2_3: "\<And> i.  \<lbrakk>
                i \\in negNat;
                i * Succ[j] = Succ[j] * i
            \<rbrakk> \<Longrightarrow>
                -.Succ[-.i] * Succ[j] = Succ[j] * -.Succ[-.i]"
            proof -
            fix "i" :: "c"
            assume s2_3_idom: "i \\in negNat"
            assume s2_3_induct: "i * Succ[j] = Succ[j] * i"
            have s3_1: "-.Succ[-.i] * Succ[j] =
                    i * j + ((i + -.j) + -.1)"
                proof -
                have s4_1: "-.Succ[-.i] * Succ[j] =
                        -.Succ[-.i] * j + -.Succ[-.i]"
                    proof -
                    have s5_1: "-.Succ[-.i] \\in Int"
                        using s2_3_idom minus_negnat_succ_in_negnat
                            neg_nat_in_int by auto
                    have s5_2: "j \\in Nat"
                        using s1_2_jdom by auto
                    show ?thesis
                        using s5_1 s5_2 multint_succ_nat by auto
                    qed
                also have s4_2: "... = j * -.Succ[-.i] + -.Succ[-.i]"
                    proof -
                    have s5_1: "-.Succ[-.i] \\in Int"
                        using s2_3_idom minus_negnat_succ_in_negnat
                            neg_nat_in_int by auto
                    have s5_2: "\<forall> k \<in> Int:  k * j = j * k"
                        using s1_2_induct by auto
                    have s5_3: "-.Succ[-.i] * j = j * -.Succ[-.i]"
                        using s5_1 s5_2 spec by fast
                    show ?thesis
                        using s5_3 by auto
                    qed
                also have s4_3: "... = (j * -.-.i + -.j) + -.Succ[-.i]"
                    proof -
                    have s5_1: "j \\in Int"
                        using s1_2_jdom nat_in_int by auto
                    have s5_2: "-.i \\in Nat"
                        using s2_3_idom minus_neg_nat_in_nat by auto
                    have s5_3: "j * -.Succ[-.i] = j * -.-.i + -.j"
                        using s5_1 s5_2 multint_succ_negnat by auto
                    show ?thesis
                        using s5_3 by auto
                    qed
                also have s4_4: "... = (j * i + -.j) + -.Succ[-.i]"
                    proof -
                    have s5_1: "i \\in Int"
                        using s2_3_idom neg_nat_in_int by auto
                    have s5_2: "-.-.i = i"
                        using s5_1 minus_involutive by auto
                    show ?thesis
                        using s5_2 by auto
                    qed
                also have s4_5: "... = (i * j + -.j) + -.Succ[-.i]"
                    proof -
                    have s5_1: "i \\in Int"
                        using s2_3_idom neg_nat_in_int by auto
                    have s5_2: "\<forall> k \<in> Int:  k * j = j * k"
                        using s1_2_induct by auto
                    have s5_3: "i * j = j * i"
                        using s5_1 s5_2 spec by fast
                    show ?thesis
                        using s5_3 by auto
                    qed
                also have s4_6: "... = (i * j + -.j) + (i + -.1)"
                    proof -
                    have s5_1: "-.i \\in Nat"
                        using s2_3_idom minus_neg_nat_in_nat by auto
                    have s5_2: "-.Succ[-.i] = -.-.i + -.1"
                        using s5_1 MinusSuccIsMinusOne by fast
                    have s5_3: "-.-.i = i"
                        using s2_3_idom neg_nat_in_int minus_involutive
                        by auto
                    have s5_4: "-.Succ[-.i] = i + -.1"
                        using s5_2 s5_3 by auto
                    show ?thesis
                        using s5_4 by auto
                    qed
                also have s4_7: "... = i * j + (-.j + (i + -.1))"
                    proof -
                    have s5_1: "i * j \\in Int"
                        using s1_2_jdom nat_in_int s2_3_idom
                            neg_nat_in_int multIsInt by auto
                    have s5_2: "-.j \\in Int"
                        using s1_2_jdom minus_nat_in_int by auto
                    have s5_3: "i + -.1 \\in Int"
                        using s2_3_idom minus_one_in_negnat
                            neg_nat_in_int addIsInt by auto
                    show ?thesis
                        using s5_1 s5_2 s5_3
                            AddAssociative_sequent by auto
                    qed
                also have s4_8: "... = i * j + ((-.j + i) + -.1)"
                    proof -
                    have s5_1: "-.j \\in Int"
                        using s1_2_jdom minus_nat_in_int by auto
                    have s5_2: "i \\in Int"
                        using s2_3_idom neg_nat_in_int by auto
                    have s5_3: "-.1 \\in Int"
                        using minus_one_in_negnat neg_nat_in_int by auto
                    have s5_4: " -.j + (i + -.1) = (-.j + i) + -.1"
                        using s5_1 s5_2 s5_3
                            AddAssociative_sequent by auto
                    show ?thesis
                        using s5_4 by auto
                    qed
                also have s4_9: "... = i * j + ((i + -.j) + -.1)"
                    proof -
                    have s5_1: "-.j \\in Int"
                        using s1_2_jdom minus_nat_in_int by auto
                    have s5_2: "i \\in Int"
                        using s2_3_idom neg_nat_in_int by auto
                    have s5_3: "-.j + i = i + -.j"
                        using s5_1 s5_2 AddCommutative_sequent
                        by auto
                    show ?thesis
                        using s5_3 by auto
                    qed
                finally show ?thesis .
                qed
            have s3_2: "Succ[j] * -.Succ[-.i] =
                    i * j + ((i + -.j) + -.1)"
                proof -
                have s4_1: "Succ[j] * -.Succ[-.i] =
                        Succ[j] * -.-.i + -.Succ[j]"
                    proof -
                    have s5_1: "Succ[j] \\in Int"
                        using s1_2_jdom succIsNat nat_in_int by auto
                    have s5_2: "-.i \\in Nat"
                        using s2_3_idom minus_neg_nat_in_nat by auto
                    show ?thesis
                        using s5_1 s5_2 multint_succ_negnat by auto
                    qed
                also have s4_2: "... = Succ[j] * i + -.Succ[j]"
                    proof -
                    have s5_1: "i \\in Int"
                        using s2_3_idom neg_nat_in_int by auto
                    have s5_2: "-.-.i = i"
                        using s5_1 minus_involutive by auto
                    show ?thesis
                        using s5_2 by auto
                    qed
                also have s4_3: "... = i * Succ[j] + -.Succ[j]"
                    using s2_3_induct by auto
                also have s4_4: "... = (i * j + i) + -.Succ[j]"
                    proof -
                    have s5_1: "i \\in Int"
                        using s2_3_idom neg_nat_in_int by auto
                    have s5_2: "j \\in Nat"
                        using s1_2_jdom by auto
                    have s5_3: "i * Succ[j] = i * j + i"
                        using s5_1 s5_2 multint_succ_nat by auto
                    show ?thesis
                        using s5_3 by auto
                    qed
                also have s4_5: "... = (i * j + i) + (-.j + -.1)"
                    proof -
                    have s5_1: "j \\in Nat"
                        using s1_2_jdom by auto
                    have s5_2: "-.Succ[j] = -.j + -.1"
                        using s5_1 MinusSuccIsMinusOne by fast
                    show ?thesis
                        using s5_2 by auto
                    qed
                also have s4_6: "... = i * j + (i + (-.j + -.1))"
                    proof -
                    have s5_1: "i * j \\in Int"
                        proof -
                        have s6_1: "i \\in Int"
                            using s2_3_idom neg_nat_in_int by auto
                        have s6_2: "j \\in Int"
                            using s1_2_jdom nat_in_int by auto
                        show ?thesis
                            using s6_1 s6_2 multIsInt by auto
                        qed
                    have s5_2: "i \\in Int"
                        using s2_3_idom neg_nat_in_int by auto
                    have s5_3: "-.j + -.1 \\in Int"
                        proof -
                        have s6_1: "-.j \\in Int"
                            using s1_2_jdom minus_nat_in_int by auto
                        have s6_2: "-.1 \\in Int"
                            using minus_one_in_negnat neg_nat_in_int by auto
                        show ?thesis
                            using s6_1 s6_2 addIsInt by auto
                        qed
                    show ?thesis
                        using s5_1 s5_2 s5_3
                            AddAssociative_sequent by auto
                    qed
                also have s4_7: "... = i * j + ((i + -.j) + -.1)"
                    proof -
                    have s5_1: "i \\in Int"
                        using s2_3_idom neg_nat_in_int by auto
                    have s5_2: "-.j \\in Int"
                        using s1_2_jdom minus_nat_in_int by auto
                    have s5_3: "-.1 \\in Int"
                        using minus_one_in_negnat neg_nat_in_int by auto
                    have s5_4: "i + (-.j + -.1) = (i + -.j) + -.1"
                        using s5_1 s5_2 s5_3
                            AddAssociative_sequent by auto
                    show ?thesis
                        using s5_4 by auto
                    qed
                finally show ?thesis .
                qed
            show "-.Succ[-.i] * Succ[j] = Succ[j] * -.Succ[-.i]"
                using s3_1 s3_2 by auto
            qed
        have s2_4: "\<forall> i \<in> Nat:  i * Succ[j] = Succ[j] * i"
            using s2_1 s2_2 natInduct by auto
        have s2_5: "\<forall> i \<in> negNat:  i * Succ[j] = Succ[j] * i"
            using s2_1 s2_3 neg_nat_induction by auto
        show "\<forall> i \<in> Int:  i * Succ[j] = Succ[j] * i"
            using s2_4 s2_5 int_union_nat_negnat by auto
        qed
    have s1_3: "\<And> j.  \<lbrakk>
            j \\in negNat;
            \<forall> i \<in> Int:  i * j = j * i
        \<rbrakk> \<Longrightarrow>
            \<forall> i \<in> Int:  i * -.Succ[-.j] = -.Succ[-.j] * i"
        proof -
        fix "j" :: "c"
        assume s1_3_jdom: "j \\in negNat"
        assume s1_3_induct: "\<forall> i \<in> Int:  i * j = j * i"
        have s2_1: "0 * -.Succ[-.j] = -.Succ[-.j] * 0"
            proof -
            have s3_1: "0 * -.Succ[-.j] = 0 * -.-.j + -.0"
                proof -
                have s4_1: "0 \\in Int"
                    using zeroIsNat nat_in_int by auto
                have s4_2: "-.j \\in Nat"
                    using s1_3_jdom minus_neg_nat_in_nat by auto
                show ?thesis
                    using s4_1 s4_2 multint_succ_negnat by auto
                qed
            also have s3_2: "... = 0 * -.-.j"
                proof -
                have s4_1: "0 * -.-.j \\in Int"
                    proof -
                    have s5_1: "0 \\in Int"
                        using zeroIsNat nat_in_int by auto
                    have s5_2: "-.-.j \\in Int"
                        using s1_3_jdom neg_nat_in_int minus_involutive
                        by auto
                    show ?thesis
                        using s5_1 s5_2 multIsInt by auto
                    qed
                have s4_2: "0 * -.-.j + 0 = 0 * -.-.j"
                    using s4_1 add_0 by auto
                show ?thesis
                    using s4_2 neg0 by auto
                qed
            also have s3_3: "... = 0 * j"
                proof -
                have s4_1: "j \\in Int"
                    using s1_3_jdom neg_nat_in_int by auto
                show ?thesis
                    using s4_1 minus_involutive by auto
                qed
            also have s3_4: "... = j * 0"
                proof -
                have s4_1: "0 \\in Int"
                    using zeroIsNat nat_in_int by auto
                have s4_2: "\<forall> k \<in> Int:  k * j = j * k"
                    using s1_3_induct by auto
                show ?thesis
                    using s4_1 s4_2 spec by fast
                qed
            also have s3_5: "... = 0"
                proof -
                have s4_1: "j \\in Int"
                    using s1_3_jdom neg_nat_in_int by auto
                show ?thesis
                    using s4_1 mult_0 by auto
                qed
            also have s3_6: "... = -.Succ[-.j] * 0"
                proof -
                have s4_1: "-.Succ[-.j] \\in Int"
                    using s1_3_jdom minus_negnat_succ_in_negnat
                        neg_nat_in_int by auto
                show ?thesis
                    using s4_1 mult_0 by auto
                qed
            finally show ?thesis .
            qed
        have s2_2: "\<And> i.  \<lbrakk>
                i \\in Nat;
                i * -.Succ[-.j] = -.Succ[-.j] * i
            \<rbrakk> \<Longrightarrow>
                Succ[i] * -.Succ[-.j] = -.Succ[-.j] * Succ[i]"
            proof -
            fix "i" :: "c"
            assume s2_2_idom: "i \\in Nat"
            assume s2_2_induct: "i * -.Succ[-.j] = -.Succ[-.j] * i"
            have s3_1: "Succ[i] * -.Succ[-.j] =
                        i * j + ((-.i + j) + -.1)"
                proof -
                have s4_1: "Succ[i] * -.Succ[-.j] =
                        Succ[i] * -.-.j + -.Succ[i]"
                    proof -
                    have s5_1: "Succ[i] \\in Int"
                        using s2_2_idom succIsNat nat_in_int by auto
                    have s5_2: "-.j \\in Nat"
                        using s1_3_jdom minus_neg_nat_in_nat by auto
                    show ?thesis
                        using s5_1 s5_2 multint_succ_negnat by auto
                    qed
                also have s4_2: "... = Succ[i] * j + -.Succ[i]"
                    proof -
                    have s5_1: "j \\in Int"
                        using s1_3_jdom neg_nat_in_int by auto
                    have s5_2: "-.-.j = j"
                        using s5_1 minus_involutive by auto
                    show ?thesis
                        using s5_2 by auto
                    qed
                also have s4_3: "...  = j * Succ[i] + -.Succ[i]"
                    proof -
                    have s5_1: "Succ[i] \\in Int"
                        using s2_2_idom succIsNat nat_in_int by auto
                    have s5_2: "\<forall> k \<in> Int:  k * j = j * k"
                        using s1_3_induct by auto
                    have s5_3: "Succ[i] * j = j * Succ[i]"
                        using s5_1 s5_2 spec by auto
                    show ?thesis
                        using s5_3 by auto
                    qed
                also have s4_4: "... = (j * i + j) + -.Succ[i]"
                    proof -
                    have s5_1: "j \\in Int"
                        using s1_3_jdom neg_nat_in_int by auto
                    have s5_2: "i \\in Nat"
                        using s2_2_idom by auto
                    have s5_3: "j * Succ[i] = j * i + j"
                        using s5_1 s5_2 multint_succ_nat by auto
                    show ?thesis
                        using s5_3 by auto
                    qed
                also have s4_5: "... = (i * j + j) + -.Succ[i]"
                    proof -
                    have s5_1: "i \\in Int"
                        using s2_2_idom nat_in_int by auto
                    have s5_2: "\<forall> k \<in> Int:  k * j = j * k"
                        using s1_3_induct by auto
                    have s5_3: "i * j = j * i"
                        using s5_1 s5_2 spec by auto
                    show ?thesis
                        using s5_3 by auto
                    qed
                also have s4_6: "... = i * j + (j + -.Succ[i])"
                    proof -
                    have s5_1: "i * j \\in Int"
                        proof -
                        have s6_1: "i \\in Int"
                            using s2_2_idom nat_in_int by auto
                        have s6_2: "j \\in Int"
                            using s1_3_jdom neg_nat_in_int by auto
                        show ?thesis
                            using s6_1 s6_2 multIsInt by auto
                        qed
                    have s5_2: "j \\in Int"
                        using s1_3_jdom neg_nat_in_int by auto
                    have s5_3: "-.Succ[i] \\in Int"
                        using s2_2_idom succIsNat minus_nat_in_int by auto
                    show ?thesis
                        using s5_1 s5_2 s5_3 AddAssociative_sequent by auto
                    qed
                also have s4_7: "... = i * j + (j + (-.i + -.1))"
                    proof -
                    have s5_1: "i \\in Nat"
                        using s2_2_idom by auto
                    have s5_2: "-.Succ[i] = -.i + -.1"
                        using s5_1 MinusSuccIsMinusOne by fast
                    show ?thesis
                        using s5_2 by auto
                    qed
                also have s4_8: "... = i * j + ((j + -.i) + -.1)"
                    proof -
                    have s5_1: "j \\in Int"
                        using s1_3_jdom neg_nat_in_int by auto
                    have s5_2: "-.i \\in Int"
                        using s2_2_idom minus_nat_in_int by auto
                    have s5_3: "-.1 \\in Int"
                        using minus_one_in_int by auto
                    have s5_4: "j + (-.i + -.1) = (j + -.i) + -.1"
                        using s5_1 s5_2 s5_3
                            AddAssociative_sequent by auto
                    show ?thesis
                        using s5_4 by auto
                    qed
                also have s4_9: "... = i * j + ((-.i + j) + -.1)"
                    proof -
                    have s5_1: "j \\in Int"
                        using s1_3_jdom neg_nat_in_int by auto
                    have s5_2: "-.i \\in Int"
                        using s2_2_idom minus_nat_in_int by auto
                    have s5_3: "j + -.i = -.i + j"
                        using s5_1 s5_2 AddCommutative_sequent by auto
                    show ?thesis
                        using s5_3 by auto
                    qed
                finally show ?thesis .
                qed
            have s3_2: "-.Succ[-.j] * Succ[i] =
                        i * j + ((-.i + j) + -.1)"
                proof -
                have s4_1: "-.Succ[-.j] * Succ[i] =
                        -.Succ[-.j] * i + -.Succ[-.j]"
                    proof -
                    have s5_1: "-.Succ[-.j] \\in Int"
                        using s1_3_jdom minus_negnat_succ_in_negnat
                            neg_nat_in_int by auto
                    have s5_2: "i \\in Nat"
                        using s2_2_idom by auto
                    show ?thesis
                        using s5_1 s5_2 multint_succ_nat by auto
                    qed
                also have s4_2: "... = i * -.Succ[-.j] + -.Succ[-.j]"
                    using s2_2_induct by auto
                also have s4_3: "... = (i * -.-.j + -.i) + -.Succ[-.j]"
                    proof -
                    have s5_1: "i \\in Int"
                        using s2_2_idom nat_in_int by auto
                    have s5_2: "-.j \\in Nat"
                        using s1_3_jdom minus_neg_nat_in_nat by auto
                    have s5_3: "i * -.Succ[-.j] = i * -.-.j + -.i"
                        using s5_1 s5_2 multint_succ_negnat by auto
                    show ?thesis
                        using s5_3 by auto
                    qed
                also have s4_4: "... = (i * j + -.i) + -.Succ[-.j]"
                    proof -
                    have s5_1: "j \\in Int"
                        using s1_3_jdom neg_nat_in_int by auto
                    have s5_2: "-.-.j = j"
                        using s5_1 minus_involutive by auto
                    show ?thesis
                        using s5_2 by auto
                    qed
                also have s4_5: "... = (i * j + -.i) + (-.-.j + -.1)"
                    proof -
                    have s5_1: "-.j \\in Nat"
                        using s1_3_jdom minus_neg_nat_in_nat by auto
                    have s5_2: "-.Succ[-.j] = -.-.j + -.1"
                        using s5_1 MinusSuccIsMinusOne by fast
                    show ?thesis
                        using s5_2 by auto
                    qed
                also have s4_6: "... = (i * j + -.i) + (j + -.1)"
                    proof -
                    have s5_1: "j \\in Int"
                        using s1_3_jdom neg_nat_in_int by auto
                    have s5_2: "-.-.j = j"
                        using s5_1 minus_involutive by auto
                    show ?thesis
                        using s5_2 by auto
                    qed
                also have s4_7: "... = i * j + (-.i + (j + -.1))"
                    proof -
                    have s5_1: "i * j \\in Int"
                        proof -
                        have s6_1: "i \\in Int"
                            using s2_2_idom nat_in_int by auto
                        have s6_2: "j \\in Int"
                            using s1_3_jdom neg_nat_in_int by auto
                        show ?thesis
                            using s6_1 s6_2 multIsInt by auto
                        qed
                    have s5_2: "-.i \\in Int"
                        using s2_2_idom minus_nat_in_int by auto
                    have s5_3: "j + -.1 \\in Int"
                        proof -
                        have s6_1: "j \\in Int"
                            using s1_3_jdom neg_nat_in_int by auto
                        have s6_2: "-.1 \\in Int"
                            using minus_one_in_int by auto
                        show ?thesis
                            using s6_1 s6_2 addIsInt by auto
                        qed
                    show ?thesis
                        using s5_1 s5_2 s5_3 AddAssociative_sequent by auto
                    qed
                also have s4_8: "... = i * j + ((-.i + j) + -.1)"
                    proof -
                    have s5_1: "-.i \\in Int"
                        using s2_2_idom minus_nat_in_int by auto
                    have s5_2: "j \\in Int"
                        using s1_3_jdom neg_nat_in_int by auto
                    have s5_3: "-.1 \\in Int"
                        using minus_one_in_int by auto
                    have s5_4: "-.i + (j + -.1) = (-.i + j) + -.1"
                        using s5_1 s5_2 s5_3 AddAssociative_sequent by auto
                    show ?thesis
                        using s5_4 by auto
                    qed
                finally show ?thesis .
                qed
            show "Succ[i] * -.Succ[-.j] = -.Succ[-.j] * Succ[i]"
                using s3_1 s3_2 by auto
            qed
        have s2_3: "\<And> i.  \<lbrakk>
                i \\in negNat;
                i * -.Succ[-.j] = -.Succ[-.j] * i
            \<rbrakk> \<Longrightarrow>
                -.Succ[-.i] * -.Succ[-.j] = -.Succ[-.j] * -.Succ[-.i]"
            proof -
            fix "i" :: "c"
            assume s2_3_idom: "i \\in negNat"
            assume s2_3_induct: "i * -.Succ[-.j] = -.Succ[-.j] * i"
            have s3_1: "-.Succ[-.i] * -.Succ[-.j] =
                        i * j + ((-.i + -.j) + 1)"
                proof -
                have s4_1: "-.Succ[-.i] * -.Succ[-.j] =
                        -.Succ[-.i] * -.-.j + -.-.Succ[-.i]"
                    proof -
                    have s5_1: "-.Succ[-.i] \\in Int"
                        using s2_3_idom minus_negnat_succ_in_negnat
                            neg_nat_in_int by auto
                    have s5_2: "-.j \\in Nat"
                        using s1_3_jdom minus_neg_nat_in_nat by auto
                    show ?thesis
                        using s5_1 s5_2 multint_succ_negnat by auto
                    qed
                also have s4_2: "... = -.Succ[-.i] * j + -.-.Succ[-.i]"
                    proof -
                    have s5_1: "j \\in Int"
                        using s1_3_jdom neg_nat_in_int by auto
                    have s5_2: "-.-.j = j"
                        using s5_1 minus_involutive by auto
                    show ?thesis
                        using s5_2 by auto
                    qed
                also have s4_3: "... = -.Succ[-.i] * j + Succ[-.i]"
                    proof -
                    have s5_1: "Succ[-.i] \\in Int"
                        using s2_3_idom negnat_succ_in_nat nat_in_int by auto
                    have s5_2: "-.-.Succ[-.i] = Succ[-.i]"
                        using s5_1 minus_involutive by auto
                    show ?thesis
                        using s5_2 by auto
                    qed
                also have s4_4: "... = j * -.Succ[-.i] + Succ[-.i]"
                    proof -
                    have s5_1: "-.Succ[-.i] \\in Int"
                        using s2_3_idom minus_negnat_succ_in_negnat
                            neg_nat_in_int by auto
                    have s5_2: "\<forall> k \<in> Int:
                                    k * j = j * k"
                        using s1_3_induct by auto
                    have s5_3: "-.Succ[-.i] * j = j * -.Succ[-.i]"
                        using s5_1 s5_2 spec by auto
                    show ?thesis
                        using s5_3 by auto
                    qed
                also have s4_5: "... = (j * -.-.i + -.j) + Succ[-.i]"
                    proof -
                    have s5_1: "j \\in Int"
                        using s1_3_jdom neg_nat_in_int by auto
                    have s5_2: "-.i \\in Nat"
                        using s2_3_idom minus_neg_nat_in_nat by auto
                    have s5_3: "j * -.Succ[-.i] = j * -.-.i + -.j"
                        using s5_1 s5_2 multint_succ_negnat by auto
                    show ?thesis
                        using s5_3 by auto
                    qed
                also have s4_6: "... = (j * i + -.j) + Succ[-.i]"
                    proof -
                    have s5_1: "i \\in Int"
                        using s2_3_idom neg_nat_in_int by auto
                    have s5_2: "-.-.i = i"
                        using s5_1 minus_involutive by auto
                    show ?thesis
                        using s5_2 by auto
                    qed
                also have s4_7: "... = (i * j + -.j) + Succ[-.i]"
                    proof -
                    have s5_1: "i \\in Int"
                        using s2_3_idom neg_nat_in_int by auto
                    have s5_2: "\<forall> k \<in> Int:
                                    k * j = j * k"
                        using s1_3_induct by auto
                    have s5_3: "i * j = j * i"
                        using s5_1 s5_2 spec by auto
                    show ?thesis
                        using s5_3 by auto
                    qed
                also have s4_8: "... = (i * j + -.j) + (-.i + 1)"
                    proof -
                    have s5_1: "i \\in negNat"
                        using s2_3_idom by auto
                    have s5_2: "Succ[-.i] = -.i + 1"
                        using s5_1 SuccMinusIsPlusOne by fast
                    show ?thesis
                        using s5_2 by auto
                    qed
                also have s4_9: "... = i * j + (-.j + (-.i + 1))"
                    proof -
                    have s5_1: "i * j \\in Int"
                        proof -
                        have s6_1: "i \\in Int"
                            using s2_3_idom neg_nat_in_int by auto
                        have s6_2: "j \\in Int"
                            using s1_3_jdom neg_nat_in_int by auto
                        show ?thesis
                            using s6_1 s6_2 multIsInt by auto
                        qed
                    have s5_2: "-.j \\in Int"
                        using s1_3_jdom minus_negnat_in_int by auto
                    have s5_3: "-.i + 1 \\in Int"
                        proof -
                        have s6_1: "-.i \\in Int"
                            using s2_3_idom minus_negnat_in_int by auto
                        have s6_2: "1 \\in Int"
                            using oneIsNat nat_in_int by auto
                        show ?thesis
                            using s6_1 s6_2 addIsInt by auto
                        qed
                    show ?thesis
                        using s5_1 s5_2 s5_3 AddAssociative_sequent by auto
                    qed
                also have s4_10: "... = i * j + ((-.j + -.i) + 1)"
                    proof -
                    have s5_1: "-.j \\in Int"
                        using s1_3_jdom minus_negnat_in_int by auto
                    have s5_2: "-.i \\in Int"
                        using s2_3_idom minus_negnat_in_int by auto
                    have s5_3: "1 \\in Int"
                        using oneIsNat nat_in_int by auto
                    have s5_4: "-.j + (-.i + 1) = (-.j + -.i) + 1"
                        using s5_1 s5_2 s5_3 AddAssociative_sequent by auto
                    show ?thesis
                        using s5_4 by auto
                    qed
                also have s4_11: "... = i * j + ((-.i + -.j) + 1)"
                    proof -
                    have s5_1: "-.j \\in Int"
                        using s1_3_jdom minus_negnat_in_int by auto
                    have s5_2: "-.i \\in Int"
                        using s2_3_idom minus_negnat_in_int by auto
                    have s5_3: "-.j + -.i = -.i + -.j"
                        using s5_1 s5_2 AddCommutative_sequent by auto
                    show ?thesis
                        using s5_3 by auto
                    qed
                finally show ?thesis .
                qed
            have s3_2: "-.Succ[-.j] * -.Succ[-.i] =
                    i * j + ((-.i + -.j) + 1)"
                proof -
                have s4_1: "-.Succ[-.j] * -.Succ[-.i] =
                        -.Succ[-.j] * -.-.i + -.-.Succ[-.j]"
                    proof -
                    have s5_1: "-.Succ[-.j] \\in Int"
                        using s1_3_jdom minus_succ_minus_negnat_in_int
                        by auto
                    have s5_2: "-.i \\in Nat"
                        using s2_3_idom minus_neg_nat_in_nat by auto
                    show ?thesis
                        using s5_1 s5_2 multint_succ_negnat by auto
                    qed
                also have s4_2: "... = -.Succ[-.j] * i + -.-.Succ[-.j]"
                    proof -
                    have s5_1: "i \\in Int"
                        using s2_3_idom neg_nat_in_int by auto
                    have s5_2: "-.-.i = i"
                        using s5_1 minus_involutive by auto
                    show ?thesis
                        using s5_2 by auto
                    qed
                also have s4_3: "... = -.Succ[-.j] * i + Succ[-.j]"
                    proof -
                    have s5_1: "Succ[-.j] \\in Int"
                        using s1_3_jdom negnat_succ_in_nat
                            nat_in_int by auto
                    have s5_2: "-.-.Succ[-.j] = Succ[-.j]"
                        using s5_1 minus_involutive by auto
                    show ?thesis
                        using s5_2 by auto
                    qed
                also have s4_4: "... = i * -.Succ[-.j] + Succ[-.j]"
                    using s2_3_induct by auto
                also have s4_5: "... = (i * -.-.j + -.i) + Succ[-.j]"
                    proof -
                    have s5_1: "i \\in Int"
                        using s2_3_idom neg_nat_in_int by auto
                    have s5_2: "-.j \\in Nat"
                        using s1_3_jdom minus_neg_nat_in_nat by auto
                    have s5_3: "i * -.Succ[-.j] = i * -.-.j + -.i"
                        using s5_1 s5_2 multint_succ_negnat by auto
                    show ?thesis
                        using s5_3 by auto
                    qed
                also have s4_6: "... = (i * j + -.i) + Succ[-.j]"
                    proof -
                    have s5_1: "j \\in Int"
                        using s1_3_jdom neg_nat_in_int by auto
                    have s5_2: "-.-.j = j"
                        using s5_1 minus_involutive by auto
                    show ?thesis
                        using s5_2 by auto
                    qed
                also have s4_7: "... = i * j + (-.i + Succ[-.j])"
                    proof -
                    have s5_1: "i * j \\in Int"
                        proof -
                        have s6_1: "i \\in Int"
                            using s2_3_idom neg_nat_in_int by auto
                        have s6_2: "j \\in Int"
                            using s1_3_jdom neg_nat_in_int by auto
                        show ?thesis
                            using s6_1 s6_2 multIsInt by auto
                        qed
                    have s5_2: "-.i \\in Int"
                        using s2_3_idom minus_negnat_in_int by auto
                    have s5_3: "Succ[-.j] \\in Int"
                        using s1_3_jdom negnat_succ_in_nat nat_in_int by auto
                    show ?thesis
                        using s5_1 s5_2 s5_3 AddAssociative_sequent by auto
                    qed
                also have s4_8: "... = i * j + (-.i + (-.j + 1))"
                    proof -
                    have s5_1: "Succ[-.j] = -.j + 1"
                        using s1_3_jdom SuccMinusIsPlusOne by fast
                    show ?thesis
                        using s5_1 by auto
                    qed
                also have s4_9: "... = i * j + ((-.i + -.j) + 1)"
                    proof -
                    have s5_1: "-.i \\in Int"
                        using s2_3_idom minus_negnat_in_int by auto
                    have s5_2: "-.j \\in Int"
                        using s1_3_jdom minus_negnat_in_int by auto
                    have s5_3: "1 \\in Int"
                        using oneIsNat nat_in_int by auto
                    have s5_4: "-.i + (-.j + 1) = (-.i + -.j) + 1"
                        using s5_1 s5_2 s5_3 AddAssociative_sequent by auto
                    show ?thesis
                        using s5_4 by auto
                    qed
                finally show ?thesis .
                qed
            show "-.Succ[-.i] * -.Succ[-.j] = -.Succ[-.j] * -.Succ[-.i]"
                using s3_1 s3_2 by auto
            qed
        have s2_4: "\<forall> i \<in> Nat:
                        i * -.Succ[-.j] = -.Succ[-.j] * i"
            using s2_1 s2_2 natInduct by auto
        have s2_5: "\<forall> i \<in> negNat:
                        i * -.Succ[-.j] = -.Succ[-.j] * i"
            using s2_1 s2_3 neg_nat_induction by auto
        show "\<forall> i \<in> Int:  i * -.Succ[-.j] = -.Succ[-.j] * i"
            using s2_4 s2_5 int_union_nat_negnat by auto
        qed
    have s1_4: "\<forall> j \<in> Nat:  \<forall> i \<in> Int:
        i * j = j * i"
        using s1_1 s1_2 natInduct by auto
    have s1_5: "\<forall> j \<in> negNat:  \<forall> i \<in> Int:
        i * j = j * i"
        using s1_1 s1_3 neg_nat_induction by auto
    show ?thesis
        using s1_4 s1_5 int_union_nat_negnat by auto
    qed


theorem MultCommutative_sequent:
    assumes idom: "i \\in Int" and jdom: "j \\in Int"
    shows "i * j = j * i"
    using idom jdom MultCommutative spec by auto


(*
THEOREM mult_0_left ==
    ASSUME m \in Int
    PROVE 0 * m = 0
    BY mult_0, MultCommutative
*)
theorem mult_0_left:
    assumes ndom: "n \\in Int"
    shows "0 * n = 0"
    proof -
    have s1_1: "n * 0 = 0"
        using ndom mult_0 by auto
    have s1_2: "n * 0 = 0 * n"
        using ndom zero_in_int MultCommutative_sequent by auto
    show ?thesis
        using s1_1 s1_2 by auto
    qed


(*----------------------------------------------------------------------------*)
(* Associativity of multiplication. *)


(*
THEOREM MultLeftDistributesAdd ==
    \A a, b, c \in Int:
        a * (b + c) = a * b + a * c
PROOF
<1>1. SUFFICES
        ASSUME NEW b \in Int, NEW c \in Int
        PROVE \A a \in Int:  a * (b + c) = a * b + a * c
    BY <1>1
<1>2. 0 * (b + c) = 0 * b + 0 * c
    <2>1. 0 * (b + c) = 0
        <3>1. b + c \in Int
            BY <1>1, addIsInt
        <3> QED
            BY <3>1, mult_0_left
    <2>2. 0 * b + 0 * c = 0
        <3>1. 0 * b = 0
            BY <1>1, mult_0_left
        <3>2. 0 * c = 0
            BY <1>1, mult_0_left
        <3> QED
            BY <3>1, <3>2, zero_in_int, add_0
    <2> QED
        BY <2>1, <2>2
<1>3. ASSUME NEW a \in Nat,
        a * (b + c) = a * b + a * c
      PROVE Succ[a] * (b + c) = Succ[a] * b + Succ[a] * c
    <2>1. Succ[a] * (b + c) = (b + c) * Succ[a]
        <3>1. Succ[a] \in Int
            BY <1>3, succIsNat, nat_in_int
        <3>2. b + c \in Int
            BY <1>1, addIsInt
        <3> QED
            BY <3>1, <3>2, MultCommutative
    <2>2. @ = (b + c) * a + (b + c)
        <3>1. b + c \in Int
            BY <1>1, addIsInt
        <3>2. a \in Nat
            BY <1>3
        <3> QED
            BY <3>1, <3>2, multint_succ_nat
    <2>3. @ = a * (b + c) + (b + c)
        <3>1. b + c \in Int
            BY <1>1, addIsInt
        <3>2. a \in Int
            BY <1>3, nat_in_int
        <3>3. (b + c) * a = a * (b + c)
            BY <3>1, <3>2, MultCommutative
        <3> QED
            BY <3>3
    <2>4. @ = (a * b + a * c) + (b + c)
        BY <1>3  \* induction hypothesis
    <2>5. @ = a * b + (a * c + (b + c))
        <3>1. a * b \in Int
            BY <1>1, <1>3, nat_in_int, multIsInt
        <3>2. a * c \in Int
            BY <1>1, <1>3, nat_in_int, multIsInt
        <3>3. b + c \in Int
            BY <1>1, addIsInt
        <3> QED
            BY <3>1, <3>2, <3>3, AddAssociative
    <2>6. @ = a * b + ((a * c + b) + c)
        <3>1. a * c \in Int
            BY <1>1, <1>3, nat_in_int, multIsInt
        <3>2. b \in Int
            BY <1>1
        <3>3. c \in Int
            BY <1>1
        <3>4. a * c + (b + c) = (a * c + b) + c
            BY <3>1, <3>2, <3>3, AddAssociative
        <3> QED
            BY <3>4
    <2>7. @ = a * b + ((b + a * c) + c)
        <3>1. a * c \in Int
            BY <1>1, <1>3, nat_in_int, multIsInt
        <3>2. b \in Int
            BY <1>1
        <3>3. a * c + b = b + a * c
            BY <3>1, <3>2, AddCommutative
        <3> QED
            BY <3>3
    <2>8. @ = a * b + (b + (a * c + c))
        <3>1. b \in Int
            BY <1>1
        <3>2. a * c \in Int
            BY <1>1, <1>3, nat_in_int, multIsInt
        <3>3. c \in Int
            BY <1>1
        <3>4. (b + a * c) + c = b + (a * c + c)
            BY <3>1, <3>2, <3>3, AddAssociative
        <3> QED
            BY <3>4
    <2>9. @ = (a * b + b) + (a * c + c)
        <3>1. a * b \in Int
            BY <1>1, <1>3, nat_in_int, multIsInt
        <3>2. b \in Int
            BY <1>1
        <3>3. (a * c + c) \in Int
            BY <1>1, <1>3, nat_in_int, addIsInt, multIsInt
        <3> QED
            BY <3>1, <3>2, <3>3, AddAssociative
    <2>10. @ = (b * a + b) + (c * a + c)
        <3>1. a * b = b * a
            <4>1. a \in Int
                BY <1>3, nat_in_int
            <4>2. b \in Int
                BY <1>1
            <4> QED
                BY <4>1, <4>2, MultCommutative
        <3>2. a * c = c * a
            <4>1. a \in Int
                BY <1>3, nat_in_int
            <4>2. c \in Int
                BY <1>1
            <4> QED
                BY <4>1, <4>2, MultCommutative
        <3> QED
            BY <3>1, <3>2
    <2>11. @ = b * Succ[a] + c * Succ[a]
        <3>1. b * Succ[a] = b * a + b
            <4>1. b \in Int
                BY <1>1
            <4>2. a \in Nat
                BY <1>3
            <4> QED
                BY <4>1, <4>2, multint_succ_nat
        <3>2. c * Succ[a] = c * a + c
            <4>1. c \in Int
                BY <1>1
            <4>2. a \in Nat
                BY <1>3
            <4> QED
                BY <4>1, <4>2, multint_succ_nat
        <3> QED
            BY <3>1, <3>2
    <2>12. @ = Succ[a] * b + Succ[a] * c
        <3>1. b * Succ[a] = Succ[a] * b
            <4>1. b \in Int
                BY <1>1
            <4>2. Succ[a] \in Int
                BY <1>3, succIsNat, nat_in_int
            <4> QED
                BY <4>1, <4>2, MultCommutative
        <3>2. c * Succ[a] = Succ[a] * c
            <4>1. c \in Int
                BY <1>1
            <4>2. Succ[a] \in Int
                BY <1>3, succIsNat, nat_in_int
            <4> QED
                BY <4>1, <4>2, MultCommutative
        <3> QED
            BY <3>1, <3>2
    <2> QED
        BY <2>1, <2>2, <2>3, <2>4,
            <2>5, <2>6, <2>7, <2>8, <2>9,
            <2>10, <2>11, <2>12
<1>4. ASSUME NEW a \in negNat,
        a * (b + c) = a * b + a * c
      PROVE -.Succ[-.a] * (b + c) = -.Succ[-.a] * b + -.Succ[-.a] * c
    <2>1. -.Succ[-.a] * (b + c) = (b + c) * -.Succ[-.a]
        <3>1. -.Succ[-.a] \in Int
            BY <1>4, minus_succ_minus_negnat_in_int
        <3>2. b + c \in Int
            BY <1>1, addIsInt
        <3> QED
            BY <3>1, <3>2, MultCommutative
    <2>2. @ = (b + c) * -.-.a + -.(b + c)
        <3>1. b + c \in Int
            BY <1>1, addIsInt
        <3>2. -.a \in Nat
            BY <1>4, minus_neg_nat_in_nat
        <3> QED
            BY <3>1, <3>2, multint_succ_negnat
    <2>3. @ = (b + c) * a + -.(b + c)
        <3>1. a \in Int
            BY <1>4, neg_nat_in_int
        <3>2. -.-.a = a
            BY <3>1, minus_involutive
        <3> QED
            BY <3>2
    <2>4. @ = a * (b + c) + -.(b + c)
        <3>1. a \in Int
            BY <1>4, neg_nat_in_int
        <3>2. b + c \in Int
            BY <1>1, addIsInt
        <3>3. (b + c) * a = a * (b + c)
            BY <3>1, <3>2, MultCommutative
        <3> QED
            BY <3>3
    <2>5. @ = (a * b + a * c) + -.(b + c)
        BY <1>4  \* induction hypothesis
    <2>6. @ = (a * b + a * c) + (-.b + -.c)
        <3>1. b \in Int
            BY <1>1
        <3>2. c \in Int
            BY <1>1
        <3>3. -.(b + c) = -.b + -.c
            BY <3>1, <3>2, MinusDistributesAdd, spec
        <3> QED
            BY <3>3
    <2>7. @ = a * b + (a * c + (-.b + -.c))
        <3>1. a * b \in Int
            <4>1. a \in Int
                BY <1>4, neg_nat_in_int
            <4>2. b \in Int
                BY <1>1
            <4> QED
                BY <4>1, <4>2, multIsInt
        <3>2. a * c \in Int
            <4>1. a \in Int
                BY <1>4, neg_nat_in_int
            <4>2. c \in Int
                BY <1>1
            <4> QED
                BY <4>1, <4>2, multIsInt
        <3>3. -.b + -.c \in Int
            <4>1. -.b \in Int
                BY <1>1, neg_int_eq_int
            <4>2. -.c \in Int
                BY <1>1, neg_int_eq_int
            <4> QED
                BY <4>1, <4>2, addIsInt
        <3> QED
            BY <3>1, <3>2, <3>3, AddAssociative
    <2>8. @ = a * b + ((a * c + -.b) + -.c)
        <3>1. a * c \in Int
            <4>1. a \in Int
                BY <1>4, neg_nat_in_int
            <4>2. c \in Int
                BY <1>1
            <4> QED
                BY <4>1, <4>2, multIsInt
        <3>2. -.b \in Int
            BY <1>1, neg_int_eq_int
        <3>3. -.c \in Int
            BY <1>1, neg_int_eq_int
        <3>4. a * c + (-.b + -.c) =
                (a * c + -.b) + -.c
            BY <3>1, <3>2, <3>3, AddAssociative
        <3> QED
            BY <3>4
    <2>9. @ = a * b + ((-.b + a * c) + -.c)
        <3>1. a * c \in Int
            <4>1. a \in Int
                BY <1>4, neg_nat_in_int
            <4>2. c \in Int
                BY <1>1
            <4> QED
                BY <4>1, <4>2, multIsInt
        <3>2. -.b \in Int
            BY <1>1, neg_int_eq_int
        <3>3. a * c + -.b = -.b + a * c
            BY <3>1, <3>2, AddCommutative
        <3> QED
            BY <3>3
    <2>10. @ = a * b + (-.b + (a * c + -.c))
        <3>1. -.b \in Int
            BY <1>1, neg_int_eq_int
        <3>2. a * c \in Int
            <4>1. a \in Int
                BY <1>4, neg_nat_in_int
            <4>2. c \in Int
                BY <1>1
            <4> QED
                BY <4>1, <4>2, multIsInt
        <3>3. -.c \in Int
            BY <1>1, neg_int_eq_int
        <3>4. (-.b + a * c) + -.c =
                -.b + (a * c + -.c)
            BY <3>1, <3>2, <3>3, AddAssociative
        <3> QED
            BY <3>4
    <2>11. @ = (a * b + -.b) + (a * c + -.c)
        <3>1. a * b \in Int
            <4>1. a \in Int
                BY <1>4, neg_nat_in_int
            <4>2. b \in Int
                BY <1>1
            <4> QED
                BY <4>1, <4>2, multIsInt
        <3>2. -.b \in Int
            BY <1>1, neg_int_eq_int
        <3>3. a * c + -.c \in Int
            <4>1. a * c \in Int
                <5>1. a \in Int
                    BY <1>4, neg_nat_in_int
                <5>2. c \in Int
                    BY <1>1
                <5> QED
                    BY <5>1, <5>2, multIsInt
            <4>2. -.c \in Int
                BY <1>1, neg_int_eq_int
            <4> QED
                BY <4>1, <4>2, addIsInt
        <3> QED
            BY <3>1, <3>2, <3>3, AddAssociative
    <2>12. @ = (b * a + -.b) + (c * a + -.c)
        <3>1. a * b = b * a
            <4>1. a \in Int
                BY <1>4, neg_nat_in_int
            <4>2. b \in Int
                BY <1>1
            <4> QED
                BY <4>1, <4>2, MultCommutative
        <3>2. a * c = c * a
            <4>1. a \in Int
                BY <1>4, neg_nat_in_int
            <4>2. c \in Int
                BY <1>1
            <4> QED
                BY <4>1, <4>2, MultCommutative
        <3> QED
            BY <3>1, <3>2
    <2>13. @ = (b * -.-.a + -.b) + (c * -.-.a + -.c)
        <3>1. a \in Int
            BY <1>4, neg_nat_in_int
        <3>2. -.-.a = a
            BY <3>1, minus_involutive
        <3> QED
            BY <3>2
    <2>14. @ = b * -.Succ[-.a] + c * -.Succ[-.a]
        <3>1. b * -.Succ[-.a] = b * -.-.a + -.b
            <4>1. b \in Int
                BY <1>1
            <4>2. -.a \in Nat
                BY <1>4, minus_neg_nat_in_nat
            <4> QED
                BY <4>1, <4>2, multint_succ_negnat
        <3>2. c * -.Succ[-.a] = c * -.-.a + -.c
            <4>1. c \in Int
                BY <1>1
            <4>2. -.a \in Nat
                BY <1>4, minus_neg_nat_in_nat
            <4> QED
                BY <4>1, <4>2, multint_succ_negnat
        <3> QED
            BY <3>1, <3>2
    <2>15. @ = -.Succ[-.a] * b + -.Succ[-.a] * c
        <3>1. -.Succ[-.a] \in Int
            BY <1>4, minus_succ_minus_negnat_in_int
        <3>2. b * -.Succ[-.a] = -.Succ[-.a] * b
            <4>1. b \in Int
                BY <1>1
            <4> QED
                BY <3>1, <4>1, MultCommutative
        <3>3. c * -.Succ[-.a] = -.Succ[-.a] * c
            <4>1. c \in Int
                BY <1>1
            <4> QED
                BY <3>1, <4>1, MultCommutative
        <3> QED
            BY <3>2, <3>3
    <2> QED
        BY <2>1, <2>2, <2>3, <2>4, <2>5, 2<6>,
            <2>7, <2>8, <2>9, <2>10, <2>11,
            <2>12, <2>13, <2>14, <2>15
<1>5. \A a \in Nat:  a * (b + c) = a * b + a * c
    BY <1>2, <1>3, NatInduction
<1>6. \A a \in negNat:  a * (b + c) = a * b + a * c
    BY <1>2, <1>4, neg_nat_induction
<1> QED
    BY <1>5, <1>6, int_union_nat_negnat
*)
theorem MultLeftDistributesAdd_forall:
    "\<forall> a \<in> Int:
     \<forall> b \<in> Int:
     \<forall> c \<in> Int:
        a * (b + c) = a * b + a * c"
    proof -
    {
    fix "b" :: "c"
    fix "c" :: "c"
    assume bdom: "b \\in Int"
    assume cdom: "c \\in Int"
    have s1_2: "0 * (b + c) = 0 * b + 0 * c"
        proof -
        have s2_1: "0 * (b + c) = 0"
            proof -
            have s3_1: "b + c \\in Int"
                using bdom cdom addIsInt by auto
            show ?thesis
                using s3_1 mult_0_left by auto
            qed
        have s2_2: "0 * b + 0 * c = 0"
            proof -
            have s3_1: "0 * b = 0"
                using bdom mult_0_left by auto
            have s3_2: "0 * c = 0"
                using cdom mult_0_left by auto
            show ?thesis
                using s3_1 s3_2 zero_in_int add_0 by auto
            qed
        show ?thesis
            using s2_1 s2_2 by auto
        qed
    have s1_3: "\<And> a.  \<lbrakk>
            a \\in Nat;
            a * (b + c) = a * b + a * c
        \<rbrakk> \<Longrightarrow>
            Succ[a] * (b + c) = Succ[a] * b + Succ[a] * c"
        proof -
        fix "a" :: "c"
        assume s1_3_adom: "a \\in Nat"
        assume s1_3_induct: "a * (b + c) = a * b + a * c"
        have s2_1: "Succ[a] * (b + c) = (b + c) * Succ[a]"
            proof -
            have s3_1: "Succ[a] \\in Int"
                using s1_3_adom succIsNat nat_in_int by auto
            have s3_2: "b + c \\in Int"
                using bdom cdom addIsInt by auto
            show ?thesis
                using s3_1 s3_2 MultCommutative_sequent by auto
            qed
        also have s2_2: "... = (b + c) * a + (b + c)"
            proof -
            have s3_1: "b + c \\in Int"
                using bdom cdom addIsInt by auto
            have s3_2: "a \\in Nat"
                using s1_3_adom by auto
            show ?thesis
                using s3_1 s3_2 multint_succ_nat by auto
            qed
        also have s2_3: "... = a * (b + c) + (b + c)"
            proof -
            have s3_1: "b + c \\in Int"
                using bdom cdom addIsInt by auto
            have s3_2: "a \\in Int"
                using s1_3_adom nat_in_int by auto
            have s3_3: "(b + c) * a = a * (b + c)"
                using s3_1 s3_2 MultCommutative_sequent by auto
            show ?thesis
                using s3_3 by auto
            qed
        also have s2_4: "... = (a * b + a * c) + (b + c)"
            using s1_3_induct by auto
        also have s2_5: "... = a * b + (a * c + (b + c))"
            proof -
            have s3_1: "a * b \\in Int"
                using bdom s1_3_adom nat_in_int multIsInt by auto
            have s3_2: "a * c \\in Int"
                using cdom s1_3_adom nat_in_int multIsInt by auto
            have s3_3: "b + c \\in Int"
                using bdom cdom addIsInt by auto
            show ?thesis
                using s3_1 s3_2 s3_3 AddAssociative_sequent by auto
            qed
        also have s2_6: "... = a * b + ((a * c + b) + c)"
            proof -
            have s3_1: "a * c \\in Int"
                using cdom s1_3_adom nat_in_int multIsInt by auto
            have s3_2: "b \\in Int"
                using bdom by auto
            have s3_3: "c \\in Int"
                using cdom by auto
            have s3_4: "a * c + (b + c) = (a * c + b) + c"
                using s3_1 s3_2 s3_3 AddAssociative_sequent by auto
            show ?thesis
                using s3_4 by auto
            qed
        also have s2_7: "... = a * b + ((b + a * c) + c)"
            proof -
            have s3_1: "a * c \\in Int"
                using cdom s1_3_adom nat_in_int multIsInt by auto
            have s3_2: "b \\in Int"
                using bdom by auto
            have s3_3: "a * c + b = b + a * c"
                using s3_1 s3_2 AddCommutative_sequent by auto
            show ?thesis
                using s3_3 by auto
            qed
        also have s2_8: "... = a * b + (b + (a * c + c))"
            proof -
            have s3_1: "b \\in Int"
                using bdom by auto
            have s3_2: "a * c \\in Int"
                using cdom s1_3_adom nat_in_int multIsInt by auto
            have s3_3: "c \\in Int"
                using cdom by auto
            have s3_4: "(b + a * c) + c = b + (a * c + c)"
                using s3_1 s3_2 s3_3 AddAssociative_sequent by auto
            show ?thesis
                using s3_4 by auto
            qed
        also have s2_9: "... = (a * b + b) + (a * c + c)"
            proof -
            have s3_1: "a * b \\in Int"
                using bdom s1_3_adom nat_in_int multIsInt by auto
            have s3_2: "b \\in Int"
                using bdom by auto
            have s3_3: "a * c + c \\in Int"
                using cdom s1_3_adom nat_in_int addIsInt multIsInt by auto
            show ?thesis
                using s3_1 s3_2 s3_3 AddAssociative_sequent by auto
            qed
        also have s2_10: "... = (b * a + b) + (c * a + c)"
            proof -
            have s3_1: "a * b = b * a"
                proof -
                have s4_1: "a \\in Int"
                    using s1_3_adom nat_in_int by auto
                have s4_2: "b \\in Int"
                    using bdom by auto
                show ?thesis
                    using s4_1 s4_2 MultCommutative_sequent by auto
                qed
            have s3_2: "a * c = c * a"
                proof -
                have s4_1: "a \\in Int"
                    using s1_3_adom nat_in_int by auto
                have s4_2: "c \\in Int"
                    using cdom by auto
                show ?thesis
                    using s4_1 s4_2 MultCommutative_sequent by auto
                qed
            show ?thesis
                using s3_1 s3_2 by auto
            qed
        also have s2_11: "... = b * Succ[a] + c * Succ[a]"
            proof -
            have s3_1: "b * Succ[a] = b * a + b"
                proof -
                have s4_1: "b \\in Int"
                    using bdom by auto
                have s4_2: "a \\in Nat"
                    using s1_3_adom by auto
                show ?thesis
                    using s4_1 s4_2 multint_succ_nat by auto
                qed
            have s3_2: "c * Succ[a] = c * a + c"
                proof -
                have s4_1: "c \\in Int"
                    using cdom by auto
                have s4_2: "a \\in Nat"
                    using s1_3_adom by auto
                show ?thesis
                    using s4_1 s4_2 multint_succ_nat by auto
                qed
            show ?thesis
                using s3_1 s3_2 by auto
            qed
        also have s2_12: "... = Succ[a] * b + Succ[a] * c"
            proof -
            have s3_1: "b * Succ[a] = Succ[a] * b"
                proof -
                have s4_1: "b \\in Int"
                    using bdom by auto
                have s4_2: "Succ[a] \\in Int"
                    using s1_3_adom succIsNat nat_in_int by auto
                show ?thesis
                    using s4_1 s4_2 MultCommutative by auto
                qed
            have s3_2: "c * Succ[a] = Succ[a] * c"
                proof -
                have s4_1: "c \\in Int"
                    using cdom by auto
                have s4_2: "Succ[a] \\in Int"
                    using s1_3_adom succIsNat nat_in_int by auto
                show ?thesis
                    using s4_1 s4_2 MultCommutative by auto
                qed
            show ?thesis
                using s3_1 s3_2 by auto
            qed
        finally show "Succ[a] * (b + c) = Succ[a] * b + Succ[a] * c" .
        qed
    have s1_4: "\<And> a.  \<lbrakk>
            a \\in negNat;
            a * (b + c) = a * b + a * c
        \<rbrakk> \<Longrightarrow>
            -.Succ[-.a] * (b + c) =
            -.Succ[-.a] * b + -.Succ[-.a] * c"
        proof -
        fix "a" :: "c"
        assume s1_4_adom: "a \\in negNat"
        assume s1_4_induct: "a * (b + c) = a * b + a * c"
        have s2_1: "-.Succ[-.a] * (b + c) = (b + c) * -.Succ[-.a]"
            proof -
            have s3_1: "-.Succ[-.a] \\in Int"
                using s1_4_adom minus_succ_minus_negnat_in_int by auto
            have s3_2: "b + c \\in Int"
                using bdom cdom addIsInt by auto
            show ?thesis
                using s3_1 s3_2 MultCommutative by auto
            qed
        also have s2_2: "... = (b + c) * -.-.a + -.(b + c)"
            proof -
            have s3_1: "b + c \\in Int"
                using bdom cdom addIsInt by auto
            have s3_2: "-.a \\in Nat"
                using s1_4_adom minus_neg_nat_in_nat by auto
            show ?thesis
                using s3_1 s3_2 multint_succ_negnat by auto
            qed
        also have s2_3: "... = (b + c) * a + -.(b + c)"
            proof -
            have s3_1: "a \\in Int"
                using s1_4_adom neg_nat_in_int by auto
            have s3_2: "-.-.a = a"
                using s3_1 minus_involutive by auto
            show ?thesis
                using s3_2 by auto
            qed
        also have s2_4: "... = a * (b + c) + -.(b + c)"
            proof -
            have s3_1: "a \\in Int"
                using s1_4_adom neg_nat_in_int by auto
            have s3_2: "b + c \\in Int"
                using bdom cdom addIsInt by auto
            have s3_3: "(b + c) * a = a * (b + c)"
                using s3_1 s3_2 MultCommutative_sequent by auto
            show ?thesis
                using s3_3 by auto
            qed
        also have s2_5: "... = (a * b + a * c) + -.(b + c)"
            using s1_4_induct by auto
        also have s2_6: "... = (a * b + a * c) + (-.b + -.c)"
            proof -
            have s3_1: "b \\in Int"
                using bdom by auto
            have s3_2: "c \\in Int"
                using cdom by auto
            have s3_3: "-.(b + c) = -.b + -.c"
                using s3_1 s3_2 MinusDistributesAdd spec by auto
            show ?thesis
                using s3_3 by auto
            qed
        also have s2_7: "... = a * b + (a * c + (-.b + -.c))"
            proof -
            have s3_1: "a * b \\in Int"
                proof -
                have s4_1: "a \\in Int"
                    using s1_4_adom neg_nat_in_int by auto
                have s4_2: "b \\in Int"
                    using bdom by auto
                show ?thesis
                    using s4_1 s4_2 multIsInt by auto
                qed
            have s3_2: "a * c \\in Int"
                proof -
                have s4_1: "a \\in Int"
                    using s1_4_adom neg_nat_in_int by auto
                have s4_2: "c \\in Int"
                    using cdom by auto
                show ?thesis
                    using s4_1 s4_2 multIsInt by auto
                qed
            have s3_3: "-.b + -.c \\in Int"
                proof -
                have s4_1: "-.b \\in Int"
                    using bdom neg_int_eq_int by auto
                have s4_2: "-.c \\in Int"
                    using cdom neg_int_eq_int by auto
                show ?thesis
                    using s4_1 s4_2 addIsInt by auto
                qed
            show ?thesis
                using s3_1 s3_2 s3_3 AddAssociative_sequent by auto
            qed
        also have s2_8: "... = a * b + ((a * c + -.b) + -.c)"
            proof -
            have s3_1: "a * c \\in Int"
                proof -
                have s4_1: "a \\in Int"
                    using s1_4_adom neg_nat_in_int by auto
                have s4_2: "c \\in Int"
                    using cdom by auto
                show ?thesis
                    using s4_1 s4_2 multIsInt by auto
                qed
            have s3_2: "-.b \\in Int"
                using bdom neg_int_eq_int by auto
            have s3_3: "-.c \\in Int"
                using cdom neg_int_eq_int by auto
            have s3_4: "a * c + (-.b + -.c) =
                        (a * c + -.b) + -.c"
                using s3_1 s3_2 s3_3 AddAssociative_sequent by auto
            show ?thesis
                using s3_4 by auto
            qed
        also have s2_9: "... = a * b + ((-.b + a * c) + -.c)"
            proof -
            have s3_1: "a * c \\in Int"
                proof -
                have s4_1: "a \\in Int"
                    using s1_4_adom neg_nat_in_int by auto
                have s4_2: "c \\in Int"
                    using cdom by auto
                show ?thesis
                    using s4_1 s4_2 multIsInt by auto
                qed
            have s3_2: "-.b \\in Int"
                using bdom neg_int_eq_int by auto
            have s3_3: "a * c + -.b = -.b + a * c"
                using s3_1 s3_2 AddCommutative_sequent by auto
            show ?thesis
                using s3_3 by auto
            qed
        also have s2_10: "... = a * b + (-.b + (a * c + -.c))"
            proof -
            have s3_1: "-.b \\in Int"
                using bdom neg_int_eq_int by auto
            have s3_2: "a * c \\in Int"
                proof -
                have s4_1: "a \\in Int"
                    using s1_4_adom neg_nat_in_int by auto
                have s4_2: "c \\in Int"
                    using cdom by auto
                show ?thesis
                    using s4_1 s4_2 multIsInt by auto
                qed
            have s3_3: "-.c \\in Int"
                using cdom neg_int_eq_int by auto
            have s3_4: "(-.b + a * c) + -.c =
                        -.b + (a * c + -.c)"
                using s3_1 s3_2 s3_3 AddAssociative_sequent by auto
            show ?thesis
                using s3_4 by auto
            qed
        also have s2_11: "... = (a * b + -.b) + (a * c + -.c)"
            proof -
            have s3_1: "a * b \\in Int"
                proof -
                have s4_1: "a \\in Int"
                    using s1_4_adom neg_nat_in_int by auto
                have s4_2: "b \\in Int"
                    using bdom by auto
                show ?thesis
                    using s4_1 s4_2 multIsInt by auto
                qed
            have s3_2: "-.b \\in Int"
                using bdom neg_int_eq_int by auto
            have s3_3: "a * c + -.c \\in Int"
                proof -
                have s4_1: "a * c \\in Int"
                    proof -
                    have s5_1: "a \\in Int"
                        using s1_4_adom neg_nat_in_int by auto
                    have s5_2: "c \\in Int"
                        using cdom by auto
                    show ?thesis
                        using s5_1 s5_2 multIsInt by auto
                    qed
                have s4_2: "-.c \\in Int"
                    using cdom neg_int_eq_int by auto
                show ?thesis
                    using s4_1 s4_2 addIsInt by auto
                qed
            show ?thesis
                using s3_1 s3_2 s3_3 AddAssociative_sequent by auto
            qed
        also have s2_12: "... = (b * a + -.b) + (c * a + -.c)"
            proof -
            have s3_1: "a * b = b * a"
                proof -
                have s4_1: "a \\in Int"
                    using s1_4_adom neg_nat_in_int by auto
                have s4_2: "b \\in Int"
                    using bdom by auto
                show ?thesis
                    using s4_1 s4_2 MultCommutative_sequent by auto
                qed
            have s3_2: "a * c = c * a"
                proof -
                have s4_1: "a \\in Int"
                    using s1_4_adom neg_nat_in_int by auto
                have s4_2: "c \\in Int"
                    using cdom by auto
                show ?thesis
                    using s4_1 s4_2 MultCommutative_sequent by auto
                qed
            show ?thesis
                using s3_1 s3_2 by auto
            qed
        also have s2_13: "... = (b * -.-.a + -.b) + (c * -.-.a + -.c)"
            proof -
            have s3_1: "a \\in Int"
                using s1_4_adom neg_nat_in_int by auto
            have s3_2: "-.-.a = a"
                using s3_1 minus_involutive by auto
            show ?thesis
                using s3_2 by auto
            qed
        also have s2_14: "... = b * -.Succ[-.a] + c * -.Succ[-.a]"
            proof -
            have s3_1: "b * -.Succ[-.a] = b * -.-.a + -.b"
                proof -
                have s4_1: "b \\in Int"
                    using bdom by auto
                have s4_2: "-.a \\in Nat"
                    using s1_4_adom minus_neg_nat_in_nat by auto
                show ?thesis
                    using s4_1 s4_2 multint_succ_negnat by auto
                qed
            have s3_2: "c * -.Succ[-.a] = c * -.-.a + -.c"
                proof -
                have s4_1: "c \\in Int"
                    using cdom by auto
                have s4_2: "-.a \\in Nat"
                    using s1_4_adom minus_neg_nat_in_nat by auto
                show ?thesis
                    using s4_1 s4_2 multint_succ_negnat by auto
                qed
            show ?thesis
                using s3_1 s3_2 by auto
            qed
        also have s2_15: "... = -.Succ[-.a] * b + -.Succ[-.a] * c"
            proof -
            have s3_1: "-.Succ[-.a] \\in Int"
                using s1_4_adom minus_succ_minus_negnat_in_int by auto
            have s3_2: "b * -.Succ[-.a] = -.Succ[-.a] * b"
                proof -
                have s4_1: "b \\in Int"
                    using bdom by auto
                show ?thesis
                    using s3_1 s4_1 MultCommutative_sequent by auto
                qed
            have s3_3: "c * -.Succ[-.a] = -.Succ[-.a] * c"
                proof -
                have s4_1: "c \\in Int"
                    using cdom by auto
                show ?thesis
                    using s3_1 s4_1 MultCommutative_sequent by auto
                qed
            show ?thesis
                using s3_2 s3_3 by auto
            qed
        finally show "-.Succ[-.a] * (b + c) =
                      -.Succ[-.a] * b + -.Succ[-.a] * c" .
        qed
    have s1_5: "\<forall> a \<in> Nat:
                    a * (b + c) = a * b + a * c"
        using s1_2 s1_3 natInduct by auto
    have s1_6: "\<forall> a \<in> negNat:
                    a * (b + c) = a * b + a * c"
        using s1_2 s1_4 neg_nat_induction by auto
    have s1_7: "\<forall> a \<in> Int:
                    a * (b + c) = a * b + a * c"
        using s1_5 s1_6 int_union_nat_negnat by auto
    }
    from this show ?thesis
        by auto
    qed


theorem MultLeftDistributesAdd:
    assumes adom: "a \\in Int" and bdom: "b \\in Int" and
        cdom: "c \\in Int"
    shows "a * (b + c) = a * b + a * c"
    using adom bdom cdom MultLeftDistributesAdd_forall by auto


theorem MultRightDistributesAdd:
    assumes adom: "a \\in Int" and bdom: "b \\in Int" and
        cdom: "c \\in Int"
    shows "(b + c) * a = b * a + c * a"
    proof -
    have s1_1: "a * (b + c) = a * b + a * c"
        using adom bdom cdom MultLeftDistributesAdd by auto
    have s1_2: "a * (b + c) = (b + c) * a"
        using adom bdom cdom addIsInt MultCommutative by auto
    have s1_3: "a * b = b * a"
        using adom bdom MultCommutative by auto
    have s1_4: "a * c = c * a"
        using adom cdom MultCommutative by auto
    show ?thesis
        using s1_1 s1_2 s1_3 s1_4 by auto
    qed


theorems mult_distributes[algebra_simps] =
    MultLeftDistributesAdd MultRightDistributesAdd


(*
THEOREM MinusCommutesRightMult ==
    \A a, b \in Int:  -.(a * b) = a * -.b
PROOF
<1>1. SUFFICES
        ASSUME NEW a \in Int
        PROVE \A b \in Int:  -.(a * b) = a * -.b
    BY <1>1
<1>2. -.(a * 0) = a * -.0
    <2>1. -.(a * 0) = 0
        BY <1>1, mult_0, neg0
    <2>2. a * -.0 = 0
        BY <1>1, neg0, mult_0
    <2> QED
        BY <2>1, <2>2
<1>3. ASSUME NEW b \in Nat,
            -.(a * b) = a * -.b
      PROVE -.(a * Succ[b]) = a * -.Succ[b]
    <2>1. -.(a * Succ[b]) = -.(a * b + a)
        <3>1. a \in Int
            BY <1>1
        <3>2. b \in Nat
            BY <1>3
        <3> QED
            BY <3>1, <3>2, multint_succ_nat
    <2>2. @ = -.(a * b) + -.a
        <3>1. a * b \in Int
            BY <1>1, <1>3, nat_in_int, multIsInt
        <3>2. a \in Int
            BY <1>1
        <3> QED
            BY <3>1, <3>2, MinusDistributesAdd
    <2>3. @ = a * -.b + -.a
        BY <1>3  \* induction hypothesis
    <2>4. @ = a * -.Succ[b]
        <3>1. a \in Int
            BY <1>1
        <3>2. b \in Nat
            BY <1>3
        <3> QED
            BY <3>1, <3>2, multint_succ_negnat
    <2> QED
        BY <2>1, <2>2, <2>3, <2>4
<1>4. ASSUME NEW b \in negNat,
            -.(a * b) = a * -.b
      PROVE -.(a * -.Succ[-.b]) = a * -.-.Succ[-.b]
    <2>1. -.(a * -.Succ[-.b]) = -.(a * -.-.b + -.a)
        <3>1. a \in Int
            BY <1>1
        <3>2. -.b \in Nat
            BY <1>4, minus_neg_nat_in_nat
        <3> QED
            BY <3>1, <3>2, multint_succ_negnat
    <2>2. @ = -.(a * -.-.b) + -.-.a
        <3>1. a * -.-.b \in Int
            <4>1. a \in Int
                BY <1>1
            <4>2. -.-.b \in Int
                BY <1>4, minus_negnat_in_int,
                    neg_int_eq_int
            <4> QED
                BY <4>1, <4>2, multIsInt
        <3>2. -.a \in Int
            BY <1>1, neg_int_eq_int
        <3> QED
            BY <3>1, <3>2, MinusDistributesAdd
    <2>3. @ = -.(a * -.-.b) + a
        <3>1. a \in Int
            BY <1>1
        <3>2. -.-.a = a
            BY <3>1, minus_involutive
        <3> QED
            BY <3>2
    <2>4. @ = -.(a * b) + a
        <3>1. b \in Int
            BY <1>4, neg_nat_in_int
        <3>2. -.-.b = b
            BY <3>1, minus_involutive
        <3> QED
            BY <3>2
    <2>5. @ = a * -.b + a
        BY <1>4  \* induction hypothesis
    <2>6. @ = a * Succ[-.b]
        <3>1. a \in Int
            BY <1>1
        <3>2. -.b \in Nat
            BY <1>4, minus_neg_nat_in_nat
        <3> QED
            BY <3>1, <3>2, multint_succ_nat
    <2>7. @ = a * -.-.Succ[-.b]
        <3>1. Succ[-.b] \in Int
            BY <1>4, negnat_succ_in_nat, nat_in_int
        <3>2. -.-.Succ[-.b] = Succ[-.b]
            BY <3>1, minus_involutive
        <3> QED
            BY <3>2
    <2> QED
        BY <2>1, <2>2, <2>3, ,2>4,
            <2>5, <2>6, <2>7
<1>5. \A b \in Nat:  -.(a * b) = a * -.b
    BY <1>2, <1>3, NatInduction
<1>6. \A b \in negNat:  -.(a * b) = a * -.b
    BY <1>2, <1>4, neg_nat_induction
<1> QED
    BY <1>5, <1>6, int_union_nat_negnat
*)
theorem MinusCommutesRightMult:
    "\<forall> a \<in> Int:  \<forall> b \<in> Int:
        -.(a * b) = a * -.b"
    proof -
    {
    fix "a" :: "c"
    assume adom: "a \\in Int"
    have s1_2: "-.(a * 0) = a * -.0"
        proof -
        have s2_1: "-.(a * 0) = 0"
            using adom mult_0 neg0 by auto
        have s2_2: "a * -.0 = 0"
            using adom neg0 mult_0 by auto
        show ?thesis
            using s2_1 s2_2 by auto
        qed
    have s1_3: "\<And> b.  \<lbrakk>
            b \\in Nat;
            -.(a * b) = a * -.b
        \<rbrakk> \<Longrightarrow>
            -.(a * Succ[b]) = a * -.Succ[b]"
        proof -
        fix "b" :: "c"
        assume s1_3_bdom: "b \\in Nat"
        assume s1_3_induct: "-.(a * b) = a * -.b"
        have s2_1: "-.(a * Succ[b]) = -.(a * b + a)"
            proof -
            have s3_1: "a \\in Int"
                using adom by auto
            have s3_2: "b \\in Nat"
                using s1_3_bdom by auto
            show ?thesis
                using s3_1 s3_2 multint_succ_nat by auto
            qed
        also have s2_2: "... = -.(a * b) + -.a"
            proof -
            have s3_1: "a * b \\in Int"
                using adom s1_3_bdom nat_in_int multIsInt by auto
            have s3_2: "a \\in Int"
                using adom by auto
            show ?thesis
                using s3_1 s3_2 MinusDistributesAdd by auto
            qed
        also have s2_3: "... = a * -.b + -.a"
            using s1_3_induct by auto
        also have s2_4: "... = a * -.Succ[b]"
            proof -
            have s3_1: "a \\in Int"
                using adom by auto
            have s3_2: "b \\in Nat"
                using s1_3_bdom by auto
            show ?thesis
                using s3_1 s3_2 multint_succ_negnat by auto
            qed
        finally show "-.(a * Succ[b]) = a * -.Succ[b]" .
        qed
    have s1_4: "\<And> b.  \<lbrakk>
            b \\in negNat;
            -.(a * b) = a * -.b
        \<rbrakk> \<Longrightarrow>
            -.(a * -.Succ[-.b]) = a * -.-.Succ[-.b]"
        proof -
        fix "b" :: "c"
        assume s1_4_bdom: "b \\in negNat"
        assume s1_4_induct: "-.(a * b) = a * -.b"
        have s2_1: "-.(a * -.Succ[-.b]) = -.(a * -.-.b + -.a)"
            proof -
            have s3_1: "a \\in Int"
                using adom by auto
            have s3_2: "-.b \\in Nat"
                using s1_4_bdom minus_neg_nat_in_nat by auto
            show ?thesis
                using s3_1 s3_2 multint_succ_negnat by auto
            qed
        also have s2_2: "... = -.(a * -.-.b) + -.-.a"
            proof -
            have s3_1: "a * -.-.b \\in Int"
                proof -
                have s4_1: "a \\in Int"
                    using adom by auto
                have s4_2: "-.-.b \\in Int"
                    using s1_4_bdom minus_negnat_in_int
                        neg_int_eq_int by auto
                show ?thesis
                    using s4_1 s4_2 multIsInt by auto
                qed
            have s3_2: "-.a \\in Int"
                using adom neg_int_eq_int by auto
            show ?thesis
                using s3_1 s3_2 MinusDistributesAdd by auto
            qed
        also have s2_3: "... = -.(a * -.-.b) + a"
            proof -
            have s3_1: "a \\in Int"
                using adom by auto
            have s3_2: "-.-.a = a"
                using s3_1 minus_involutive by auto
            show ?thesis
                using s3_2 by auto
            qed
        also have s2_4: "... = -.(a * b) + a"
            proof -
            have s3_1: "b \\in Int"
                using s1_4_bdom neg_nat_in_int by auto
            have s3_2: "-.-.b = b"
                using s3_1 minus_involutive by auto
            show ?thesis
                using s3_2 by auto
            qed
        also have s2_5: "... = a * -.b + a"
            using s1_4_induct by auto
        also have s2_6: "... = a * Succ[-.b]"
            proof -
            have s3_1: "a \\in Int"
                using adom by auto
            have s3_2: "-.b \\in Nat"
                using s1_4_bdom minus_neg_nat_in_nat by auto
            show ?thesis
                using s3_1 s3_2 multint_succ_nat by auto
            qed
        also have s2_7: "... = a * -.-.Succ[-.b]"
            proof -
            have s3_1: "Succ[-.b] \\in Int"
                using s1_4_bdom negnat_succ_in_nat nat_in_int by auto
            have s3_2: "-.-.Succ[-.b] = Succ[-.b]"
                using s3_1 minus_involutive by auto
            show ?thesis
                using s3_2 by auto
            qed
        finally show "-.(a * -.Succ[-.b]) = a * -.-.Succ[-.b]" .
        qed
    have s1_5: "\<forall> b \<in> Nat:
                    -.(a * b) = a * -.b"
        using s1_2 s1_3 natInduct by auto
    have s1_6: "\<forall> b \<in> negNat:
                    -.(a * b) = a * -.b"
        using s1_2 s1_4 neg_nat_induction by auto
    have s1_7: "\<forall> b \<in> Int:
                    -.(a * b) = a * -.b"
        using s1_5 s1_6 int_union_nat_negnat by auto
    }
    from this show ?thesis
        by auto
    qed


(*
THEOREM MinusCommutesLeftMult ==
    \A a, b \in Int:  -.(a * b) = -.a * b
PROOF
<1>1. SUFFICES
        ASSUME NEW a \in Int, NEW b \in Int
        PROVE -.(a * b) = -.a * b
    BY <1>1
<1>2. -.(a * b) = -.(b * a)
    BY <1>1, MultCommutative
<1>3. @ = b * -.a
    BY <1>1, MinusCommutesRightMult
<1>4. @ = -.a * b
    BY <1>1, neg_int_eq_int, MultCommutative
<1> QED
    BY <1>2, <1>3, <1>4
*)
theorem MinusCommutesLeftMult:
    "\<forall> a \<in> Int:  \<forall> b \<in> Int:
        -.(a * b) = -.a * b"
    proof -
    {
    fix "a" :: "c"
    fix "b" :: "c"
    assume adom: "a \\in Int"
    assume bdom: "b \\in Int"
    have s1_2: "-.(a * b) = -.(b * a)"
        using adom bdom MultCommutative_sequent by auto
    also have s1_3: "... = b * -.a"
        using adom bdom MinusCommutesRightMult by auto
    also have s1_4: "... = -.a * b"
        using adom bdom neg_int_eq_int
            MultCommutative_sequent by auto
    finally have "-.(a * b) = -.a * b"
        by auto
    }
    from this show ?thesis
        by auto
    qed


(*
THEOREM MultAssociative ==
    \A a \in Int:  \A b \in Int:  \A c \in Int:
        (a * b) * c = a * (b * c)
PROOF
<1>1. SUFFICES
        ASSUME NEW a \in Int, NEW b \in Int
        PROVE \A c \in Int:  (a * b) * c = a * (b * c)
    BY <1>1, allI
<1>2. (a * b) * 0 = a * (b * 0)
    <2>1. (a * b) * 0 = 0
        <3>1. a * b \in Int
            BY <1>1, multIsInt
        <3> QED
            BY <3>1, mult_0
    <2>2. a * (b * 0) = 0
        <3>1. b * 0 = 0
            BY <1>1, mult_0
        <3>2. a * 0 = 0
            BY <1>1, mult_0
        <3> QED
            BY <3>1, <3>2
    <2> QED
        BY <2>1, <2>2
<1>3. ASSUME NEW c \in Nat,
        (a * b) * c = a * (b * c)
      PROVE (a * b) * Succ[c] = a * (b * Succ[c])
    <2>1. (a * b) * Succ[c] = (a * b) * c + (a * b)
        <3>1. a * b \in Int
            BY <1>1, multIsInt
        <3>2. c \in Nat
            BY <1>3
        <3> QED
            BY <3>1, <3>2, multint_succ_nat
    <2>2. @ = a * (b * c) + (a * b)
        BY <1>3  \* induction hypothesis
    <2>3. @ = a * (b * c + b)
        <3>1. a \in Int
            BY <1>1
        <3>2. b * c \in Int
            BY <1>1, <1>3, nat_in_int, multIsInt
        <3>3. b \in Int
            BY <1>1
        <3> QED
            BY <3>1, <3>2, <3>3, MultLeftDistributesAdd
    <2>4. @ = a * (b * Succ[c])
        <3>1. b \in Int
            BY <1>1
        <3>2. c \in Nat
            BY <1>3
        <3>3. b * Succ[c] = b * c + b
            BY <3>1, <3>2, multint_succ_nat
        <3> QED
            BY <3>3
    <2> QED
        BY <2>1, <2>2, <2>3, <2>4
<1>4. ASSUME NEW c \in negNat,
        (a * b) * c = a * (b * c)
      PROVE (a * b) * -.Succ[-.c] = a * (b * -.Succ[-.c])
    <2>1. (a * b) * -.Succ[-.c] = (a * b) * -.-.c + -.(a * b)
        <3>1. a * b \in Int
            BY <1>1, multIsInt
        <3>2. -.c \in Nat
            BY <1>4, minus_neg_nat_in_nat
        <3> QED
            BY <3>1, <3>2, multint_succ_negnat
    <2>2. @ = (a * b) * c + -.(a * b)
        <3>1. c \in Int
            BY <1>4, neg_nat_in_int
        <3>2. -.-.c = c
            BY <3>1, minus_involutive
        <3> QED
            BY <3>2
    <2>3. @ = a * (b * c) + -.(a * b)
        BY <1>4  \* induction hypothesis
    <2>4. @ = a * (b * c) + a * -.b
        <3>1. a \in Int
            BY <1>1
        <3>2. b \in Int
            BY <1>1
        <3>3. -.(a * b) = a * -.b
            BY <3>1, <3>2, MinusCommutesRightMult
        <3> QED
            BY <3>3
    <2>5. @ = a * (b * c + -.b)
        <3>1. a \in Int
            BY <1>1
        <3>2. b * c \in Int
            BY <1>1 <1>4, neg_nat_in_int, multIsInt
        <3>3. -.b \in Int
            BY <1>1, neg_int_eq_int
        <3> QED
            BY <3>1, <3>2, <3>3, MultLeftDistributesAdd
    <2>6. @ = a * (b * -.-.c + -.b)
        <3>1. c \in Int
            BY <1>4, neg_nat_in_int
        <3>2. -.-.c = c
            BY <3>1, minus_involutive
        <3> QED
            BY <3>2
    <2>7. @ = a * (b * -.Succ[-.c])
        <3>1. b \in Int
            BY <1>1
        <3>2. -.c \in Nat
            BY <1>4, minus_neg_nat_in_nat
        <3>3. b * -.Succ[-.c] = b * -.-.c + -.b
            BY <3>1, <3>2, multint_succ_negnat
        <3> QED
            BY <3>3
    <2> QED
        BY <2>1, <2>2, <2>3, <2>4,
            <2>5, <2>6, <2>7
<1>5. \A c \in Nat:  (a * b) * c = a * (b * c)
    BY <1>2, <1>3, NatInduction
<1>6. \A c \in negNat:  (a * b) * c = a * (b * c)
    BY <1>2, <1>4, neg_nat_induction
<1> QED
    BY <1>5, <1>6, int_union_nat_negnat
*)
theorem MultAssociative:
    "\<forall> a \<in> Int:
     \<forall> b \<in> Int:
     \<forall> c \<in> Int:
        (a * b) * c = a * (b * c)"
    proof -
    {
    fix "a" :: "c"
    fix "b" :: "c"
    assume adom: "a \\in Int"
    assume bdom: "b \\in Int"
    have s1_2: "(a * b) * 0 = a * (b * 0)"
        proof -
        have s2_1: "(a * b) * 0 = 0"
            proof -
            have s3_1: "a * b \\in Int"
                using adom bdom multIsInt by auto
            show ?thesis
                using s3_1 mult_0 by auto
            qed
        have s2_2: "a * (b * 0) = 0"
            proof -
            have s3_1: "b * 0 = 0"
                using bdom mult_0 by auto
            have s3_2: "a * 0 = 0"
                using adom mult_0 by auto
            show ?thesis
                using s3_1 s3_2 by auto
            qed
        show ?thesis
            using s2_1 s2_2 by auto
        qed
    have s1_3: "\<And> c.  \<lbrakk>
            c \\in Nat;
            (a * b) * c = a * (b * c)
        \<rbrakk> \<Longrightarrow>
            (a * b) * Succ[c] = a * (b * Succ[c])"
        proof -
        fix "c" :: "c"
        assume s1_3_cdom: "c \\in Nat"
        assume s1_3_induct: "(a * b) * c = a * (b * c)"
        have s2_1: "(a * b) * Succ[c] = (a * b) * c + (a * b)"
            proof -
            have s3_1: "a * b \\in Int"
                using adom bdom multIsInt by auto
            have s3_2: "c \\in Nat"
                using s1_3_cdom by auto
            show ?thesis
                using s3_1 s3_2 multint_succ_nat by auto
            qed
        also have s2_2: "... = a * (b * c) + (a * b)"
            using s1_3_induct by auto
        also have s2_3: "... = a * (b * c + b)"
            proof -
            have s3_1: "a \\in Int"
                using adom by auto
            have s3_2: "b * c \\in Int"
                using bdom s1_3_cdom nat_in_int multIsInt by auto
            have s3_3: "b \\in Int"
                using bdom by auto
            show ?thesis
                using s3_1 s3_2 s3_3 MultLeftDistributesAdd[symmetric] by auto
            qed
        also have s2_4: "... = a * (b * Succ[c])"
            proof -
            have s3_1: "b \\in Int"
                using bdom by auto
            have s3_2: "c \\in Nat"
                using s1_3_cdom by auto
            have s3_3: "b * Succ[c] = b * c + b"
                using s3_1 s3_2 multint_succ_nat by auto
            show ?thesis
                using s3_3 by auto
            qed
        finally show "(a * b) * Succ[c] = a * (b * Succ[c])" .
        qed
    have s1_4: "\<And> c.  \<lbrakk>
            c \\in negNat;
            (a * b) * c = a * (b * c)
        \<rbrakk> \<Longrightarrow>
            (a * b) * -.Succ[-.c] = a * (b * -.Succ[-.c])"
        proof -
        fix "c" :: "c"
        assume s1_4_cdom: "c \\in negNat"
        assume s1_4_induct: "(a * b) * c = a * (b * c)"
        have s2_1: "(a * b) * -.Succ[-.c] = (a * b) * -.-.c + -.(a * b)"
            proof -
            have s3_1: "a * b \\in Int"
                using adom bdom multIsInt by auto
            have s3_2: "-.c \\in Nat"
                using s1_4_cdom minus_neg_nat_in_nat by auto
            show ?thesis
                using s3_1 s3_2 multint_succ_negnat by auto
            qed
        also have s2_2: "... = (a * b) * c + -.(a * b)"
            proof -
            have s3_1: "c \\in Int"
                using s1_4_cdom neg_nat_in_int by auto
            have s3_2: "-.-.c = c"
                using s3_1 minus_involutive by auto
            show ?thesis
                using s3_2 by auto
            qed
        also have s2_3: "... = a * (b * c) + -.(a * b)"
            using s1_4_induct by auto
        also have s2_4: "... = a * (b * c) + a * -.b"
            proof -
            have s3_1: "a \\in Int"
                using adom by auto
            have s3_2: "b \\in Int"
                using bdom by auto
            have s3_3: "-.(a * b) = a * -.b"
                using s3_1 s3_2 MinusCommutesRightMult by auto
            show ?thesis
                using s3_3 by auto
            qed
        also have s2_5: "... = a * (b * c + -.b)"
            proof -
            have s3_1: "a \\in Int"
                using adom by auto
            have s3_2: "b * c \\in Int"
                using bdom s1_4_cdom neg_nat_in_int multIsInt by auto
            have s3_3: "-.b \\in Int"
                using bdom neg_int_eq_int by auto
            show ?thesis
                using s3_1 s3_2 s3_3 MultLeftDistributesAdd[symmetric]
                by auto
            qed
        also have s2_6: "... = a * (b * -.-.c + -.b)"
            proof -
            have s3_1: "c \\in Int"
                using s1_4_cdom neg_nat_in_int by auto
            have s3_2: "-.-.c = c"
                using s3_1 minus_involutive by auto
            show ?thesis
                using s3_2 by auto
            qed
        also have s2_7: "... = a * (b * -.Succ[-.c])"
            proof -
            have s3_1: "b \\in Int"
                using bdom by auto
            have s3_2: "-.c \\in Nat"
                using s1_4_cdom minus_neg_nat_in_nat by auto
            have s3_3: "b * -.Succ[-.c] = b * -.-.c + -.b"
                using s3_1 s3_2 multint_succ_negnat by auto
            show ?thesis
                using s3_3 by auto
            qed
        finally show "(a * b) * -.Succ[-.c] = a * (b * -.Succ[-.c])" .
        qed
    have s1_5: "\<forall> c \<in> Nat:
                    (a * b) * c = a * (b * c)"
        using s1_2 s1_3 natInduct by auto
    have s1_6: "\<forall> c \<in> negNat:
                    (a * b) * c = a * (b * c)"
        using s1_2 s1_4 neg_nat_induction by auto
    have s1_7: "\<forall> c \<in> Int:
                    (a * b) * c = a * (b * c)"
        using s1_5 s1_6 int_union_nat_negnat by auto
    }
    from this show ?thesis
        by auto
    qed



(*----------------------------------------------------------------------------*)
(* Properties of `leq` and `add` and `diff`. *)


theorem LeqIsBool:
    "(m <= n) \\in BOOLEAN"
    unfolding leq_def by auto


theorem LeqReflexive:
    assumes ndom: "n \\in Int"
    shows "n <= n"
    proof -
    have s1_1: "n + 0 = n"
        using ndom add_0 by auto
    have s1_2: "0 \\in Nat"
        using zeroIsNat by auto
    have s1_3: "\<exists> r \<in> Nat:  n + r = n"
        using s1_1 s1_2 by auto
    show ?thesis
        unfolding leq_def
        using s1_3 by auto
    qed


theorem LeqTransitive:
    assumes mdom: "m \\in Int" and ndom: "n \\in Int" and
        kdom: "k \\in Int" and mn: "m <= n" and nk: "n <= k"
    shows "m <= k"
    proof -
    (* PICK r \in Nat:  m + r = n *)
    def P \<equiv> "\<lambda> x.  x \\in Nat \<and> m + x = n"
    def r \<equiv> "CHOOSE x:  P(x)"
    have s1_1: "r \\in Nat \<and> m + r = n"
        proof -
        have s2_1: "\\E x:  P(x)"
            using mn by (auto simp: leq_def P_def)
        have s2_2: "P(r)"
            unfolding r_def
            using s2_1 chooseI_ex[of P] by auto
        show ?thesis
            using s2_2 by (auto simp: P_def)
        qed
    (* PICK t \in Nat:  n + t = k *)
    def Q \<equiv> "\<lambda> x.  x \\in Nat \<and> n + x = k"
    def t \<equiv> "CHOOSE x:  Q(x)"
    have s1_2: "t \\in Nat \<and> n + t = k"
        proof -
        have s2_1: "\\E x:  Q(x)"
            using nk by (auto simp: leq_def Q_def)
        have s2_2: "Q(t)"
            unfolding t_def
            using s2_1 chooseI_ex[of Q] by auto
        show ?thesis
            using s2_2 by (auto simp: Q_def)
        qed
    have s1_3: "(m + r) + t = k"
        using s1_1 s1_2 by auto
    have s1_4: "m + (r + t) = k"
        proof -
        have s2_1: "m \\in Int"
            using mdom by auto
        have s2_2: "r \\in Int"
            using s1_1 nat_in_int by auto
        have s2_3: "t \\in Int"
            using s1_2 nat_in_int by auto
        have s2_4: "(m + r) + t = m + (r + t)"
            using s2_1 s2_2 s2_3 AddAssociative_sequent by auto
        show ?thesis
            using s1_3 s2_4 by auto
        qed
    have s1_5: "r + t \\in Nat"
        using s1_1 s1_2 nat_add_in_nat by auto
    have s1_6: "\<exists> q \<in> Nat:  m + q = k"
        using s1_4 s1_5 by auto
    show ?thesis
        unfolding leq_def
        using s1_6 by auto
    qed


theorem leq_0:
    assumes ndom: "n \\in Int"
    shows "(n \\in Nat) = (0 <= n)"
    proof -
    have s1_1: "n \\in Nat ==> 0 <= n"
        proof -
        assume s1_1_ndom: "n \\in Nat"
        have s2_1: "0 + n = n"
            using ndom add_0_left by auto
        have s2_2: "\<exists> r \<in> Nat:  0 + r = n"
            using s2_1 s1_1_ndom by auto
        show "0 <= n"
            unfolding leq_def
            using s2_2 by auto
        qed
    have s1_2: "0 <= n ==> n \\in Nat"
        proof -
        assume s1_2_leq: "0 <= n"
        def P \<equiv> "\<lambda> x.  x \\in Nat \<and> 0 + x = n"
        def r \<equiv> "CHOOSE x:  P(x)"
        have s2_1: "r \\in Nat \<and> 0 + r = n"
            proof -
            have s3_1: "\\E x:  P(x)"
                using s1_2_leq by (auto simp: leq_def P_def)
            have s3_2: "P(r)"
                unfolding r_def
                using s3_1 chooseI_ex[of P] by auto
            show ?thesis
                using s3_2 by (auto simp: P_def)
            qed
        have s2_2: "0 + r = r"
            proof -
            have s3_1: "r \\in Int"
                using s2_1 nat_in_int by auto
            show ?thesis
                using s3_1 add_0_left by auto
            qed
        have s2_3: "r = n"
            using s2_1 s2_2 by auto
        show "n \\in Nat"
            using s2_1 s2_3 by auto
        qed
    have s1_3: "(0 <= n) \\in BOOLEAN"
        using LeqIsBool by auto
    have s1_4: "(n \\in Nat) \\in BOOLEAN"
        using inIsBool isBoolTrueFalse by auto
    show ?thesis
        using s1_1 s1_2 s1_3 s1_4 by auto
    qed


theorem eq_leq_both:
    assumes mdom: "m \\in Int" and ndom: "n \\in Int" and
        mn: "m = n"
    shows "m <= n \<and> n <= m"
    proof -
    have s1_1: "m <= n"
        proof -
        have s2_1: "m + 0 = m"
            using mdom add_0 by auto
        have s2_2: "m + 0 = n"
            using s2_1 mn by auto
        have s2_3: "0 \\in Nat"
            using zeroIsNat by auto
        have s2_4: "\<exists> r \<in> Nat:  m + r = n"
            using s2_2 s2_3 by auto
        show ?thesis
            unfolding leq_def
            using s2_4 by auto
        qed
    have s1_2: "n <= m"
        proof -
        have s2_1: "n + 0 = n"
            using ndom add_0 by auto
        have s2_2: "n + 0 = m"
            using s2_1 mn by auto
        have s2_3: "0 \\in Nat"
            using zeroIsNat by auto
        have s2_4: "\<exists> r \<in> Nat:  n + r = m"
            using s2_2 s2_3 by auto
        show ?thesis
            unfolding leq_def
            using s2_4 by auto
        qed
    show ?thesis
        using s1_1 s1_2 by auto
    qed


(* The inverse of the theorem `eq_leq_both`. *)
theorem leq_both_eq:
    assumes mdom: "m \\in Int" and ndom: "n \\in Int" and
        mn: "m <= n" and nm: "n <= m"
    shows "m = n"
    proof -
    def P \<equiv> "\<lambda> x.  x \\in Nat \<and> m + x = n"
    def p \<equiv> "CHOOSE x:  P(x)"
    def Q \<equiv> "\<lambda> x.  x \\in Nat \<and> n + x = m"
    def q \<equiv> "CHOOSE x:  Q(x)"
    have s1_1: "p \\in Nat \<and> m + p = n"
        proof -
        have s2_1: "\<exists> x:  P(x)"
            using mn by (auto simp: leq_def P_def)
        have s2_2: "P(p)"
            unfolding p_def using s2_1 chooseI_ex[of P]
            by auto
        show ?thesis
            using s2_2 by (auto simp: P_def)
        qed
    have s1_2: "q \\in Nat \<and> n + q = m"
        proof -
        have s2_1: "\<exists> x:  Q(x)"
            using nm by (auto simp: leq_def Q_def)
        have s2_2: "Q(q)"
            unfolding q_def using s2_1 chooseI_ex[of Q]
            by auto
        show ?thesis
            using s2_2 by (auto simp: Q_def)
        qed
    have s1_3: "(m + p) + (n + q) = n + m"
        using s1_1 s1_2 by auto
    have s1_4: "p + q = 0"
        proof -
        have s2_1: "(m + p) + (n + q) = n + m"
            using s1_3 by auto
        have s2_2: "m + (p + (n + q)) = n + m"
            proof -
            have s3_1: "m \\in Int"
                using mdom by auto
            have s3_2: "p \\in Int"
                using s1_1 nat_in_int by auto
            have s3_3: "n + q \\in Int"
                using ndom s1_2 nat_in_int addIsInt by auto
            have s3_4: "(m + p) + (n + q) =
                    m + (p + (n + q))"
                using s3_1 s3_2 s3_3
                    AddAssociative_sequent by auto
            show ?thesis
                using s2_1 s3_4 by auto
            qed
        have s2_3: "m + (p + (q + n)) = n + m"
            proof -
            have s3_1: "n \\in Int"
                using ndom by auto
            have s3_2: "q \\in Int"
                using s1_2 nat_in_int by auto
            have s3_3: "n + q = q + n"
                using s3_1 s3_2 AddCommutative_sequent
                by auto
            show ?thesis
                using s2_2 s3_3 by auto
            qed
        have s2_4: "m + ((p + q) + n) = n + m"
            proof -
            have s3_1: "p \\in Int"
                using s1_1 nat_in_int by auto
            have s3_2: "q \\in Int"
                using s1_2 nat_in_int by auto
            have s3_3: "n \\in Int"
                using ndom by auto
            have s3_4: "p + (q + n) = (p + q) + n"
                using s3_1 s3_2 s3_3
                    AddAssociative_sequent by auto
            show ?thesis
                using s2_3 s3_4 by auto
            qed
        have s2_5: "m + (n + (p + q)) = n + m"
            proof -
            have s3_1: "p + q \\in Int"
                using s1_1 s1_2 nat_in_int addIsInt by auto
            have s3_2: "n \\in Int"
                using ndom by auto
            have s3_3: "(p + q) + n = n + (p + q)"
                using s3_1 s3_2
                    AddCommutative_sequent by auto
            show ?thesis
                using s2_4 s3_3 by auto
            qed
        have s2_6: "(m + n) + (p + q) = n + m"
            proof -
            have s3_1: "m \\in Int"
                using mdom by auto
            have s3_2: "n \\in Int"
                using ndom by auto
            have s3_3: "p + q \\in Int"
                using s1_1 s1_2 nat_in_int addIsInt by auto
            have s3_4: "m + (n + (p + q)) = (m + n) + (p + q)"
                using s3_1 s3_2 s3_3
                    AddAssociative_sequent by auto
            show ?thesis
                using s2_5 s3_4 by auto
            qed
        have s2_7: "-.(m + n) + ((m + n) + (p + q)) =
                    -.(m + n) + (n + m)"
            using s2_6 by auto
        have s2_8: "(-.(m + n) + (m + n)) + (p + q) =
                    -.(m + n) + (n + m)"
            proof -
            have s3_1: "m + n \\in Int"
                using mdom ndom addIsInt by auto
            have s3_2: "-.(m + n) \\in Int"
                using s3_1 neg_int_eq_int by auto
            have s3_3: "p + q \\in Int"
                using s1_1 s1_2 nat_in_int addIsInt by auto
            have s3_4: "-.(m + n) + ((m + n) + (p + q)) =
                (-.(m + n) + (m + n)) + (p + q)"
                using s3_1 s3_2 s3_3
                    AddAssociative_sequent by auto
            show ?thesis
                using s2_7 s3_4 by auto
            qed
        have s2_9: "(-.(m + n) + (m + n)) + (p + q) =
                    -.(m + n) + (m + n)"
            proof -
            have s3_1: "m \\in Int"
                using mdom by auto
            have s3_2: "n \\in Int"
                using ndom by auto
            have s3_3: "n + m = m + n"
                using s3_1 s3_2 AddCommutative_sequent by auto
            show ?thesis
                using s2_8 s3_3 by auto
            qed
        have s2_10: "0 + (p + q) = 0"
            proof -
            have s3_1: "-.(m + n) + (m + n) = 0"
                proof -
                have s4_1: "m + n \\in Int"
                    using mdom ndom addIsInt by auto
                show ?thesis
                    using s4_1 AddNegCancels_left by auto
                qed
            show ?thesis
                using s2_9 s3_1 by auto
            qed
        have s2_11: "p + q = 0"
            proof -
            have s3_1: "p + q \\in Int"
                using s1_1 s1_2 nat_in_int addIsInt by auto
            show ?thesis
                using s2_10 s3_1 add_0_left by auto
            qed
        show ?thesis
            using s2_11 by auto
        qed
    have s1_5: "p = 0 \<and> q = 0"
        using s1_1 s1_2 s1_4 nat_add_0 by auto
    have s1_6: "m + 0 = n"
        using s1_1 s1_5 by auto
    show ?thesis
        using s1_6 mdom add_0 by auto
    qed


theorem eq_iff_leq_both:
    assumes mdom: "m \\in Int" and ndom: "n \\in Int"
    shows "(m = n) = ((m <= n) \<and> (n <= m))"
    using mdom ndom eq_leq_both leq_both_eq by auto


(*
THEOREM dichotomy_leq ==
    ASSUME NEW a \in Int, NEW b \in Int
    PROVE (a <= b) \<or> (b <= a)
PROOF
<1>1. CASE (a - b) \in Nat
    <2>1. b + (a - b) = a
        BY a \in Int, b \in Int, a_plus_b_minus_a_eq_b
    <2>2. \E n \in Nat:  b + n = a
        BY <1>1, <2>1
    <2>3. b <= a
        BY <2>2 DEF leq
    <2> QED
        BY <2>3
<1>2. CASE (a - b) \notin Nat
    <2>1. -.(a - b) \in Nat
        <3>1. (a - b) \in Int
            <4>1. a - b = a + -.b
                BY DEF diff
            <4>2. a \in Int
                OBVIOUS
            <4>3. -.b \in Int
                BY b \in Int, neg_int_eq_int
            <4>4. a + -.b \in Int
                BY <4>2, <4>3, addIsInt
            <4> QED
                BY <4>1, <4>4
        <3> QED
            BY <3>1, <1>2, neg_negative_in_nat
    <2>2. (b - a) \in Nat
        <3>1. -.(a - b) = b - a
            BY a \in Int, b \in Int, MinusDiff
        <3> QED
            BY <2>1, <3>1
    <2>3. a + (b - a) = b
        BY a \in Int, b \in Int, a_plus_b_minus_a_eq_b
    <2>4. \E n \in Nat:  a + n = b
        BY <2>2, <2>3
    <2>5. a <= b
        BY <2>4 DEF leq
    <2> QED
        BY <2>5
<1> QED
    BY <1>1, <1>2
*)
theorem dichotomy_leq:
    assumes adom: "a \\in Int" and bdom: "b \\in Int"
    shows "(a <= b) \<or> (b <= a)"
    proof -
    have s1_1: "a - b \\in Nat ==>
            (a <= b) \<or> (b <= a)"
        proof -
        assume s1_1_asm: "a - b \\in Nat"
        have s2_1: "b + (a - b) = a"
            using adom bdom a_plus_b_minus_a_eq_b by auto
        have s2_2: "\<exists> n \<in> Nat:  b + n = a"
            using s1_1_asm s2_1 by auto
        have s2_3: "b <= a"
            unfolding leq_def
            using s2_2 by auto
        show "(a <= b) \<or> (b <= a)"
            using s2_3 by auto
        qed
    have s1_2: "a - b \\notin Nat ==>
            (a <= b) \<or> (b <= a)"
        proof -
        assume s1_2_asm: "a - b \\notin Nat"
        have s2_1: "-.(a - b) \\in Nat"
            proof -
            have s3_1: "(a - b) \\in Int"
                proof -
                have s4_1: "a - b = a + -.b"
                    unfolding diff_def by auto
                have s4_2: "a \\in Int"
                    using adom by auto
                have s4_3: "-.b \\in Int"
                    using bdom neg_int_eq_int by auto
                have s4_4: "a + -.b \\in Int"
                    using s4_2 s4_3 addIsInt by auto
                show ?thesis
                    using s4_1 s4_4 by auto
                qed
            show ?thesis
                using s3_1 s1_2_asm neg_negative_in_nat by auto
            qed
        have s2_2: "(b - a) \\in Nat"
            proof -
            have s3_1: "-.(a - b) = b - a"
                using adom bdom MinusDiff by auto
            show ?thesis
                using s2_1 s3_1 by auto
            qed
        have s2_3: "a + (b - a) = b"
            using adom bdom a_plus_b_minus_a_eq_b by auto
        have s2_4: "\<exists> n \<in> Nat:  a + n = b"
            using s2_2 s2_3 by auto
        have s2_5: "a <= b"
            unfolding leq_def
            using s2_4 by auto
        show "(a <= b) \<or> (b <= a)"
            using s2_5 by auto
        qed
    show ?thesis
        using s1_1 s1_2 by auto
    qed


theorem trichotomy_less:
    assumes adom: "a \\in Int" and bdom: "b \\in Int"
    shows "(a < b) \<or> (a = b) \<or> (b < a)"
    using adom bdom dichotomy_leq by (auto simp: less_def)


theorem trichotomy_less_0:
    assumes ndom: "n \\in Int"
    shows "(n < 0) \<or> (n = 0) \<or> (0 < n)"
    using ndom zero_in_int trichotomy_less by auto


(*
THEOREM leq_mult_monotonic ==
    \A m \in Int:  \A n \in Int:
        (m <= n) => (\A k \in Nat:  k * m <= k * n)
PROOF
<1>1. SUFFICES
        ASSUME NEW m \in Int, NEW n \in Int, NEW k \in Nat,
            m <= n
        PROVE k * m <= k * n
    BY <1>1
<1>2. PICK r \in Nat:  m + r = n
    BY <1>1 DEF leq
<1>3. k * (m + r) = k * n
    BY <1>2
<1>4. k * m + k * r = k * n
    <2>1. k \in Int
        BY <1>1, nat_in_int
    <2>2. m \in Int
        BY <1>1
    <2>3. r \in Int
        BY <1>2, nat_in_int
    <2>4. k * (m + r) = k * m + k * r
        BY <2>1, <2>2, <2>3, MultLeftDistributesAdd
    <2> QED
        BY <1>3, <2>4
<1>5. k * r \in Nat
    BY <1>1, <1>2, nat_mult_in_nat
<1>6. \E x \in Nat:  k * m + x = k * n
    BY <1>4, <1>5
<1> QED
    BY <1>6 DEF leq
*)
theorem leq_mult_monotonic:
    assumes mdom: "m \\in Int" and ndom: "n \\in Int" and
        kdom: "k \\in Nat" and mn: "m <= n"
    shows "k * m <= k * n"
    proof -
    def P \<equiv> "\<lambda> x.  x \\in Nat \<and> m + x = n"
    def r \<equiv> "CHOOSE x:  P(x)"
    have s1_2: "r \\in Nat \<and> m + r = n"
        proof -
        have s2_1: "\\E x:  P(x)"
            using mn by (auto simp: leq_def P_def)
        have s2_2: "P(r)"
            unfolding r_def
            using s2_1 chooseI_ex[of P] by auto
        show ?thesis
            using s2_2 by (auto simp: P_def)
        qed
    have s1_3: "k * (m + r) = k * n"
        using s1_2 by auto
    have s1_4: "k * m + k * r = k * n"
        proof -
        have s2_1: "k \\in Int"
            using kdom nat_in_int by auto
        have s2_2: "m \\in Int"
            using mdom by auto
        have s2_3: "r \\in Int"
            using s1_2 nat_in_int by auto
        have s2_4: "k * (m + r) = k * m + k * r"
            using s2_1 s2_2 s2_3 MultLeftDistributesAdd by auto
        show ?thesis
            using s1_3 s2_4 by auto
        qed
    have s1_5: "k * r \\in Nat"
        using kdom s1_2 nat_mult_in_nat by auto
    have s1_6: "\<exists> x \<in> Nat:  k * m + x = k * n"
        using s1_4 s1_5 by auto
    show ?thesis
        unfolding leq_def
        using s1_6 by auto
    qed


(*
THEOREM leq_mult_monotonic_neg:
    \A m \in Int:  \A n \in Int:
        (m <= n) => (\A k \in negNat:  k * n <= k * m)
PROOF
<1>1. SUFFICES
        ASSUME NEW m \in Int, NEW n \in Int, NEW k \in negNat,
            m <= n
        PROVE k * n <= k * m
    BY <1>1
<1>2. PICK r \in Nat:  m + r = n
    BY <1>1 DEF leq
<1>3. k * (m + r) = k * n
    BY <1>2
<1>4. k * m + k * r = k * n
    <2>1. k \in Int
        BY <1>1, neg_nat_in_int
    <2>2. m \in Int
        BY <1>1
    <2>3. r \in Int
        BY <1>2, nat_in_int
    <2>4. k * (m + r) = k * m + k * r
        BY <2>1, <2>2, <2>3, MultLeftDistributesAdd
    <2> QED
        BY <1>3, <2>4
<1>5. k * m = k * n + -.(k * r)
    <2>1. (k * m + k * r) + -.(k * r) = k * n + -.(k * r)
        BY <1>4
    <2>2. k * m + (k * r + -.(k * r)) = k * n + -.(k * r)
        <3>1. k * m \in Int
            BY <1>1, neg_nat_in_int, multIsInt
        <3>2. k * r \in Int
            <4>1. k \in Int
                BY <1>1, neg_nat_in_int
            <4>2. r \in Int
                BY <1>2, nat_in_int
            <4> QED
                BY <4>1, <4>2, multIsInt
        <3>3. -.(k * r) \in Int
            BY <3>2, neg_int_eq_int
        <3>4. (k * m + k * r) + -.(k * r) =
                k * m + (k * r + -.(k * r))
            BY <3>1, <3>2, <3>3, AddAssociative
        <3> QED
            BY <2>1, <3>4
    <2>3. k * r + -.(k * r) = 0
        <3>1. k * r \in Int
            <4>1. k \in Int
                BY <1>1, neg_nat_in_int
            <4>2. r \in Int
                BY <1>2, nat_in_int
            <4> QED
                BY <4>1, <4>2, multIsInt
        <3> QED
            BY <3>1, AddNegCancels
    <2>4. k * m + 0 = k * n + -.(k * r)
        BY <2>2, <2>3
    <2>5. k * m + 0 = k * m
        <3>1. k * m \in Int
            <4>1. k \in Int
                BY <1>1, neg_nat_in_int
            <4>2. m \in Int
                BY <1>1
            <4> QED
                BY <4>1, <4>2, multIsInt
        <3> QED
            BY <3>1, add_0
    <2> QED
        BY <2>4, <2>5
<1>6. k * n + (-.k * r) = k * m
    <2>1. k * n + -.(k * r) = k * m
        BY <1>5  \* symmetric
    <2>2. -.(k * r) = -.k * r
        <3>1. k \in Int
            BY <1>1, neg_nat_in_int
        <3>2. r \in Int
            BY <1>2, nat_in_int
        <3> QED
            BY <3>1, <3>2, MinusCommutesLeftMult
    <2> QED
        BY <2>1, <2>2
<1>7. -.k * r \in Nat
    <2>1. -.k \in Nat
        BY <1>1, minus_neg_nat_in_nat
    <2>2. r \in Nat
        BY <1>2
    <2> QED
        BY <2>1, <2>2, nat_mult_in_nat
<1>8. \E x \in Nat:  k * n + x = k * m
    BY <1>6, <1>7
<1> QED
    BY <1>8 DEF leq
*)
theorem leq_mult_monotonic_neg:
    assumes mdom: "m \\in Int" and ndom: "n \\in Int" and
        kdom: "k \\in negNat" and mn: "m <= n"
    shows "k * n <= k * m"
    proof -
    (* PICK r \in Nat:  m + r = n *)
    def P \<equiv> "\<lambda> x.  x \\in Nat \<and> m + x = n"
    def r \<equiv> "CHOOSE x:  P(x)"
    have s1_2: "r \\in Nat \<and> m + r = n"
        proof -
        have s2_1: "\\E x:  P(x)"
            using mn by (auto simp: leq_def P_def)
        have s2_2: "P(r)"
            unfolding r_def
            using s2_1 chooseI_ex[of P] by auto
        show ?thesis
            using s2_2 by (auto simp: P_def)
        qed
    have s1_3: "k * (m + r) = k * n"
        using s1_2 by auto
    have s1_4: "k * m + k * r = k * n"
        proof -
        have s2_1: "k \\in Int"
            using kdom neg_nat_in_int by auto
        have s2_2: "m \\in Int"
            using mdom by auto
        have s2_3: "r \\in Int"
            using s1_2 nat_in_int by auto
        have s2_4: "k * (m + r) = k * m + k * r"
            using s2_1 s2_2 s2_3 MultLeftDistributesAdd by auto
        show ?thesis
            using s1_3 s2_4 by auto
        qed
    have s1_5: "k * m = k * n + -.(k * r)"
        proof -
        have s2_1: "(k * m + k * r) + -.(k * r) = k * n + -.(k * r)"
            using s1_4 by auto
        have s2_2: "k * m + (k * r + -.(k * r)) = k * n + -.(k * r)"
            proof -
            have s3_1: "k * m \\in Int"
                using mdom kdom neg_nat_in_int multIsInt by auto
            have s3_2: "k * r \\in Int"
                proof -
                have s4_1: "k \\in Int"
                    using kdom neg_nat_in_int by auto
                have s4_2: "r \\in Int"
                    using s1_2 nat_in_int by auto
                show ?thesis
                    using s4_1 s4_2 multIsInt by auto
                qed
            have s3_3: "-.(k * r) \\in Int"
                using s3_2 neg_int_eq_int by auto
            have s3_4: "(k * m + k * r) + -.(k * r) =
                        k * m + (k * r + -.(k * r))"
                using s3_1 s3_2 s3_3 AddAssociative_sequent by auto
            show ?thesis
                using s2_1 s3_4 by auto
            qed
        have s2_3: "k * r + -.(k * r) = 0"
            proof -
            have s3_1: "k * r \\in Int"
                proof -
                have s4_1: "k \\in Int"
                    using kdom neg_nat_in_int by auto
                have s4_2: "r \\in Int"
                    using s1_2 nat_in_int by auto
                show ?thesis
                    using s4_1 s4_2 multIsInt by auto
                qed
            show ?thesis
                using s3_1 AddNegCancels by auto
            qed
        have s2_4: "k * m + 0 = k * n + -.(k * r)"
            using s2_2 s2_3 by auto
        have s2_5: "k * m + 0 = k * m"
            proof -
            have s3_1: "k * m \\in Int"
                proof -
                have s4_1: "k \\in Int"
                    using kdom neg_nat_in_int by auto
                have s4_2: "m \\in Int"
                    using mdom by auto
                show ?thesis
                    using s4_1 s4_2 multIsInt by auto
                qed
            show ?thesis
                using s3_1 add_0 by auto
            qed
        show ?thesis
            using s2_4 s2_5 by auto
        qed
    have s1_6: "k * n + (-.k * r) = k * m"
        proof -
        have s2_1: "k * n + -.(k * r) = k * m"
            using s1_5 by auto
        have s2_2: "-.(k * r) = -.k * r"
            proof -
            have s3_1: "k \\in Int"
                using kdom neg_nat_in_int by auto
            have s3_2: "r \\in Int"
                using s1_2 nat_in_int by auto
            show ?thesis
                using s3_1 s3_2 MinusCommutesLeftMult by auto
            qed
        show ?thesis
            using s2_1 s2_2 by auto
        qed
    have s1_7: "-.k * r \\in Nat"
        proof -
        have s2_1: "-.k \\in Nat"
            using kdom minus_neg_nat_in_nat by auto
        have s2_2: "r \\in Nat"
            using s1_2 by auto
        show ?thesis
            using s2_1 s2_2 nat_mult_in_nat by auto
        qed
    have s1_8: "\<exists> x \<in> Nat:  k * n + x = k * m"
        using s1_6 s1_7 by auto
    show ?thesis
        unfolding leq_def
        using s1_8 by auto
    qed


(*----------------------------------------------------------------------------*)


(* Monotonicity of addition with respect to order. *)
theorem leq_add_monotonic_right:
    assumes mdom: "m \<in> Int" and ndom: "n \<in> Int" and
        kdom: "k \<in> Int" and mn: "m <= n"
    shows "m + k <= n + k"
    proof -
    have s1_1: "\<exists> r:  r \<in> Nat \<and> m + r = n"
        using mn by (auto simp: leq_def)
    def r \<equiv> "CHOOSE r:  r \<in> Nat \<and> m + r = n"
    have s1_2: "r \<in> Nat \<and> m + r = n"
        unfolding r_def
        by (rule chooseI_ex, rule s1_1)
    have s1_3: "(m + r) + k = n + k"
        using s1_2 by auto
    have s1_4: "(m + k) + r = n + k"
        proof -
        have s2_1: "(r + m) + k = n + k"
            proof -
            have s3_1: "m \<in> Int"
                using mdom by auto
            have s3_2: "r \<in> Int"
                using s1_2 nat_in_int by auto
            have s3_3: "m + r = r + m"
                using s3_1 s3_2 AddCommutative by auto
            show ?thesis
                using s1_3 s3_3 by auto
            qed
        have s2_2: "r + (m + k) = n + k"
            proof -
            have s3_1: "r \<in> Int"
                using s1_2 nat_in_int by auto
            have s3_2: "m \<in> Int"
                using mdom by auto
            have s3_3: "k \<in> Int"
                using kdom by auto
            have s3_4: "(r + m) + k = r + (m + k)"
                using s3_1 s3_2 s3_3 AddAssociative_sequent by auto
            show ?thesis
                using s2_1 s3_4 by auto
            qed
        show ?thesis
            proof -
            have s3_1: "r \<in> Int"
                using s1_2 nat_in_int by auto
            have s3_2: "m + k \<in> Int"
                using mdom kdom addIsInt by auto
            have s3_3: "r + (m + k) = (m + k) + r"
                using s3_1 s3_2 AddCommutative by auto
            show ?thesis
                using s2_2 s3_3 by auto
            qed
        qed
    have s1_5: "\<exists> t \<in> Nat:
                    (m + k) + t = n + k"
        using s1_2 s1_4 by auto
    show "m + k <= n + k"
        using s1_5 by (auto simp: leq_def)
    qed


theorem eq_add_inj_right:
    assumes mdom: "m \\in Int" and ndom: "n \\in Int" and
        kdom: "k \\in Int" and mn: "m + k = n + k"
    shows "m = n"
    proof -
    have s1_1: "(m + k) + -.k = (n + k) + -.k"
        using mn by auto
    have s1_2: "m + (k + -.k) = n + (k + -.k)"
        proof -
        have minus_kdom: "-.k \\in Int"
            using kdom neg_int_eq_int by auto
        have s2_1: "(m + k) + -.k = m + (k + -.k)"
            using mdom kdom minus_kdom AddAssociative_sequent
            by auto
        have s2_2: "(n + k) + -.k = n + (k + -.k)"
            using ndom kdom minus_kdom AddAssociative_sequent
            by auto
        show ?thesis
            using s1_1 s2_1 s2_2 by auto
        qed
    have s1_3: "m + 0 = n + 0"
        proof -
        have s2_1: "k + -.k = 0"
            using kdom AddNegCancels_sequent by auto
        show ?thesis
            using s1_2 s2_1 by auto
        qed
    have s1_4: "m + 0 = m"
        using mdom add_0 by auto
    have s1_5: "n + 0 = n"
        using ndom add_0 by auto
    show ?thesis
        using s1_3 s1_4 s1_5 by auto
    qed


theorem less_add_monotonic_right:
    assumes mdom: "m \\in Int" and ndom: "n \\in Int" and
        kdom: "k \\in Int" and mn: "m < n"
    shows "m + k < n + k"
    proof -
    have s1_1: "m + k <= n + k"
        proof -
        have s2_1: "m <= n"
            using mn by (auto simp: less_def)
        show ?thesis
            using mdom ndom kdom s2_1 leq_add_monotonic_right by auto
        qed
    have s1_2: "m + k \<noteq> n + k"
        proof -
        have s2_1: "m + k = n + k ==> FALSE"
            proof -
            assume s2_1_asm: "m + k = n + k"
            have s3_1: "m = n"
                using s2_1_asm mdom ndom kdom eq_add_inj_right
                by auto
            have s3_2: "m \<noteq> n"
                using mn by (auto simp: less_def)
            show "FALSE"
                using s3_1 s3_2 by auto
            qed
        show ?thesis
            using s2_1 by auto
        qed
    show ?thesis
        unfolding less_def
        using s1_1 s1_2 by auto
    qed


theorem less_add_monotonic_left:
    assumes mdom: "m \\in Int" and ndom: "n \\in Int" and
        kdom: "k \\in Int" and mn: "m < n"
    shows "k + m < k + n"
    proof -
    have s1_1: "m + k < n + k"
        using mdom ndom kdom mn less_add_monotonic_right by auto
    have s1_2: "m + k = k + m"
        using mdom kdom AddCommutative_sequent by auto
    have s1_3: "n + k = k + n"
        using ndom kdom AddCommutative_sequent by auto
    show ?thesis
        using s1_1 s1_2 s1_3 by auto
    qed


theorem minus_less:
    assumes mdom: "m \\in Int" and ndom: "n \\in Int" and
        mn: "m < n"
    shows "-.n < -.m"
    proof -
    have s1_1: "m + -.m < n + -.m"
        proof -
        have s2_1: "-.m \\in Int"
            using mdom neg_int_eq_int by auto
        show ?thesis
            using mdom s2_1 ndom mn less_add_monotonic_right by auto
        qed
    have s1_2: "0 < n + -.m"
        proof -
        have s2_1: "m + -.m = 0"
            using mdom AddNegCancels_sequent by auto
        show ?thesis
            using s1_1 s2_1 by auto
        qed
    have s1_3: "-.n + 0 < -.n + (n + -.m)"
        proof -
        have s2_1: "-.n \\in Int"
            using ndom neg_int_eq_int by auto
        have s2_2: "0 \\in Int"
            using zeroIsNat nat_in_int by auto
        have s2_3: "n + -.m \\in Int"
            proof -
            have s3_1: "n \\in Int"
                using ndom by auto
            have s3_2: "-.m \\in Int"
                using mdom neg_int_eq_int by auto
            show ?thesis
                using s3_1 s3_2 addIsInt by auto
            qed
        show ?thesis
            using s1_2 s2_1 s2_2 s2_3 less_add_monotonic_left
            by auto
        qed
    have s1_4: "-.n < -.n + (n + -.m)"
        proof -
        have s2_1: "-.n + 0 = -.n"
            using ndom neg_int_eq_int add_0 by auto
        show ?thesis
            using s1_3 s2_1 by auto
        qed
    have s1_5: "-.n + (n + -.m) = -.m"
        proof -
        have s2_1: "-.n + (n + -.m) = (-.n + n) + -.m"
            using ndom mdom neg_int_eq_int AddAssociative_sequent
            by auto
        have s2_2: "-.n + n = 0"
            using ndom AddNegCancels_left by auto
        have s2_3: "(-.n + n) + -.m = 0 + -.m"
            using s2_2 by auto
        have s2_4: "0 + -.m = -.m"
            proof -
            have s3_1: "-.m \\in Int"
                using mdom neg_int_eq_int by auto
            show ?thesis
                using s3_1 add_0_left by auto
            qed
        show ?thesis
            using s2_1 s2_3 s2_4 by auto
        qed
    show ?thesis
        using s1_4 s1_5 by auto
    qed


theorem leq_diff_add:
    assumes ndom: "n \<in> Int" and mdom: "m \<in> Int" and
        kdom: "k \<in> Int" and nmk: "n - m <= k"
    shows "n <= k + m"
    proof -
    def P \<equiv> "\<lambda> x.  x \\in Nat \<and> (n - m) + x = k"
    def r \<equiv> "CHOOSE x:  P(x)"
    have s1_1: "r \\in Nat \<and> (n - m) + r = k"
        proof -
        have s2_1: "\\E x:  P(x)"
            using nmk by (auto simp: leq_def P_def)
        have s2_2: "P(r)"
            unfolding r_def
            using s2_1 chooseI_ex[of P] by auto
        show ?thesis
            using s2_2 by (auto simp: P_def)
        qed
    have s1_2: "m + ((n - m) + r) = m + k"
        using s1_1 by auto
    have s1_3: "(m + -.m) + (n + r) = k + m"
        proof -
        have s2_1: "m + ((n - m) + r) = (m + -.m) + (n + r)"
            proof -
            have s3_1: "m + ((n - m) + r) =
                    m + ((n + -.m) + r)"
                unfolding diff_def by auto
            also have s3_2: "... = m + ((-.m + n) + r)"
                using mdom neg_int_eq_int ndom
                    AddCommutative_sequent by auto
            also have s3_3: "... = (m + (-.m + n)) + r"
                using mdom neg_int_eq_int ndom s1_1 nat_in_int
                    addIsInt AddAssociative_sequent by auto
            also have s3_4: "... = ((m + -.m) + n) + r"
                using mdom neg_int_eq_int ndom
                    AddAssociative_sequent by auto
            also have s3_5: "... = (m + -.m) + (n + r)"
                using mdom neg_int_eq_int addIsInt ndom
                    s1_1 nat_in_int AddAssociative_sequent by auto
            finally show ?thesis .
            qed
        have s2_2: "m + k = k + m"
            using mdom kdom AddCommutative_sequent by auto
        show ?thesis
            using s1_2 s2_1 s2_2 by auto
        qed
    have s1_4: "n + r = k + m"
        proof -
        have s2_1: "m + -.m = 0"
            using mdom AddNegCancels_sequent by auto
        have s2_2: "(m + -.m) + (n + r) = n + r"
            proof -
            have s3_1: "(m + -.m) + (n + r) = 0 + (n + r)"
                using s2_1 by auto
            have s3_2: "0 + (n + r) = n + r"
                proof -
                have s4_1: "n + r \\in Int"
                    using ndom s1_1 nat_in_int addIsInt by auto
                show ?thesis
                    using s4_1 add_0_left by auto
                qed
            show ?thesis
                using s3_1 s3_2 by auto
            qed
        show ?thesis
            using s1_3 s2_2 by auto
        qed
    have s1_5: "\<exists> x \<in> Nat:  n + x = k + m"
        using s1_1 s1_4 by auto
    show ?thesis
        unfolding leq_def
        using s1_5 by auto
    qed


theorem leq_diff_nat:
    assumes mdom: "m \\in Int" and ndom: "n \\in Nat"
    shows "m - n <= m"
    proof -
    have s1_1: "(m - n) + n = m"
        proof -
        have s2_1: "-.n + n = 0"
            proof -
            have s3_1: "n \\in Int"
                using ndom nat_in_int by auto
            show ?thesis
                using s3_1 AddNegCancels_left by auto
            qed
        have s2_2: "m + (-.n + n) = m + 0"
            using s2_1 by auto
        have s2_3: "(m + -.n) + n = m"
            proof -
            have s3_1: "m + (-.n + n) = (m + -.n) + n"
                proof -
                have s4_1: "m \\in Int"
                    using mdom by auto
                have s4_2: "-.n \\in Int"
                    using ndom minus_nat_in_int by auto
                have s4_3: "n \\in Int"
                    using ndom nat_in_int by auto
                show ?thesis
                    using s4_1 s4_2 s4_3 AddAssociative_sequent by auto
                qed
            have s3_2: "m + 0 = m"
                using mdom add_0 by auto
            show ?thesis
                using s2_2 s3_1 s3_2 by auto
            qed
        show ?thesis
            unfolding diff_def
            using s2_3 by auto
        qed
    have s1_2: "\<exists> r \<in> Nat:  (m - n) + r = m"
        using ndom s1_1 by auto
    show ?thesis
        unfolding leq_def
        using s1_2 by auto
    qed


(* See also the theorem `less_leq_trans`. *)
theorem leq_less_trans:
    assumes mdom: "m \\in Int" and ndom: "n \\in Int"
        and kdom: "k \\in Int" and
        mn: "m <= n" and nk: "n < k"
    shows "m < k"
    proof -
    have s1_1: "(n <= k) \<and> (n \<noteq> k)"
        using nk by (auto simp: less_def)
    have s1_2: "m <= k"
        proof -
        have s2_2: "n <= k"
            using s1_1 by auto
        have s2_3: "m <= n"
            using mn by auto
        show ?thesis
            using s2_2 s2_3 mdom ndom kdom LeqTransitive
            by iprover
        qed
    have s1_3: "m \<noteq> k"
        proof -
        {
            assume s3_1: "m = k"
            have s3_2: "k <= n"
                using mn s3_1 by auto
            have s3_3: "n <= k"
                using nk by (auto simp: less_def)
            have s3_4: "n = k"
                using s3_2 s3_3 ndom kdom leq_both_eq
                by auto
            have "FALSE"
                using s3_4 s1_1 by auto
        }
        from this show "m \<noteq> k"
            by auto
        qed
    show ?thesis
        unfolding less_def
        using s1_2 s1_3 by auto
    qed


(* See also the theorem `leq_less_trans`. *)
theorem less_leq_trans:
    assumes mdom: "m \\in Int" and ndom: "n \\in Int"
        and kdom: "k \\in Int" and
        mn: "m < n" and nk: "n <= k"
    shows "m < k"
    proof -
    have s1_1: "(m <= n) \<and> (m \<noteq> n)"
        using mn by (auto simp: less_def)
    have s1_2: "m <= k"
        proof -
        have s2_1: "m <= n"
            using s1_1 by auto
        have s2_2: "n <= k"
            using nk by auto
        show ?thesis
            using s2_1 s2_2 mdom ndom kdom LeqTransitive
            by iprover
        qed
    have s1_3: "m \<noteq> k"
        proof -
        have s2_1: "m = k ==> FALSE"
            proof -
            assume s2_1_asm: "m = k"
            have s3_1: "n <= m"
                using nk s2_1_asm by auto
            have s3_2: "m <= n"
                using mn by (auto simp: less_def)
            have s3_3: "m = n"
                using s3_1 s3_2 mdom ndom leq_both_eq
                by auto
            show "FALSE"
                using s3_3 s1_1 by auto
            qed
        show ?thesis
            using s2_1 by auto
        qed
    show ?thesis
        unfolding less_def
        using s1_2 s1_3 by auto
    qed


theorem less_not_leq:
    assumes mdom: "m \\in Int" and ndom: "n \\in Int"
    shows "(m < n) = (~ (n <= m))"
    proof -
    have s1_1: "m < n ==> ~ (n <= m)"
        proof -
        assume mn: "m < n"
        have s2_1: "(m <= n) \<and> (m \<noteq> n)"
            using mn by (auto simp: less_def)
        have s2_2: "n <= m ==> FALSE"
            proof -
            assume nm: "n <= m"
            have s3_1: "m = n"
                using mdom ndom s2_1 nm leq_both_eq by blast
            show "FALSE"
                using s2_1 s3_1 by auto
            qed
        show "~ (n <= m)"
            using s2_2 by auto
        qed
    have s1_2: "(~ (n <= m)) ==> m < n"
        proof -
        assume nm: "~ (n <= m)"
        have s2_1: "(m <= n) \<or> (n <= m)"
            using mdom ndom dichotomy_leq by auto
        have s2_2: "m <= n"
            using nm s2_1 by auto
        have s2_3: "m = n ==> FALSE"
            proof -
            assume eq: "m = n"
            have s3_1: "n <= n"
                using ndom LeqReflexive by auto
            have s3_2: "n <= m"
                using eq s3_1 by auto
            show "FALSE"
                using nm s3_2 by auto
            qed
        have s2_4: "m \<noteq> n"
            using s2_3 by auto
        show "m < n"
            unfolding less_def
            using s2_2 s2_4 by auto
        qed
    have s1_3: "(~ (n <= m)) \\in BOOLEAN"
        by auto
    have s1_4: "(m < n) \\in BOOLEAN"
        unfolding less_def by auto
    show ?thesis
        using s1_1 s1_2 s1_3 s1_4 by auto
    qed


theorem leq_linear:
    assumes adom: "a \\in Int" and bdom: "b \\in Int"
    shows "(~ (a <= b)) \<or> (a = b) \<or> (~ (b <= a))"
    using adom bdom trichotomy_less[of "a" "b"]
        less_not_leq[of "a" "b"]
        less_not_leq[of "b" "a"] by auto


theorem leq_geq_linear:
    assumes adom: "a \\in Int" and bdom: "b \\in Int"
    shows "(~ (b >= a)) \<or> (a = b) \<or> (~ (b <= a))"
    using adom bdom leq_linear by auto


(*
THEOREM less_is_leq_plus_one ==
    ASSUME NEW m \in Int, NEW n \in Int, m < n
    PROVE m + 1 <= n
PROOF
<1>1. PICK r \in Nat:  m + r = n
    BY m < n DEF less, leq
<1>2. PICK k \in Nat:  r = Succ[k]
    <2>1. r = 0 \/ \E k \in Nat:  r = Succ[k]
        BY <1>1, nat_0_succ
    <2>2. ASSUME r = 0
          PROVE FALSE
        <3>1. m + 0 = n
            BY <1>1, <2>2
        <3>2. m = n
            BY <3>1, m \in Int, add_0
        <3>3. m # n
            BY m < n DEF less
        <3> QED
            BY <3>2, <3>3
    <2> QED
        BY <2>1, <2>2
<1>3. m + Succ[k] = n
    BY <1>1, <1>2
<1>4. m + (k + 1) = n
    <2>1. Succ[k] = k + 1
        BY <1>2, nat_add_1
    <2> QED
        BY <1>3, <2>1
<1>5. m + (1 + k) = n
    <2>1. k \in Int
        BY <1>2, nat_in_int
    <2>2. 1 \in Int
        BY oneIsNat, nat_in_int
    <2>3. k + 1 = 1 + k
        BY <2>1, <2>2, AddCommutative
    <2> QED
        BY <1>4, <2>3
<1>6. (m + 1) + k = n
    <2>1. m \in Int
        OBVIOUS
    <2>2. 1 \in Int
        BY oneIsNat nat_in_int
    <2>3. k \in Int
        BY <1>2, nat_in_int
    <2>4. m + (1 + k) = (m + 1) + k
        BY <2>1, <2>2, <2>3, AddAssociative
    <2> QED
        BY <1>5, <2>4
<1>7. \E q \in Nat:  (m + 1) + q = n
    BY <1>2, <1>6
<1> QED
    BY <1>7 DEF leq
*)
theorem less_is_leq_plus_one:
    assumes mdom: "m \\in Int" and ndom: "n \\in Int" and
        mn: "m < n"
    shows "m + 1 <= n"
    proof -
    (* PICK r \in Nat:  m + r = n *)
    def P \<equiv> "\<lambda> x.  x \\in Nat \<and> m + x = n"
    def r \<equiv> "CHOOSE x:  P(x)"
    have s1_1: "r \\in Nat \<and> m + r = n"
        proof -
        have s2_1: "\\E x:  P(x)"
            using mn by (auto simp: less_def leq_def P_def)
        have s2_2: "P(r)"
            unfolding r_def
            using s2_1 chooseI_ex[of P] by auto
        show ?thesis
            using s2_2 by (auto simp: P_def)
        qed
    (* PICK k \in Nat:  r = Succ[k] *)
    def Q \<equiv> "\<lambda> x.  x \\in Nat \<and> r = Succ[x]"
    def k \<equiv> "CHOOSE x:  Q(x)"
    have s1_2: "k \\in Nat \<and> r = Succ[k]"
        proof -
        have s2_1: "r = 0 \<or>
            (\<exists> x \<in> Nat:  r = Succ[x])"
            using s1_1 nat_0_succ by auto
        have s2_2: "r = 0 ==> FALSE"
            proof -
            assume s2_2_asm: "r = 0"
            have s3_1: "m + 0 = n"
                using s1_1 s2_2_asm by auto
            have s3_2: "m = n"
                using s3_1 mdom add_0 by auto
            have s3_3: "m \<noteq> n"
                using mn by (auto simp: less_def)
            show ?thesis
                using s3_2 s3_3 by auto
            qed
        have s2_3: "\<exists> x \<in> Nat:  r = Succ[x]"
            using s2_1 s2_2 by auto
        have s2_4: "\\E x:  Q(x)"
            unfolding Q_def using s2_3 by auto
        have s2_5: "Q(k)"
            unfolding k_def
            using s2_4 chooseI_ex[of Q] by auto
        show ?thesis
            using s2_5 by (auto simp: Q_def)
        qed
    have s1_3: "m + Succ[k] = n"
        using s1_1 s1_2 by auto
    have s1_4: "m + (k + 1) = n"
        proof -
        have s2_1: "Succ[k] = k + 1"
            using s1_2 nat_add_1 by fast
        show ?thesis
            using s1_3 s2_1 by auto
        qed
    have s1_5: "m + (1 + k) = n"
        proof -
        have s2_1: "k \\in Int"
            using s1_2 nat_in_int by auto
        have s2_2: "1 \\in Int"
            using oneIsNat nat_in_int by auto
        have s2_3: "k + 1 = 1 + k"
            using s2_1 s2_2 AddCommutative_sequent by auto
        show ?thesis
            using s1_4 s2_3 by auto
        qed
    have s1_6: "(m + 1) + k = n"
        proof -
        have s2_1: "m \\in Int"
            using mdom by auto
        have s2_2: "1 \\in Int"
            using oneIsNat nat_in_int by auto
        have s2_3: "k \\in Int"
            using s1_2 nat_in_int by auto
        have s2_4: "m + (1 + k) = (m + 1) + k"
            using s2_1 s2_2 s2_3 AddAssociative_sequent by auto
        show ?thesis
            using s1_5 s2_4 by auto
        qed
    have s1_7: "\<exists> q \<in> Nat:  (m + 1) + q = n"
        using s1_2 s1_6 by auto
    show ?thesis
        unfolding leq_def using s1_7 by auto
    qed


(*
THEOREM less_succ_nat ==
    ASSUME NEW n \in Nat
    PROVE n < Succ[n]
PROOF
<1>1. n <= Succ[n]
    <2>1. Succ[n] = n + 1
        BY n \in Nat, nat_add_1
    <2>2. 1 \in Nat
        BY oneIsNat
    <2>3. \E r \in Nat:  n + r = Succ[n]
        BY <2>1, <2>2
    <2> QED
        BY <2>3 DEF leq
<1>2. n # Succ[n]
    BY n \in Nat, succIrrefl
<1> QED
    BY <1>1, <1>2 DEF less
*)
theorem less_succ_nat:
    assumes ndom: "n \\in Nat"
    shows "n < Succ[n]"
    proof -
    have s1_1: "n <= Succ[n]"
        proof -
        have s2_1: "Succ[n] = n + 1"
            using ndom nat_add_1 by fast
        have s2_2: "1 \\in Nat"
            using oneIsNat by auto
        have s2_3: "\\E r \\in Nat:  n + r = Succ[n]"
            using s2_1 s2_2 by auto
        show ?thesis
            unfolding leq_def
            using s2_3 by auto
        qed
    have s1_2: "n \<noteq> Succ[n]"
        using ndom succIrrefl by auto
    show ?thesis
        unfolding less_def
        using s1_1 s1_2 by auto
    qed


theorem less_pred_nat:
    assumes ndom: "n \\in Nat \<setminus> {0}"
    shows "Pred[n] < n"
    proof -
    have s1_1: "Pred[n] <= n"
        proof -
        have s2_1: "Pred[n] \\in Nat"
            using ndom Pred_in_nat by auto
        have s2_2: "Succ[Pred[n]] = n"
            using ndom Succ_Pred_nat by auto
        have s2_3: "Pred[n] + 1 = n"
            proof -
            have s3_1: "Succ[Pred[n]] = Pred[n] + 1"
                using s2_1 nat_add_1 by fast
            show ?thesis
                using s2_2 s3_1 by auto
            qed
        have s2_4: "1 \\in Nat"
            using oneIsNat by auto
        have s2_5: "\\E x \\in Nat:  Pred[n] + x = n"
            using s2_3 s2_4 by auto
        show ?thesis
            unfolding leq_def
            using s2_5 by auto
        qed
    have s1_2: "Pred[n] \<noteq> n"
        using ndom pred_irrefl by auto
    show ?thesis
        unfolding less_def
        using s1_1 s1_2 by auto
    qed


theorem less_isucc:
    assumes idom: "i \\in Int"
    shows "i < iSucc[i]"
    proof -
    have s1_1: "i \\in Nat ==> i < iSucc[i]"
        proof -
        assume s1_1_asm: "i \\in Nat"
        have s2_1: "i < Succ[i]"
            using s1_1_asm less_succ_nat by auto
        have s2_2: "iSucc[i] = Succ[i]"
            unfolding iSucc_def
            using idom s1_1_asm by auto
        show "i < iSucc[i]"
            using s2_1 s2_2 by auto
        qed
    have s1_2: "i \\notin Nat ==> i < iSucc[i]"
        proof -
        assume s1_2_asm: "i \\notin Nat"
        have s2_1: "iSucc[i] = -.Pred[-.i]"
            unfolding iSucc_def
            using idom s1_2_asm by auto
        have s2_2: "-.i \\in Nat \<setminus> {0}"
            using idom s1_2_asm minus_neg_int_in_nat by auto
        have s2_3: "Pred[-.i] < -.i"
            using s2_2 less_pred_nat by auto
        have s2_4: "-.-.i < -.Pred[-.i]"
            proof -
            have s3_1: "Pred[-.i] \\in Int"
                using s2_2 Pred_in_nat nat_in_int by auto
            have s3_2: "-.i \\in Int"
                using s2_2 nat_in_int by auto
            show ?thesis
                using s2_3 s3_1 s3_2 minus_less by auto
            qed
        have s2_5: "-.-.i = i"
            using idom minus_involutive by auto
        show "i < iSucc[i]"
            using s2_1 s2_4 s2_5 by auto
        qed
    show ?thesis
        using s1_1 s1_2 by iprover
    qed


theorem less_i_add_1:
    assumes idom: "i \\in Int"
    shows "i < i + 1"
    proof -
    have s1_1: "i < iSucc[i]"
        using idom less_isucc by auto
    have s1_2: "iSucc[i] = i + 1"
        using idom isucc_eq_add_1 by auto
    show ?thesis
        using s1_1 s1_2 by auto
    qed


(*
THEOREM i_less_j_nat ==
    ASSUME NEW i \in Int, NEW j \in Nat, i <= j
    PROVE i < Succ[j]
PROOF
<1>1. j < Succ[j]
    BY j \in Nat, less_succ_nat
<1>2. j \in Int
    BY j \in Nat, nat_in_int
<1>3. Succ[j] \in Int
    BY j \in Nat, succIsNat, nat_in_int
<1> QED
    BY i \in Int, <1>2, <1>3, i <= j, <1>1,
        leq_less_trans
*)
theorem i_less_succ_j_nat:
    assumes idom: "i \\in Int" and jdom: "j \\in Nat" and
        ij: "i <= j"
    shows "i < Succ[j]"
    proof -
    have s1_1: "j < Succ[j]"
        using jdom less_succ_nat by auto
    have s1_2: "j \\in Int"
        using jdom nat_in_int by auto
    have s1_3: "Succ[j] \\in Int"
        using jdom succIsNat nat_in_int by auto
    show ?thesis
        using idom s1_2 s1_3 ij s1_1 leq_less_trans by auto
    qed


theorem less_add_1:
    assumes idom: "i \\in Int" and jdom: "j \\in Int" and
        ij: "i <= j"
    shows "i < j + 1"
    proof -
    have s1_1: "j < j + 1"
        using jdom less_i_add_1 by auto
    have s1_2: "j + 1 \\in Int"
        proof -
        have s2_1: "1 \\in Int"
            using oneIsNat nat_in_int by auto
        show ?thesis
            using jdom s2_1 addIsInt by auto
        qed
    show ?thesis
        using idom jdom s1_2 ij s1_1 leq_less_trans by auto
    qed


(*----------------------------------------------------------------------------*)
(* Intervals of integers. *)


(*
THEOREM SplitNat0 ==
    Nat = {0} \cup {n + 1:  n \in Nat}
PROOF
<1>1. ASSUME NEW n \in Nat
      PROVE n \in {0} \cup {k + 1:  k \in Nat}
    <2>1. n = 0 \/ \E m \in Nat:  n = Succ[m]
        BY <1>1, nat_0_succ
    <2>2. (\E m \in Nat:  n = Succ[m]) <=>
        n \in {Succ[m]:  m \in Nat}
        OBVIOUS
    <2>3. ASSUME NEW m \in Nat
          PROVE Succ[m] = m + 1
        BY <2>3, nat_add_1
    <2>4. {Succ[m]:  m \in Nat} =
            {m + 1:  m \in Nat}
        BY <2>3
    <2>5. n \in {0} \/ n \in {m + 1:  m \in Nat}
        BY <2>1, <2>2, <2>4
    <2> QED
        BY <2>5
<1>2. ASSUME NEW n \in {0} \cup {k + 1:  k \in Nat}
      PROVE n \in Nat
    <2>1. CASE n = 0
        BY <2>1, zeroIsNat
    <2>2. CASE n \in {k + 1:  k \in Nat}
        <3>1. PICK k \in Nat:  n = k + 1
            BY <2>2
        <3>2. k + 1 \in Nat
            BY <3>1, oneIsNat, nat_add_in_nat
        <3> QED
            BY <3>1, <3>2
    <2> QED
        BY <1>2, <2>1, <2>2
<1> QED
    BY <1>1, <1>2
*)
theorem SplitNat0:
    "Nat = {0} \<union> {n + 1:  n \\in Nat}"
    proof -
    have s1_1: "\\A n \\in Nat:  n \\in {0} \<union> {k + 1:  k \\in Nat}"
        proof -
        {
        fix "n" :: "c"
        assume s1_1_asm: "n \\in Nat"
        have s2_1: "n = 0 \<or> (\\E m \\in Nat:  n = Succ[m])"
            using s1_1_asm nat_0_succ by auto
        have s2_2: "\\E m \\in Nat:  n = Succ[m] ==>
                n \\in {Succ[m]:  m \\in Nat}"
            by auto
        have s2_3: "{Succ[m]:  m \\in Nat} = {m + 1:  m \\in Nat}"
            proof -
            have s3_1: "\\A y \\in {Succ[m]:  m \\in Nat}:
                            y \\in {m + 1:  m \\in Nat}"
                proof -
                {
                fix "y" :: "c"
                assume s4_1: "y \\in {Succ[m]:  m \\in Nat}"
                have s4_2: "\\E m \\in Nat:  y = Succ[m]"
                    using s4_1 setOfAll by auto
                have s4_3: "\\E m:  m \\in Nat \<and> y = Succ[m]"
                    using s4_2 by (auto simp: bEx_def)
                (* PICK r \in Nat:  y = Succ[r] *)
                def P \<equiv> "\<lambda> x.  x \\in Nat \<and> y = Succ[x]"
                def r \<equiv> "CHOOSE x:  P(x)"
                have s4_4: "r \\in Nat \<and> y = Succ[r]"
                    proof -
                    have s5_1: "\\E x:  P(x)"
                        using s4_3 by (auto simp: P_def)
                    have s5_2: "P(r)"
                        unfolding r_def
                        using s5_1 chooseI_ex[of P] by auto
                    show ?thesis
                        using s5_2 by (auto simp: P_def)
                    qed
                have s4_5: "r \\in Nat \<and> y = r + 1"
                    proof -
                    have s5_1: "r \\in Nat"
                        using s4_4 by auto
                    have s5_2: "Succ[r] = r + 1"
                        using s5_1 nat_add_1 by fast
                    have s5_3: "y = Succ[r]"
                        using s4_4 by auto
                    show ?thesis
                        using s5_1 s5_2 s5_3 by auto
                    qed
                have "y \\in {m + 1:  m \\in Nat}"
                    using s4_5 setOfAll_eqI by auto
                }
                from this show ?thesis
                    by auto
                qed
            have s3_2: "\\A y \\in {m + 1:  m \\in Nat}:
                            y \\in {Succ[m]:  m \\in Nat}"
                proof -
                {
                fix "y" :: "c"
                assume s4_1: "y \\in {m + 1:  m \\in Nat}"
                have s4_2: "\\E m \\in Nat:  y = m + 1"
                    using s4_1 setOfAll by auto
                have s4_3: "\\E m:  m \\in Nat \<and> y = m + 1"
                    using s4_2 by (auto simp: bEx_def)
                (* PICK r \in Nat:  y = r + 1 *)
                def P \<equiv> "\<lambda> x.  x \\in Nat \<and> y = x + 1"
                def r \<equiv> "CHOOSE x:  P(x)"
                have s4_4: "r \\in Nat \<and> y = r + 1"
                    proof -
                    have s5_1: "\\E x:  P(x)"
                        using s4_3 by (auto simp: P_def)
                    have s5_2: "P(r)"
                        unfolding r_def
                        using s5_1 chooseI_ex[of P] by auto
                    show ?thesis
                        using s5_2 by (auto simp: P_def)
                    qed
                have s4_5: "r \\in Nat \<and> y = Succ[r]"
                    proof -
                    have s5_1: "r \\in Nat"
                        using s4_4 by auto
                    have s5_2: "Succ[r] = r + 1"
                        using s5_1 nat_add_1 by fast
                    have s5_3: "y = r + 1"
                        using s4_4 by auto
                    show ?thesis
                        using s5_1 s5_2 s5_3 by auto
                    qed
                have "y \\in {Succ[m]:  m \\in Nat}"
                    using s4_5 setOfAll_eqI by auto
                }
                from this show ?thesis
                    by auto
                qed
            show ?thesis
                using s3_1 s3_2 extension
                by (auto simp: subset_def)
            qed
        have s2_4: "n \\in {0} \<or> n \\in {m + 1:  m \\in Nat}"
            using s2_1 s2_2 s2_3 by auto
        have s2_5: "n \\in {0} \<union> {k + 1:  k \\in Nat}"
            using s2_4 by auto
        }
        from this show ?thesis
            by auto
        qed
    have s1_2: "\\A n \\in {0} \<union> {k + 1:  k \\in Nat}:  n \\in Nat"
        proof -
        {
        fix "n" :: "c"
        assume s1_2_asm: "n \\in {0} \<union> {k + 1:  k \\in Nat}"
        have s2_1: "n = 0 ==> n \\in Nat"
            proof -
            assume s2_1_asm: "n = 0"
            show "n \\in Nat"
                using s2_1_asm zeroIsNat by auto
            qed
        have s2_2: "n \\in {k + 1:  k \\in Nat} ==> n \\in Nat"
            proof -
            assume s2_2_asm: "n \\in {k + 1:  k \\in Nat}"
            have s3_1: "\\E k \\in Nat:  n = k + 1"
                using s2_2_asm by auto
            have s3_2: "\\E k:  k \\in Nat \<and> n = k + 1"
                using s3_1 by auto
            (* PICK k \in Nat:  n = k + 1 *)
            def P \<equiv> "\<lambda> x.  x \\in Nat \<and> n = x + 1"
            def k \<equiv> "CHOOSE x:  P(x)"
            have s3_3: "k \\in Nat \<and> n = k + 1"
                proof -
                have s4_1: "\\E x:  P(x)"
                    using s3_2 by (auto simp: P_def)
                have s4_2: "P(k)"
                    unfolding k_def
                    using s4_1 chooseI_ex[of P] by auto
                show ?thesis
                    using s4_2 by (auto simp: P_def)
                qed
            have s3_4: "k + 1 \\in Nat"
                using s3_3 oneIsNat nat_add_in_nat by auto
            show "n \\in Nat"
                using s3_3 s3_4 by auto
            qed
        have s2_3: "n \\in Nat"
            using s1_2_asm s2_1 s2_2 by auto
        }
        from this show ?thesis
            by auto
        qed
    show ?thesis
        using s1_1 s1_2 extension
        by (auto simp: subset_def)
    qed


(*
THEOREM NatIsAdd0 ==
    Nat = {k + 0:  k \in Nat}
PROOF
<1>1. Nat = {k:  k \in Nat}
    OBVIOUS
<1>2. ASSUME NEW k \in Nat
      PROVE k + 0 = k
    BY <1>2, nat_in_int, add_0
<1>3. {k:  k \in Nat} =
        {k + 0:  k \in Nat}
    BY <1>2
<1> QED
    BY <1>1, <1>3
*)
theorem NatIsAdd0:
    "Nat = {k + 0:  k \\in Nat}"
    proof -
    have s1_1: "Nat = {k:  k \\in Nat}"
        by auto
    have s1_2: "{k:  k \\in Nat} = {k + 0:  k \\in Nat}"
        using nat_in_int add_0 by auto
    show ?thesis
        using s1_1 s1_2 by auto
    qed


(*
THEOREM SplitAddi ==
    ASSUME NEW i \in Nat
    PROVE {k + i:  k \in Nat} =
            {i} \cup {k + Succ[i]:  k \in Nat}
PROOF
<1>1. n \in {k + i:  k \in Nat}
    = \E k \in Nat:  n = k + i
    OBVIOUS
<1>2. @ = \E k \in {0} \cup {q + 1:  q \in Nat}:
            n = k + i
    BY SplitNat0
<1>3. @ = \/ \E k \in {0}:  n = k + i
          \/ \E k \in {q + 1:  q \in Nat}:  n = k + i
    OBVIOUS
<1>4. @ = \/ n = 0 + i
          \/ \E k:  /\ k \in {q + 1:  q \in Nat}
                    /\ n = k + i
    OBVIOUS
<1>5. @ = \/ n = i
          \/ \E k:  /\ \E q \in Nat:  k = q + 1
                    /\ n = k + i
    BY i \in Nat, nat_in_int, add_0_left
<1>6. @ = \/ n = i
          \/ \E k:  \E q \in Nat:  /\ k = q + 1
                                   /\ n = k + i
    OBVIOUS
<1>7. @ = \/ n = i
          \/ \E q \in Nat:  n = (q + 1) + i
    OBVIOUS
<1>8. @ = \/ n \in {i}
          \/ n \in {q + (i + 1):  q \in Nat}
    BY AddCommutative, AddAssociative,
        oneIsNat, nat_in_int
<1>9. @ = \/ n \in {i}
          \/ n \in {q + Succ[i]:  q \in Nat}
    BY nat_add_1
<1>10. @ = n \in {i} \cup {q + Succ[i]:  q \in Nat}
    OBVIOUS
<1> QED
    BY <1>1, <1>2, <1>3, <1>4, <1>5,
        <1>6, <1>7, <1>8, <1>9, <1>10
*)
theorem SplitAddi:
    assumes idom: "i \\in Nat"
    shows "{k + i:  k \\in Nat} =
            ({i} \<union> {k + Succ[i]:  k \\in Nat})"
    proof -
    {
    fix "n" :: "c"
    have s1_1: "n \\in {k + i:  k \\in Nat}
            = (\\E k \\in Nat:  n = k + i)"
        by auto
    also have s1_2: "... = (
            \\E k \\in ({0} \<union> {q + 1:  q \\in Nat}):
                n = k + i)"
        using SplitNat0 by auto
    also have s1_3: "... = (
        (\\E k \\in {0}:  n = k + i) \<or>
        (\\E k \\in {q + 1:  q \\in Nat}:  n = k + i))"
        by auto
    also have s1_4: "... = (
        (n = 0 + i) \<or>
        (\\E k:  (k \\in {q + 1:  q \\in Nat}) \<and> n = k + i))"
        by auto
    also have s1_5: "... = (
        (n = i) \<or>
        (\\E k:  (\\E q \\in Nat:  k = q + 1) \<and> n = k + i))"
        using idom nat_in_int add_0_left by auto
    also have s1_6: "... = (
        (n = i) \<or>
        (\\E k:  \\E q \\in Nat:  k = q + 1 \<and> n = k + i))"
        by auto
    also have s1_7: "... = (
        (n = i) \<or>
        (\\E q \\in Nat:  n = (q + 1) + i))"
        by auto
    also have s1_8: "... = (
        (n = i) \<or>
        (\\E q \\in Nat:  n = q + (i + 1)))"
        using AddCommutative_sequent AddAssociative_sequent
            oneIsNat idom nat_in_int by auto
    also have s1_9: "... = (
        (n = i) \<or>
        (\\E q \\in Nat:  n = q + Succ[i]))"
        using idom nat_add_1[symmetric] by force
    also have s1_10: "... = (
        (n \\in {i}) \<or>
        (n \\in {q + Succ[i]:  q \\in Nat}))"
        by auto
    also have s1_11: "... = (
        n \\in ({i} \<union> {k + Succ[i]:  k \\in Nat}))"
        by auto
    finally have s1_12: "
        (n \\in {k + i:  k \\in Nat})
        =  (n \\in ({i} \<union> {k + Succ[i]:  k \\in Nat}))" .
    }
    from this have s1_13: "\<And> n.  (n \\in {k + i:  k \\in Nat})
        =  (n \\in ({i} \<union> {k + Succ[i]:  k \\in Nat}))"
        by auto
    have s1_14: "\<And> n.  (n \\in {k + i:  k \\in Nat})
        ==> (n \\in ({i} \<union> {k + Succ[i]:  k \\in Nat}))"
        using s1_13 by auto
    have s1_15: "\<And> n.  (n \\in ({i} \<union> {k + Succ[i]:  k \\in Nat}))
        ==> (n \\in {k + i:  k \\in Nat})"
        using s1_13 by auto
    show ?thesis
        using s1_14 s1_15
        by (rule setEqualI, blast)
    qed


(*
THEOREM LeqNatOpenInterval ==
    ASSUME NEW i \in Nat,
        NEW j \in {k + Succ[i]:  k \in Nat}
    PROVE ~ (j <= i)
PROOF
<1>1. PICK k \in Nat:  j = k + Succ[i]
    OBVIOUS
<1>2. Succ[i] <= j
    BY <1>1 DEF leq
<1>3. i < Succ[i]
    BY i \in Nat, less_succ_nat
<1>4. i < j
    <2>1. i \in Int
        BY i \in Nat, nat_in_int
    <2>2. j \in Int
        BY <1>1, i \in Nat, succIsNat, nat_in_int,
            addIsInt
    <2>3. Succ[i] \in Int
        BY i \in Nat, succIsNat, nat_in_int
    <2> QED
        BY <2>1, <2>2, <2>3, <1>3, <1>2,
            leq_less_trans
<1>5. i \in Int
    BY i \in Nat, nat_in_int
<1>6. j \in Int
    BY <1>1, i \in Nat, succIsNat, nat_in_int,
        addIsInt
<1> QED
    BY <1>4, <1>5, <1>6, less_not_leq
*)
theorem LeqNatOpenInterval:
    assumes idom: "i \\in Nat" and
        jdom: "j \\in {k + Succ[i]:  k \\in Nat}"
    shows "~ (j <= i)"
    proof -
    def P \<equiv> "\<lambda> x.  x \\in Nat \<and> j = x + Succ[i]"
    def k \<equiv> "CHOOSE x:  P(x)"
    have s1_1: "k \\in Nat \<and> j = k + Succ[i]"
        proof -
        have s2_1: "\\E x:  P(x)"
            using jdom by (auto simp: P_def)
        have s2_2: "P(k)"
            unfolding k_def
            using s2_1 chooseI_ex[of P] by auto
        show ?thesis
            using s2_2 by (auto simp: P_def)
        qed
    have s1_2: "Succ[i] <= j"
        proof -
        have s2_1: "k + Succ[i] = j"
            using s1_1 by auto
        have s2_2: "Succ[i] + k = j"
            using s2_1 s1_1 idom succIsNat nat_in_int
                AddCommutative_sequent by auto
        have s2_3: "k \\in Nat"
            using s1_1 by auto
        show ?thesis
            unfolding leq_def
            using s2_2 s2_3 by auto
        qed
    have s1_3: "i < Succ[i]"
        using idom less_succ_nat by auto
    have s1_4: "i < j"
        proof -
        have s2_1: "i \\in Int"
            using idom nat_in_int by auto
        have s2_2: "j \\in Int"
            proof -
            have s3_1: "k \\in Int"
                using s1_1 nat_in_int by auto
            have s3_2: "Succ[i] \\in Int"
                using idom succIsNat nat_in_int by auto
            have s3_3: "j = k + Succ[i]"
                using s1_1 by auto
            show ?thesis
                using s3_1 s3_2 s3_3 addIsInt by auto
            qed
        have s2_3: "Succ[i] \\in Int"
            using idom succIsNat nat_in_int by auto
        show ?thesis
            using s2_1 s2_2 s2_3 s1_3 s1_2
                less_leq_trans by iprover
        qed
    have s1_5: "i \\in Int"
        using idom nat_in_int by auto
    have s1_6: "j \\in Int"
        proof -
        have s2_1: "k \\in Int"
            using s1_1 nat_in_int by auto
        have s2_2: "Succ[i] \\in Int"
            using idom succIsNat nat_in_int by auto
        have s2_3: "j = k + Succ[i]"
            using s1_1 by auto
        show ?thesis
            using s2_1 s2_2 s2_3 addIsInt by auto
        qed
    show ?thesis
        using s1_4 s1_5 s1_6 less_not_leq by auto
    qed


(*
negNatIsAdd0 ==
    negNat = {-.k + -.0:  k \in Nat}
PROOF
<1>1. negNat = {-.k:  k \in Nat}
    BY DEF negNat
<1>2. ASSUME NEW k \in Nat
      PROVE -.k + -.0 = -.k
    <2>1. -.k + -.0 = -.k + 0
        BY neg0
    <2>2. @ = -.k
        <3>1. -.k \in Int
            BY <1>2, minus_nat_in_int
        <3> QED
            BY <3>1, add_0
    <2> QED
        BY <2>1, <2>2
<1>3. {-.k:  k \in Nat} =
        (-.k + -.0:  k \in Nat}
    BY <1>2
<1> QED
    BY <1>1, <1>3
*)
theorem negNatIsAdd0:
    "negNat = {-.k + -.0:  k \\in Nat}"
    proof -
    have s1_1: "negNat = {-.k:  k \\in Nat}"
        unfolding negNat_def by auto
    have s1_2: "\<And> k.  k \\in Nat ==> -.k + -.0 = -.k"
        proof -
        fix "k" :: "c"
        assume s1_2_asm: "k \\in Nat"
        have s2_1: "-.k + -.0 = -.k + 0"
            using neg0 by auto
        also have s2_2: "... = -.k"
            proof -
            have s3_1: "-.k \\in Int"
                using s1_2_asm minus_nat_in_int by auto
            show ?thesis
                using s3_1 add_0 by auto
            qed
        finally show "-.k + -.0 = -.k" .
        qed
    have s1_3: "{-.k:  k \\in Nat} =
                {-.k + -.0:  k \\in Nat}"
        using s1_2 by auto
    show ?thesis
        using s1_1 s1_3 by auto
    qed


theorem negNatSplitAddi:
    assumes idom: "i \\in Nat"
    shows "{-.k + -.i:  k \\in Nat} =
            ({-.i} \<union> {-.k + -.Succ[i]:  k \\in Nat})"
    proof -
    have s1_1: "\<And> n.  (n \\in {-.k + -.i:  k \\in Nat})
        = (n \\in {-.i} \<union> {-.k + -.Succ[i]:  k \\in Nat})"
        proof -
        fix "n" :: "c"
        have s2_1: "n \\in {-.k + -.i:  k \\in Nat}
            = (\\E k \\in Nat:  n = -.k + -.i)"
            by auto
        also have s2_2: "... = (
            \\E k \\in ({0} \<union> {q + 1:  q \\in Nat}):
                n = -.k + -.i)"
            using SplitNat0 by auto
        also have s2_3: "... = (
            (\\E k \\in {0}:  n = -.k + -.i) \<or>
            (\\E k \\in {q + 1:  q \\in Nat}:  n = -.k + -.i)
            )"
            by auto
        also have s2_4: "... = (
            (n = -.0 + -.i) \<or>
            (\\E k:  (k \\in {q + 1:  q \\in Nat}) \<and> (n = -.k + -.i)))"
            by auto
        also have s2_5: "... = (
            (n = -.i) \<or>
            (\\E k:  (\\E q \\in Nat:  k = q + 1) \<and> n = -.k + -.i))"
            using idom minus_nat_in_int add_0_left by auto
        also have s2_6: "... = (
            (n = -.i) \<or>
            (\\E k:  \\E q \\in Nat:  k = q + 1 \<and> (n = -.k + -.i)))"
            by auto
        also have s2_7: "... = (
            (n = -.i) \<or>
            (\\E q \\in Nat:  n = -.(q + 1) + -.i))"
            by auto
        also have s2_8: "... = (
            (n = -.i) \<or>
            (\\E q \\in Nat:  n = -.q + -.Succ[i]))"
            proof -
            have s3_1: "\\E q \\in Nat:  n = -.(q + 1) + -.i ==>
                \\E q \\in Nat:  n = -.q + -.Succ[i]"
                proof -
                assume s3_1_asm: "\\E q \\in Nat:  n = -.(q + 1) + -.i"
                def P \<equiv> "\<lambda> x.  x \\in Nat \<and>
                    n = -.(x + 1) + -.i"
                def r \<equiv> "CHOOSE x:  P(x)"
                have s4_1: "r \\in Nat \<and> n = -.(r + 1) + -.i"
                    proof -
                    have s5_1: "\\E x:  P(x)"
                        using s3_1_asm by (auto simp: P_def)
                    have s5_2: "P(r)"
                        unfolding r_def
                        using s5_1 chooseI_ex[of P] by auto
                    show ?thesis
                        using s5_2 by (auto simp: P_def)
                    qed
                have s4_2: "n = (-.r + -.1) + -.i"
                    using s4_1 oneIsNat nat_in_int
                        MinusDistributesAdd_sequent by auto
                have s4_3: "n = -.r + (-.i + -.1)"
                    using s4_2 s4_1 idom oneIsNat nat_in_int minus_nat_in_int
                        AddAssociative_sequent AddCommutative_sequent by auto
                have s4_4: "n = -.r + -.(i + 1)"
                    using s4_3 idom oneIsNat nat_in_int
                        MinusDistributesAdd_sequent by auto
                have s4_5: "n = -.r + -.Succ[i]"
                    proof -
                    have s5_1: "Succ[i] = i + 1"
                        using idom nat_add_1 by fast
                    show ?thesis
                        using s5_1 s4_4 by auto
                    qed
                show "\\E q \\in Nat:  n = -.q + -.Succ[i]"
                    using s4_1 s4_5 by auto
                qed
            have s3_2: "\\E q \\in Nat:  n = -.q + -.Succ[i] ==>
                \\E q \\in Nat:  n = -.(q + 1) + -.i"
                proof -
                assume s3_2_asm: "\\E q \\in Nat:  n = -.q + -.Succ[i]"
                def P \<equiv> "\<lambda> x.  x \\in Nat \<and>
                    n = -.x + -.Succ[i]"
                def r \<equiv> "CHOOSE x:  P(x)"
                have s4_1: "r \\in Nat \<and> n = -.r + -.Succ[i]"
                    proof -
                    have s5_1: "\\E x:  P(x)"
                        using s3_2_asm by (auto simp: P_def)
                    have s5_2: "P(r)"
                        unfolding r_def
                        using s5_1 chooseI_ex[of P] by auto
                    show ?thesis
                        using s5_2 by (auto simp: P_def)
                    qed
                have s4_2: "n = -.r + -.(i + 1)"
                    proof -
                    have s5_1: "Succ[i] = i + 1"
                        using idom nat_add_1 by fast
                    show ?thesis
                        using s4_1 s5_1 by auto
                    qed
                have s4_3: "n = -.r + (-.i + -.1)"
                    using s4_2 idom oneIsNat nat_in_int
                        MinusDistributesAdd_sequent by auto
                have s4_4: "n = (-.r + -.1) + -.i"
                    using s4_3 s4_1 idom oneIsNat minus_nat_in_int
                        AddAssociative_sequent AddCommutative_sequent
                        by auto
                have s4_5: "n = -.(r + 1) + -.i"
                    using s4_4 s4_1 oneIsNat nat_in_int
                        MinusDistributesAdd_sequent by auto
                show "\\E q \\in Nat:  n = -.(q + 1) + -.i"
                    using s4_1 s4_5 by auto
                qed
            show ?thesis
                using s3_1 s3_2 by auto
            qed
        also have s2_9: "... = (
            (n \\in {-.i}) \<or>
            (n \\in {-.k + -.Succ[i]:  k \\in Nat}))"
            by auto
        also have s2_10: "... = (
            n \\in {-.i} \<union> {-.k + -.Succ[i]:  k \\in Nat})"
            by auto
        finally show "(n \\in {-.k + -.i:  k \\in Nat})
            = (n \\in {-.i} \<union> {-.k + -.Succ[i]:  k \\in Nat})" .
        qed
    have s1_2: "\<And> n.  (n \\in {-.k + -.i:  k \\in Nat})
        ==> (n \\in {-.i} \<union> {-.k + -.Succ[i]:  k \\in Nat})"
        using s1_1 by auto
    have s1_3: "\<And> n.  (n \\in {-.i} \<union> {-.k + -.Succ[i]:  k \\in Nat})
        ==> (n \\in {-.k + -.i:  k \\in Nat})"
        using s1_1 by auto
    show ?thesis
        using s1_2 s1_3 by (rule setEqualI, blast)
    qed


theorem LeqnegNatOpenInterval:
    assumes idom: "i \\in Nat" and
        jdom: "j \\in {-.k + -.Succ[i]:  k \\in Nat}"
    shows "~ (-.i <= j)"
    proof -
    def P \<equiv> "\<lambda> x.  x \\in Nat \<and> j = -.x + -.Succ[i]"
    def k \<equiv> "CHOOSE x:  P(x)"
    have s1_1: "k \\in Nat \<and> j = -.k + -.Succ[i]"
        proof -
        have s2_1: "\\E x:  P(x)"
            using jdom by (auto simp: P_def)
        have s2_2: "P(k)"
            unfolding k_def
            using s2_1 chooseI_ex[of P] by auto
        show ?thesis
            using s2_2 by (auto simp: P_def)
        qed
    have s1_types: "j \\in Int \<and> -.i \\in Int \<and>
        -.j \\in Int \<and> Succ[i] \\in Int \<and>
        -.k \\in Int \<and> -.Succ[i] \\in Int \<and>
        k \\in Int \<and> i \\in Int"
        proof -
        have s2_1: "k \\in Int"
            using s1_1 nat_in_int by auto
        have s2_2: "-.k \\in Int"
            using s2_1 neg_int_eq_int by auto
        have s2_3: "i \\in Int"
            using idom nat_in_int by auto
        have s2_4: "-.i \\in Int"
            using s2_3 neg_int_eq_int by auto
        have s2_5: "Succ[i] \\in Int"
            using idom succIsNat nat_in_int by auto
        have s2_6: "-.Succ[i] \\in Int"
            using s2_5 neg_int_eq_int by auto
        have s2_7: "j \\in Int"
            proof -
            have s2_1: "j = -.k + -.Succ[i]"
                using s1_1 by auto
            show ?thesis
                using s2_1 s2_2 s2_6 addIsInt by auto
            qed
        have s2_8: "-.j \\in Int"
            using s2_7 neg_int_eq_int by auto
        show ?thesis
            using s2_1 s2_2 s2_3 s2_4 s2_5
                s2_6 s2_7 s2_8 by auto
        qed
    have s1_2: "Succ[i] <= -.j"
        proof -
        have s2_1: "Succ[i] + k = -.j"
            proof -
            have s3_1: "j = -.k + -.Succ[i]"
                using s1_1 by auto
            have s3_2: "-.j + j = -.j + (-.k + -.Succ[i])"
                using s3_1 by auto
            have s3_3: "0 = -.j + (-.k + -.Succ[i])"
                using s3_2 s1_types AddNegCancels_left by auto
            have s3_4: "0 + Succ[i] = (-.j + (-.k + -.Succ[i])) + Succ[i]"
                using s3_3 by auto
            have s3_5: "0 + Succ[i] = ((-.j + -.k) + -.Succ[i]) + Succ[i]"
                using s3_4 s1_types AddAssociative_sequent by auto
            have s3_6: "0 + Succ[i] = (-.j + -.k) + (-.Succ[i] + Succ[i])"
                using s3_5 s1_types addIsInt AddAssociative_sequent by auto
            have s3_7: "Succ[i] = (-.j + -.k) + (-.Succ[i] + Succ[i])"
                proof -
                have s4_1: "Succ[i] \\in Int"
                    using s1_types by auto
                have s4_2: "0 + Succ[i] = Succ[i]"
                    using s4_1 add_0_left by fast
                show ?thesis
                    using s3_6 s4_2 by auto
                qed
            have s3_8: "Succ[i] = (-.j + -.k) + 0"
                using s3_7 s1_types AddNegCancels_left by auto
            have s3_9: "Succ[i] = -.j + -.k"
                proof -
                have s4_1: "-.j + -.k \\in Int"
                    using s1_types addIsInt by auto
                show ?thesis
                    using s3_8 s4_1 add_0 by auto
                qed
            have s3_10: "Succ[i] + k = (-.j + -.k) + k"
                using s3_9 by auto
            have s3_11: "Succ[i] + k = -.j + (-.k + k)"
                using s3_10 s1_types AddAssociative_sequent by auto
            have s3_12: "Succ[i] + k = -.j + 0"
                using s3_11 s1_types AddNegCancels_left by auto
            show ?thesis
                using s3_12 s1_types add_0 by auto
            qed
        have s2_2: "\\E r \\in Nat:  Succ[i] + r = -.j"
            using s1_1 s2_1 by auto
        show ?thesis
            unfolding leq_def
            using s2_2 by auto
        qed
    have s1_3: "i < Succ[i]"
        using idom less_succ_nat by fast
    have s1_4: "i < -.j"
        using s1_types s1_2 s1_3 less_leq_trans by auto
    have s1_5: "j < -.i"
        proof -
        have s2_1: "-.-.j < -.i"
            proof -
            have s3_1: "i \\in Int"
                using s1_types by auto
            have s3_2: "-.j \\in Int"
                using s1_types by auto
            show ?thesis
                using s3_1 s3_2 s1_4 minus_less by auto
            qed
        have s2_2: "-.-.j = j"
            using s1_types minus_involutive by auto
        show ?thesis
            using s2_1 s2_2 by auto
        qed
    show ?thesis
        using s1_5 s1_types less_not_leq by auto
    qed


theorem split_interval_nat_negnat:
    shows "{k \\in Int:  a <= k \<and> k <= b} =
     {k \\in negNat:  a <= k \<and> k <= b} \<union>
     {k \\in Nat:  a <= k \<and> k <= b}"
    using int_union_nat_negnat by auto


end
