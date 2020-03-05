(*  Copyright 2009 INRIA  *)

open Printf;;

(* obsolete functions (?)
let print_case_expr n other oc =
  assert (n > 0);
  fprintf oc "CASE c1x -> e1x";
  if n > 1 then for i = 2 to n do
    fprintf oc " [] c%dx -> e%dx" i i;
  done;
  if other then fprintf oc " [] OTHER -> oth";
;;

let print_case_branch i oc = fprintf oc "c%dx ==> P (e%dx) ==> FALSE" i i;;

let print_case_branch_other n other oc =
  for i = 1 to n do fprintf oc "~c%dx ==> " i; done;
  if other then fprintf oc "P (oth) ==> ";
  fprintf oc "FALSE";
;;

let print_seq n sep letter oc =
  assert (n > 0);
  fprintf oc "%s1x" letter;
  if n > 1 then for i = 2 to n do
    fprintf oc "%s%s%dx" sep letter i;
  done;
;;
*)

let tpl_case = "
  \"!! P @@@c1x e1x c2x e2x... .
    P (CASE @@@c1x -> e1x [] c2x -> e2x...) ==>
@@@
    (c1x ==> P (e1x) ==> FALSE) ==>
    (c2x ==> P (e2x) ==> FALSE) ==>
...
    (...~c2x & ~c1x@@@ & TRUE ==> FALSE) ==>
    FALSE\"
proof -
  fix P @@@c1x e1x c2x e2x...
  assume h: \"P (CASE @@@c1x -> e1x [] c2x -> e2x...)\"
            (is \"P (?cas)\")
@@@
  assume h1: \"c1x ==> P (e1x) ==> FALSE\"
  assume h2: \"c2x ==> P (e2x) ==> FALSE\"
...
  assume hoth: \"...~c2x & ~c1x@@@ & TRUE ==> FALSE\"
  def cs == \"<<@@@c1x, c2x...>>\" (is \"?cs\")
  def es == \"<<@@@e1x, e2x...>>\" (is \"?es\")
  def arms == \"UNION {CaseArm (?cs[i], ?es[i]) : i \\\\in DOMAIN ?cs}\"
              (is \"?arms\")
  def cas == \"?cas\"
  have h0: \"P (cas)\" using h by (fold cas_def)
  def dcs == \"...c2x | c1x@@@\" (is \"?dcs\")
  show FALSE
  proof (rule zenon_em [of \"?dcs\"])
    assume ha: \"~(?dcs)\"
@@@
    have hh1: \"~c1x\" using ha by blast
    have hh2: \"~c2x\" using ha by blast
...
    show FALSE
      using hoth @@@hh1 hh2... by blast
  next
    assume ha: \"?dcs\"
    def scs == \"zenon_seqify (@@@zenon_appseq (zenon_appseq (...
                               <<>>, @@@c1x), c2x)...)\"
               (is \"?scs\")
    def ses == \"zenon_seqify (@@@zenon_appseq (zenon_appseq (...
                               <<>>, @@@e1x), e2x)...)\"
               (is \"?ses\")
    have ha1: \"\\<exists> i \\<in> DOMAIN ?scs : ?scs[i]\"
      using ha zenon_case_seq_empty
      by (simp only: zenon_case_seq_simpl zenon_seqify_empty, blast)
    have ha2: \"\\<exists> i \\<in> DOMAIN ?cs : ?cs[i]\"
      using ha1 by (simp only: zenon_seqify_appseq zenon_seqify_empty)
    have hb: \"\\\\E x : x \\\\in arms\"
      using zenon_case_domain [OF ha2, where es = \"?es\"]
      by (unfold arms_def, blast)
    have hc: \"(CHOOSE x : x \\\\in arms) \\\\in arms\"
      using hb by (unfold Ex_def, auto)
    have hf0: \"?cas \\\\in arms\"
      using hc by (unfold arms_def, fold Case_def)
    have hf3: \"cas \\\\in UNION {CaseArm (?scs[i], ?ses[i])
                                  : i \\\\in DOMAIN ?scs}\"
              (is \"?hf3\")
      using hf0 by (fold cas_def, unfold arms_def,
                    simp only: zenon_seqify_appseq zenon_seqify_empty)
    have hf4: \"Len (?scs) = Len (?ses)\" (is \"?hf4\")
      by (simp only: zenon_case_len_simpl)
    have hf5: \"?hf4 & ?hf3\"
      by (rule conjI [OF hf4 hf3])
    have hf: \"
               ...cas \\\\in CaseArm (c2x, e2x)
             | cas \\\\in CaseArm (c1x, e1x)@@@
             | cas \\\\in UNION {CaseArm (zenon_seqify (<<>>)[i],
                                          zenon_seqify (<<>>)[i])
                                 : i \\\\in DOMAIN zenon_seqify (<<>>)}
             \" (is \"_ | ?gxx\")
      using hf5 by (simp only: zenon_case_union_simpl, blast)
@@@
    have hg1x: \"cas \\\\in CaseArm (c1x, e1x) => FALSE\"
      using h0 h1 by auto
    have hg2x: \"cas \\\\in CaseArm (c2x, e2x) => FALSE\"
      using h0 h2 by auto
...
    from hf
    have hh0: \"?gxx\" ...(is \"_ | ?g1\")
      by (rule zenon_disjE1 [OF _ hg3x])
    then have hh1: \"?g1\" (is \"_ | ?g0\")
      by (rule zenon_disjE1 [OF _ hg2x])
    then have hh0: \"?g0\"@@@[n-1]
      by (rule zenon_disjE1 [OF _ hg1x])
    have hi: \"cas \\\\in UNION {CaseArm (<<>>[i], <<>>[i])
                                 : i \\\\in DOMAIN <<>>}\"
      using hh0 by (simp only: zenon_seqify_empty)
    show FALSE
      by (rule zenon_case_empty_union [OF hi])
  qed
qed
";;

let tpl_case_other = "
  \"!! P oth @@@c1x e1x c2x e2x... .
    P (CASE @@@c1x -> e1x [] c2x -> e2x... [] OTHER -> oth) ==>
@@@
    (c1x ==> P (e1x) ==> FALSE) ==>
    (c2x ==> P (e2x) ==> FALSE) ==>
...
    (...~c2x & ~c1x@@@ & TRUE ==> P (oth) ==> FALSE) ==>
    FALSE\"
proof -
  fix P oth @@@c1x e1x c2x e2x...
  assume h: \"P (CASE @@@c1x -> e1x [] c2x -> e2x... [] OTHER -> oth)\"
            (is \"P (?cas)\")
@@@
  assume h1: \"c1x ==> P (e1x) ==> FALSE\"
  assume h2: \"c2x ==> P (e2x) ==> FALSE\"
...
  assume hoth: \"...~c2x & ~c1x@@@ & TRUE ==> P (oth) ==> FALSE\"
  def cs == \"<<@@@c1x, c2x...>>\" (is \"?cs\")
  def es == \"<<@@@e1x, e2x...>>\" (is \"?es\")
  def arms == \"UNION {CaseArm (?cs[i], ?es[i]) : i \\\\in DOMAIN ?cs}\"
              (is \"?arms\")
  def cas == \"?cas\"
  have h0: \"P (cas)\" using h by (fold cas_def)
  def dcs == \"...c2x | c1x@@@ | FALSE\" (is \"?dcs\")
  def scs == \"zenon_seqify (@@@zenon_appseq (zenon_appseq (...
                             <<>>, @@@c1x), c2x)...)\"
             (is \"?scs\")
  have hscs : \"?cs = ?scs\"
    by (simp only: zenon_seqify_appseq zenon_seqify_empty)
  def ses == \"zenon_seqify (@@@zenon_appseq (zenon_appseq (...
                             <<>>, @@@e1x), e2x)...)\"
             (is \"?ses\")
  have hses : \"?es = ?ses\"
    by (simp only: zenon_seqify_appseq zenon_seqify_empty)
  have hlen: \"Len (?scs) = Len (?ses)\" (is \"?hlen\")
    by (simp only: zenon_case_len_simpl)
  def armoth == \"CaseArm (\\<forall> i \\<in> DOMAIN ?cs : ~?cs[i], oth)\"
                (is \"?armoth\")
  show FALSE
  proof (rule zenon_em [of \"?dcs\"])
    assume ha: \"~(?dcs)\"
    have hb: \"P (CHOOSE x : x \\\\in arms \\<union> armoth)\"
      using h by (unfold CaseOther_def, fold arms_def armoth_def)
    have hc: \"arms \\\\cup armoth
              = UNION {CaseArm (?scs[i], ?ses[i]) : i \\\\in DOMAIN ?scs}
                \\\\cup CaseArm (\\<forall> i \\<in> DOMAIN ?scs : ~?scs[i],
                                 oth)\"
             (is \"_ = ?sarmsoth\")
      using hscs hses by (unfold arms_def armoth_def, auto)
    have hd: \"~(?dcs) & ?hlen & arms \\<union> armoth = ?sarmsoth\"
      using ha hlen hc by blast
    have he: \"arms \\<union> armoth = {oth}\"
      using hd by (simp only: zenon_case_oth_simpl zenon_case_oth_empty)
    have hf: \"(CHOOSE x : x \\\\in arms \\\\cup armoth) = oth\"
      using he by auto
    have hg: \"P (oth)\"
      using hb hf by auto
@@@
    have hh1: \"~c1x\" using ha by blast
    have hh2: \"~c2x\" using ha by blast
...
    show FALSE
      using hg hoth @@@hh1 hh2... by blast
  next
    assume ha: \"?dcs\"
    have ha1: \"\\<exists> i \\<in> DOMAIN ?scs : ?scs[i]\"
      using ha zenon_case_seq_empty
      by (simp only: zenon_case_seq_simpl zenon_seqify_empty, blast)
    have ha2: \"\\<exists> i \\<in> DOMAIN ?cs : ?cs[i]\"
      using ha1 hscs by auto
    have ha3: \"~ (\\<forall> i \\<in> DOMAIN ?cs : ~?cs[i])\"
      using ha2 by blast
    have ha4: \"armoth = {}\"
      using ha3 condElse [OF ha3, where t = \"{oth}\" and e = \"{}\"]
      by (unfold armoth_def CaseArm_def, blast)
    have hb: \"\\\\E x : x \\\\in arms \\\\cup armoth\"
      using zenon_case_domain [OF ha2, where es = \"?es\"]
      by (unfold arms_def, blast)
    have hc: \"(CHOOSE x : x \\\\in arms \\\\cup armoth)
               \\\\in arms \\\\cup armoth\"
      using hb by (unfold Ex_def, auto)
    have hf0: \"?cas \\\\in arms \\\\cup armoth\"
      using hc by (unfold arms_def armoth_def, fold CaseOther_def)
    have hf1: \"cas \\\\in arms \\\\cup armoth\"
      using hf0 by (fold cas_def)
    have hf2: \"cas \\\\in arms\"
      using hf1 ha4 by auto
    have hf3: \"cas \\\\in UNION {CaseArm (?scs[i], ?ses[i])
                                  : i \\\\in DOMAIN ?scs}\"
              (is \"?hf3\")
      using hf2 by (unfold arms_def,
                    simp only: zenon_seqify_appseq zenon_seqify_empty)
    have hf5: \"?hlen & ?hf3\"
      by (rule conjI [OF hlen hf3])
    have hf: \"
               ...cas \\\\in CaseArm (c2x, e2x)
             | cas \\\\in CaseArm (c1x, e1x)@@@
             | cas \\\\in UNION {CaseArm (zenon_seqify (<<>>)[i],
                                          zenon_seqify (<<>>)[i])
                                 : i \\\\in DOMAIN zenon_seqify (<<>>)}
             \" (is \"_ | ?gxx\")
      using hf5 by (simp only: zenon_case_union_simpl, blast)
@@@
    have hg1x: \"cas \\\\in CaseArm (c1x, e1x) => FALSE\"
      using h0 h1 by auto
    have hg2x: \"cas \\\\in CaseArm (c2x, e2x) => FALSE\"
      using h0 h2 by auto
...
    from hf
    have hh0: \"?gxx\" ...(is \"_ | ?g1\")
      by (rule zenon_disjE1 [OF _ hg3x])
    then have hh1: \"?g1\" (is \"_ | ?g0\")
      by (rule zenon_disjE1 [OF _ hg2x])
    then have hh0: \"?g0\"@@@[n-1]
      by (rule zenon_disjE1 [OF _ hg1x])
    have hi: \"cas \\\\in UNION {CaseArm (<<>>[i], <<>>[i])
                                 : i \\\\in DOMAIN <<>>}\"
      using hh0 by (simp only: zenon_seqify_empty)
    show FALSE
      by (rule zenon_case_empty_union [OF hi])
  qed
qed
";;

let print_case kind n other oc =
  assert (n > 0);
  fprintf oc "%s zenon_case%s%d :" kind (if other then "other" else "") n;
  let tpl = if other then tpl_case_other else tpl_case in
  output_string oc (Enum.expand_text n tpl);
;;

let tpl_record n = sprintf "
  \"!! r @@@l1x s1x l2x s2x... .
    isAFcn (r) ==>
    DOMAIN r = {@@@l1x, l2x...} ==>
@@@
    r[l1x] \\\\in s1x ==>
    r[l2x] \\\\in s2x ==>
...
    r \\\\in [@@@l1x : s1x, l2x : s2x...]\"
proof -
  fix r @@@l1x s1x l2x s2x...
  assume hfcn: \"isAFcn (r)\"
  assume hdom: \"DOMAIN r = {@@@l1x, l2x...}\"
@@@
  assume h1: \"r[l1x] \\\\in s1x\"
  assume h2: \"r[l2x] \\\\in s2x\"
...
  let ?doms = \"<<@@@l1x, l2x...>>\"
  let ?domset = \"{@@@l1x, l2x...}\"
  let ?domsetrev = \"{...l2x, l1x@@@}\"
  let ?rngs = \"<<@@@s1x, s2x...>>\"
  let ?n0n = \"0\"
@@@
  let ?n1n = \"Succ[?n0n]\"
  let ?n2n = \"Succ[?n1n]\"
...
  let ?indices = \"{...?n2n, ?n1n@@@}\"
  have hdomx : \"?domsetrev = DOMAIN r\"
  by (rule zenon_set_rev_1, (rule zenon_set_rev_2)+, rule zenon_set_rev_3,
      rule hdom)
  show \"r \\\\in EnumFuncSet (?doms, ?rngs)\"
  proof (rule EnumFuncSetI [of r, OF hfcn])
    have hx1: \"isASeq (?doms) & ?domsetrev = Range (?doms)\"
    by ((rule zenon_range_2)+, rule zenon_range_1)
    have hx2: \"?domsetrev = Range (?doms)\"
    by (rule conjD2 [OF hx1])
    show \"DOMAIN r = Range (?doms)\"
    by (rule subst [where P = \"%%x. x = Range (?doms)\", OF hdomx hx2])
  next
    show \"DOMAIN ?rngs = DOMAIN ?doms\"
    by (rule zenon_tuple_dom_3, (rule zenon_tuple_dom_2)+,
        rule zenon_tuple_dom_1)
  next
    have hdomseq: \"isASeq (?doms)\" by auto
    have hindx: \"isASeq (?doms) & ?n%dn = Len (?doms)
                  & ?indices = DOMAIN ?doms\"
    by (simp only: DomainSeqLen [OF hdomseq], (rule zenon_dom_app_2)+,
        rule zenon_dom_app_1)
    have hind: \"?indices = DOMAIN ?doms\" by (rule conjE [OF hindx], elim conjE)
    show \"ALL i in DOMAIN ?doms : r[?doms[i]] \\\\in ?rngs[i]\"
    proof (rule subst [OF hind], (rule zenon_all_rec_2)+, rule zenon_all_rec_1)
@@@
      have hn: \"l1x = ?doms[?n1n]\"
      by (((rule zenon_tuple_acc_2, safe, simp only: zenon_ss_1 zenon_ss_2,
            rule zenon_zero_lt,
            simp only: zenon_ss_1 zenon_ss_2 zenon_sa_1 zenon_sa_2,
            ((rule zenon_ss_le_sa_2)+)?, rule zenon_ss_le_sa_1
           )+)?,
          rule zenon_tuple_acc_1, auto)
      have hs: \"s1x = ?rngs[?n1n]\"
      by (((rule zenon_tuple_acc_2, safe, simp only: zenon_ss_1 zenon_ss_2,
            rule zenon_zero_lt,
            simp only: zenon_ss_1 zenon_ss_2 zenon_sa_1 zenon_sa_2,
            ((rule zenon_ss_le_sa_2)+)?, rule zenon_ss_le_sa_1
           )+)?,
          rule zenon_tuple_acc_1, auto)
      show \"r[?doms[?n1n]] \\\\in ?rngs[?n1n]\"
      by (rule subst[OF hs], rule subst[OF hn], rule h1)
    next
      have hn: \"l2x = ?doms[?n2n]\"
      by (((rule zenon_tuple_acc_2, safe, simp only: zenon_ss_1 zenon_ss_2,
            rule zenon_zero_lt,
            simp only: zenon_ss_1 zenon_ss_2 zenon_sa_1 zenon_sa_2,
            ((rule zenon_ss_le_sa_2)+)?, rule zenon_ss_le_sa_1
           )+)?,
          rule zenon_tuple_acc_1, auto)
      have hs: \"s2x = ?rngs[?n2n]\"
      by (((rule zenon_tuple_acc_2, safe, simp only: zenon_ss_1 zenon_ss_2,
            rule zenon_zero_lt,
            simp only: zenon_ss_1 zenon_ss_2 zenon_sa_1 zenon_sa_2,
            ((rule zenon_ss_le_sa_2)+)?, rule zenon_ss_le_sa_1
           )+)?,
          rule zenon_tuple_acc_1, auto)
      show \"r[?doms[?n2n]] \\\\in ?rngs[?n2n]\"
      by (rule subst[OF hs], rule subst[OF hn], rule h2)
...
    qed
  qed
qed
" n
;;

let print_record kind n oc =
  assert (n > 0);
  fprintf oc "%s zenon_inrecordsetI%d :" kind n;
  let tpl = tpl_record n in
  output_string oc (Enum.expand_text n tpl);
;;

(* ===================== test functions ================== *)

let print_case_up_to n file =
  let oc = open_out file in
  for i = 1 to n do
    print_case "lemma" i false oc;
    fprintf oc "\n";
    print_case "lemma" i true oc;
    fprintf oc "\n";
  done;
  close_out oc;
;;

let test_case n other =
  let oc = open_out "/tmp/testcase.thy" in
  fprintf oc "theory testcase\n";
  fprintf oc "imports Zenon\n";
  fprintf oc "begin\n\n";
  print_case "lemma" n other oc;
  fprintf oc "end\n";
  close_out oc;
  fprintf stderr "Now run:\n";
  fprintf stderr "time isabelle-process -r \
                       -e \"(use_thy \\\"/tmp/testcase\\\"; \
                             OS.Process.exit OS.Process.success);\" TLA+\n";
  flush stderr;
;;

let print_record_up_to n file =
  let oc = open_out file in
  for i = 1 to n do
    print_record "lemma" i oc;
    fprintf oc "\n";
  done;
  close_out oc;
;;

let test_record n =
  let oc = open_out "/tmp/testrecord.thy" in
  fprintf oc "theory testrecord\n";
  fprintf oc "imports Zenon\n";
  fprintf oc "begin\n\n";
  print_record "lemma" n oc;
  fprintf oc "end\n";
  close_out oc;
  fprintf stderr "Now run:\n";
  fprintf stderr "time isabelle-process -r \
                       -e \"(use_thy \\\"/tmp/testrecord\\\"; \
                             OS.Process.exit OS.Process.success);\" TLA+\n";
  flush stderr;
;;
