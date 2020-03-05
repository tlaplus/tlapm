(*  Title:      TLA+/AtomicBakery.thy
    Author:     Hernan Vanzetto, LORIA
    Copyright (C) 2009-2011  INRIA and Microsoft Corporation
    License:    BSD
    Version:    Isabelle2011-1
    Time-stamp: <2011-10-11 17:37:50 merz>
*)

theory AtomicBakeryG
imports Constant
begin

(**************************************************

\<midarrow>algorithm AtomicBakery { 
variable num = [i \<in> P \<mapsto> 0], flag = [i \<in> P \<mapsto> FALSE];

process (p \<in> P) 
  variables unread, max, nxt { 
p1 : while (TRUE){ 
       unread := P \ {self}; 
       max := 0; 
       flag [self] := TRUE;
p2 :   while (unread \<noteq> {}){ 
         with (i \<in> unread){
           unread := unread \ {i}; 
           IF (num[i] > max) { max := num[i]; } 
         } 
       }; 
p3 :   num[self] := max + 1; 
p4 :   flag[self] := FALSE; 
       unread := P \ {self}; 
p5 :   while (unread \<noteq> {}){ 
         with (i \<in> unread){ nxt := i; }; 
         await \<not>flag[nxt]; 
p6 :       await \<or> num[nxt] = 0 
             \<or> IF self > nxt 
                 THEN num[nxt] > num[self]
                 ELSE num[nxt] \<ge> num[self]; 
         unread := unread \ {nxt}; 
       }; 
p7 :   skip ; \\<ast> critical section ; 
p8 :   num[self] := 0; 
    }
  } 
} 

**************************************************)

consts
  P :: "c"
  defaultInitValue :: "c"

axiomatization where
  PInNat: "P \<subseteq> Nat"

abbreviation ProcSet where
  "ProcSet \<equiv> P"

definition Init where
  "Init(unread,max,flag,pc,num,nxt) \<equiv>
            num = [i \<in> P \<mapsto> 0]
          \<and> flag = [i \<in> P \<mapsto> FALSE]
          \<and> unread = [self \<in> P \<mapsto> defaultInitValue ] 
          \<and> max = [self \<in> P \<mapsto> defaultInitValue ] 
          \<and> nxt = [self \<in> P \<mapsto> defaultInitValue ] 
          \<and> pc = [self \<in> ProcSet \<mapsto> ''p1'']"

(* alternative definition for simplifying the reasoning:
definition Init where
  "Init(unread,max,flag,pc,num,nxt) \<equiv>
            num = [i \<in> P \<mapsto> 0]
          \<and> flag = [i \<in> P \<mapsto> FALSE]
          \<and> unread \<in> [P \<rightarrow> SUBSET P ] 
          \<and> max \<in> [P \<rightarrow> Nat ] 
          \<and> nxt \<in> [P \<rightarrow> P ] 
          \<and> pc = [self \<in> ProcSet \<mapsto> ''p1'']"
*)

definition p1 where
 "p1(self,unread,max,flag,pc,num,nxt,unread',max',flag',pc',num',nxt') \<equiv>
               pc[self] = ''p1''
             \<and> unread' = [unread EXCEPT ![self] = P \\ {self}]
             \<and> max' = [max EXCEPT ![self] = 0]
             \<and> flag' = [flag EXCEPT ![self] = TRUE]
             \<and> pc' = [pc EXCEPT ![self] = ''p2'']
             \<and> num' = num \<and> nxt' = nxt"

definition p2 where
  "p2(self,unread,max,flag,pc,num,nxt,unread',max',flag',pc',num',nxt') \<equiv>
                pc[self] = ''p2'' 
              \<and> (IF unread[self] \<noteq> {}
                  THEN \<exists>i \<in> unread[self] : 
                       (  unread' = [unread EXCEPT ![self] = unread[self] \\ {i}]
                        \<and> (IF num[i] > max[self] 
                             THEN max' = [max EXCEPT ![self] = num[i]] 
                             ELSE (max' = max)))
                        \<and> pc' = [pc EXCEPT ![self] = ''p2'']
                  ELSE   pc' = [pc EXCEPT ![self] = ''p3''] 
                       \<and> unread' = unread \<and> max' = max)
              \<and> num' = num \<and> flag' = flag \<and> nxt' = nxt"

definition p3 where
  "p3(self,unread,max,flag,pc,num,nxt,unread',max',flag',pc',num',nxt') \<equiv>
                pc[self] = ''p3''
              \<and> num' = [num EXCEPT ![self] = max[self] + 1] 
              \<and> pc' = [pc EXCEPT ![self] = ''p4''] 
              \<and> flag' = flag \<and> unread' = unread \<and> max' = max \<and> nxt' = nxt"

definition p4 where
  "p4(self,unread,max,flag,pc,num,nxt,unread',max',flag',pc',num',nxt') \<equiv>
                pc[self] = ''p4'' 
              \<and> flag' = [flag EXCEPT ![self] = FALSE] 
              \<and> unread' = [unread EXCEPT ![self] = P \\ {self}] 
              \<and> pc' = [pc EXCEPT ![self] = ''p5''] 
              \<and> num' = num \<and> max' = max \<and> nxt' = nxt"

definition p5 where
  "p5(self,unread,max,flag,pc,num,nxt,unread',max',flag',pc',num',nxt') \<equiv>
                pc[self] = ''p5'' 
              \<and> (IF unread[self] \<noteq> {} 
                   THEN   (\<exists>i \<in> unread[self] : nxt' = [nxt EXCEPT ![self] = i])
                        \<and> \<not>flag[nxt'[self]] 
                        \<and> pc' = [pc EXCEPT ![self] = ''p6''] 
                   ELSE   pc' = [pc EXCEPT ![self] = ''p7''] 
                        \<and> nxt' = nxt)
              \<and> num' = num \<and> flag' = flag \<and> unread' = unread \<and> max' = max"

definition p6 where
  "p6(self,unread,max,flag,pc,num,nxt,unread',max',flag',pc',num',nxt') \<equiv>
                pc[self] = ''p6'' 
              \<and> ( num[nxt[self]] = 0 
                \<or> (IF self > nxt[self] 
                     THEN num[nxt[self]] > num[self]
                     ELSE num[nxt[self]] \<ge> num[self]))
              \<and> unread' = [unread EXCEPT ![self] = unread[self] \\ {nxt[self]}] 
              \<and> pc' = [pc EXCEPT ![self] = ''p5''] 
              \<and> num' = num \<and> flag' = flag \<and> max' = max \<and> nxt' = nxt"

definition p7 where  -- {* Critical section *}
  "p7(self,unread,max,flag,pc,num,nxt,unread',max',flag',pc',num',nxt') \<equiv>
                pc[self] = ''p7'' 
              \<and> TRUE 
              \<and> pc' = [pc EXCEPT ![self] = ''p8''] 
              \<and> num' = num \<and> flag' = flag \<and> unread' = unread \<and> max' = max \<and> nxt' = nxt"

definition p8 where
  "p8(self,unread,max,flag,pc,num,nxt,unread',max',flag',pc',num',nxt') \<equiv>
                pc[self] = ''p8'' 
              \<and> num' = [num EXCEPT ![self] = 0] 
              \<and> pc' = [pc EXCEPT ![self] = ''p1''] 
              \<and> flag' = flag \<and> unread' = unread \<and> max' = max \<and> nxt' = nxt"

definition p where
  "p(self,unread,max,flag,pc,num,nxt,unread',max',flag',pc',num',nxt') \<equiv>
    p1(self,unread,max,flag,pc,num,nxt,unread',max',flag',pc',num',nxt') 
  \<or> p2(self,unread,max,flag,pc,num,nxt,unread',max',flag',pc',num',nxt') 
  \<or> p3(self,unread,max,flag,pc,num,nxt,unread',max',flag',pc',num',nxt') 
  \<or> p4(self,unread,max,flag,pc,num,nxt,unread',max',flag',pc',num',nxt') 
  \<or> p5(self,unread,max,flag,pc,num,nxt,unread',max',flag',pc',num',nxt')
  \<or> p6(self,unread,max,flag,pc,num,nxt,unread',max',flag',pc',num',nxt')
  \<or> p7(self,unread,max,flag,pc,num,nxt,unread',max',flag',pc',num',nxt')
  \<or> p8(self,unread,max,flag,pc,num,nxt,unread',max',flag',pc',num',nxt')"

definition Next where
 "Next(unread,max,flag,pc,num,nxt,unread',max',flag',pc',num',nxt') \<equiv>   (\<exists> self \<in> P : 
            p(self,unread,max,flag,pc,num,nxt,unread',max',flag',pc',num',nxt')) 
         \<or> (  (\<forall> self \<in> ProcSet : pc[self] = ''Done'') 
            \<and> num' = num \<and> flag' = flag \<and> pc' = pc 
              \<and> unread' = unread \<and> max' = max \<and> nxt' = nxt)"

(*
definition Spec where
  "Spec \<equiv> Init \<and> []([Next]_{vars})" 

definition Termination where
  "Termination \<equiv> <>(\<forall> self \<in> ProcSet : pc[self] = ''Done'')" 
*)
 
definition MutualExclusion where
  "MutualExclusion(pc) \<equiv> \<forall>i,j \<in> P : (i \<noteq> j) \<Rightarrow> \<not>(pc[i] = ''p7'' \<and> pc[j] = ''p7'')"

(*---------------------------------------------------------------------------*)

definition TypeOK where
  "TypeOK(unread,max,flag,pc,num,nxt) \<equiv>
              num \<in> [P \<rightarrow> Nat] 
            \<and> flag \<in> [P \<rightarrow> BOOLEAN] 
            \<and> unread \<in> [P \<rightarrow> SUBSET P \<union> {defaultInitValue}]
            \<and> (\<forall>i \<in> P :
                pc[i] \<in> {''p2'', ''p5'', ''p6''} \<Rightarrow>   unread[i] \<subseteq> P 
                                                    \<and> i \<notin> unread[i])
            \<and> max \<in> [P \<rightarrow> Nat \<union> {defaultInitValue}] 
            \<and> (\<forall>j \<in> P : (pc[j] \<in> {''p2'', ''p3''}) \<Rightarrow> max[j] \<in> Nat)
            \<and> nxt \<in> [P \<rightarrow> P \<union> {defaultInitValue}] 
            \<and> (\<forall>i \<in> P : (pc[i] = ''p6'') \<Rightarrow> nxt[i] \<in> P \\ {i})
            \<and> pc \<in> [P \<rightarrow> {''p1'',''p2'',''p3'',''p4'',''p5'',''p6'',''p7'',''p8''}]"
--{* The type invariant in p6 should be
            @{text "\<and> (\<forall>i \<in> P : (pc[i] = ''p6'') \<Rightarrow> nxt[i] \<in> unread[i] \\ {i})"}
  but it works anyway as it is.
*}

(**
definition TypeOK where (** version for the alternative initial condition **)
  "TypeOK(unread,max,flag,pc,num,nxt) \<equiv>
              num \<in> [P \<rightarrow> Nat] 
            \<and> flag \<in> [P \<rightarrow> BOOLEAN] 
            \<and> unread \<in> [P \<rightarrow> SUBSET P]
            \<and> (\<forall>i \<in> P :
                pc[i] \<in> {''p2'', ''p5'', ''p6''} \<Rightarrow> i \<notin> unread[i])
            \<and> max \<in> [P \<rightarrow> Nat]
            \<and> nxt \<in> [P \<rightarrow> P]
            \<and> (\<forall>i \<in> P : (pc[i] = ''p6'') \<Rightarrow> nxt[i] \<noteq> i)
            \<and> pc \<in> [P \<rightarrow> {''p1'',''p2'',''p3'',''p4'',''p5'',''p6'',''p7'',''p8''}]"
--{* The type invariant in p6 should be
            @{text "\<and> (\<forall>i \<in> P : (pc[i] = ''p6'') \<Rightarrow> nxt[i] \<in> unread[i] \\ {i})"}
  but it works anyway as it is.
*}
**)

definition GG where
  "GG(j,i, num) \<equiv> IF j > i THEN num[i] > num[j] ELSE num[i] \<ge> num[j]"

definition After where
  "After(i,j,unread,max,flag,pc,num,nxt) \<equiv>
                  num[j] > 0 
                \<and> (  pc[i] = ''p1'' 
                   \<or> (  pc[i] = ''p2'' 
                      \<and> (  j \<in> unread[i] 
                         \<or> max[i] \<ge> num[j]))
                   \<or> (  pc[i] = ''p3'' 
                      \<and> max[i] \<ge> num[j])
                   \<or> (  pc[i] \<in> {''p4'', ''p5'', ''p6''} 
                      \<and> GG(j,i, num)
                      \<and> (pc[i] \<in> {''p5'', ''p6''} \<Rightarrow> j \<in> unread[i])))"

definition IInv where
  "IInv(i,unread,max,flag,pc,num,nxt) \<equiv>
               ((num[i] = 0) = (pc[i] \<in> {''p1'', ''p2'', ''p3''}))
             \<and> (flag[i] = (pc[i] \<in> {''p2'', ''p3'', ''p4''}))
             \<and> (pc[i] \<in> {''p5'', ''p6''} \<Rightarrow> 
                 (\<forall>j \<in> (P \\ unread[i]) \\ {i} : After(j,i,unread,max,flag,pc,num,nxt)))
             \<and> ( pc[i] = ''p6''
               \<and> ( (pc[nxt[i]] = ''p2'') \<and> i \<notin> unread[nxt[i]]
                 \<or> (pc[nxt[i]] = ''p3''))
               \<Rightarrow> max[nxt[i]] \<ge> num[i])
             \<and> ((pc[i] \<in> {''p7'', ''p8''}) \<Rightarrow> (\<forall>j \<in> P \\ {i} : After(j,i,unread,max,flag,pc,num,nxt)))"

definition Inv where
  "Inv(unread,max,flag,pc,num,nxt) \<equiv> 
     TypeOK(unread,max,flag,pc,num,nxt)
   \<and> (\<forall>i \<in> P : IInv(i,unread,max,flag,pc,num,nxt))"

(*---------------------------------------------------------------------------*)

lemma procInNat:
  assumes "i \<in> P" shows "i \<in> Nat"
using assms by (blast dest: subsetD[OF PInNat])

theorem GGIrreflexive:
  assumes i: "i \<in> P" and j: "j \<in> P" 
    and 1: "i \<noteq> j" and 2: "num[i] \<in> Nat \\ {0}" and 3: "num[j] \<in> Nat \\ {0}"
  shows "\<not>(GG(i,j,num) \<and> GG(j,i,num))"
unfolding GG_def using assms nat_less_linear[of i j]
by (auto dest: procInNat nat_less_not_sym nat_less_leq_trans)

theorem InitImpliesTypeOK:
  "Init(unread,max,flag,pc,num,nxt) \<Longrightarrow> TypeOK(unread,max,flag,pc,num,nxt)"
  unfolding Init_def TypeOK_def
by (auto intro!: functionInFuncSet)

lemma TypeOKInvariant: 
  assumes type: "TypeOK(unread,max,flag,pc,num,nxt)" and self: "self \<in> P"
      and p: "p(self,unread,max,flag,pc,num,nxt,unread',max',flag',pc',num',nxt')"
  shows "TypeOK(unread',max',flag',pc',num',nxt')"
using p proof (auto simp: p_def)
  assume "p1(self,unread,max,flag,pc,num,nxt,unread',max',flag',pc',num',nxt')"
  with type show ?thesis
    by (clarsimp simp: TypeOK_def p1_def) auto
next
  assume p2: "p2(self,unread,max,flag,pc,num,nxt,unread',max',flag',pc',num',nxt')"
  show ?thesis
  proof (cases "unread[self] = {}")
    case True with type p2 show ?thesis
      by (clarsimp simp: TypeOK_def p2_def) auto
  next
    case False
    from type have "isAFcn(pc)"
      (* FIXME: needed for proving that pc'=pc, but why doesn't "simp ..." suffice *)
      by (force simp add: TypeOK_def)
    with False p2 obtain i where
      i: "pc[self] = ''p2''" "i \<in> unread[self]"
         "unread' = [unread EXCEPT ![self] = unread[self] \\ {i}]"
         "max' = (IF num[i] > max[self] THEN [max EXCEPT ![self] = num[i]] ELSE max)"
         "pc' = pc"
         "num' = num" "flag' = flag" "nxt' = nxt"
      by (auto simp: p2_def)
    with type
    have triv: "num' \<in> [P \<rightarrow> Nat]" "flag' \<in> [P \<rightarrow> BOOLEAN]"
               "nxt' \<in> [P \<rightarrow> P \<union> {defaultInitValue}]"
               "pc' \<in> [P \<rightarrow> {''p1'',''p2'',''p3'',''p4'',''p5'',''p6'',''p7'',''p8''}]"
               "\<forall>i \<in> P : (pc'[i] = ''p6'') \<Rightarrow> nxt'[i] \<in> P \\ {i}"
      by (auto simp: TypeOK_def)
    from i type self have u: "unread[self] \<subseteq> ProcSet"
      by (auto simp add: TypeOK_def)
    with i type have u': "unread' \<in> [P \<rightarrow> SUBSET P \<union> {defaultInitValue}]"
      by (auto simp: TypeOK_def)
    have u'': "\<forall>i \<in> P : pc'[i] \<in> {''p2'', ''p5'', ''p6''} \<Rightarrow> unread'[i] \<subseteq> P \<and> i \<notin> unread'[i]"
    proof (clarify)
      fix j
      assume j: "j \<in> P" and pc: "pc'[j] \<in> {''p2'', ''p5'', ''p6''}"
      from j type have junr: "j \<in> DOMAIN unread" by (auto simp: TypeOK_def)
      with i j pc type show "unread'[j] \<subseteq> P \<and> j \<notin> unread'[j]"
        by (auto simp: TypeOK_def)
    qed
    from u type i have n: "num[i] \<in> Nat"
      by (auto simp: TypeOK_def)
    with i type have m': "max' \<in> [P \<rightarrow> Nat \<union> {defaultInitValue}]"
      by (auto simp: TypeOK_def)
    from n i type have m'': "\<forall>j \<in> P : pc'[j] \<in> {''p2'',''p3''} \<Rightarrow> max'[j] \<in> Nat"
      (* FIXME: 
         - why doesn't Isabelle do the case distinction by itself?
         - why do we need condElse? *)
      by (cases "max[self] < num[i]", auto simp: TypeOK_def (*condThen*) condElse)
    from triv u' u'' m' m'' show ?thesis
      by (auto simp add: TypeOK_def)
  qed
next
  assume "p3(self,unread,max,flag,pc,num,nxt,unread',max',flag',pc',num',nxt')"
  with type show ?thesis
    by (clarsimp simp: TypeOK_def p3_def, auto)
next
  assume "p4(self,unread,max,flag,pc,num,nxt,unread',max',flag',pc',num',nxt')"
  with type show ?thesis
    by (clarsimp simp: TypeOK_def p4_def, auto)
next
  assume p5: "p5(self,unread,max,flag,pc,num,nxt,unread',max',flag',pc',num',nxt')"
  show ?thesis
  proof (cases "unread[self] = {}")
    case True with type p5 show ?thesis
      by (clarsimp simp: TypeOK_def p5_def, auto)
  next
    case False
    with p5 obtain i where
      i: "pc[self] = ''p5''" "i \<in> unread[self]" "nxt' = [nxt EXCEPT ![self] = i]"
         "\<not>flag[nxt'[self]]" "pc' = [pc EXCEPT ![self] = ''p6'']"
         "num' = num" "flag' = flag" "unread' = unread" "max' = max"
      by (auto simp: p5_def)
    with type show ?thesis by (clarsimp simp: TypeOK_def) auto
  qed
next
  assume "p6(self,unread,max,flag,pc,num,nxt,unread',max',flag',pc',num',nxt')"
  with type show ?thesis
    by (clarsimp simp: TypeOK_def p6_def) auto
next
  assume "p7(self,unread,max,flag,pc,num,nxt,unread',max',flag',pc',num',nxt')"
  with type show ?thesis
    by (clarsimp simp: TypeOK_def p7_def) auto
next
  assume "p8(self,unread,max,flag,pc,num,nxt,unread',max',flag',pc',num',nxt')"
  with type show ?thesis
    by (clarsimp simp: TypeOK_def p8_def) auto
qed

theorem InitImpliesInv:
  assumes init: "Init(unread,max,flag,pc,num,nxt)"
  shows "Inv(unread,max,flag,pc,num,nxt)"
proof -
  from init have "TypeOK(unread,max,flag,pc,num,nxt)"
    by (rule InitImpliesTypeOK)
  with init show ?thesis
    by (auto simp: Inv_def IInv_def Init_def)
qed

theorem InvImpliesMutex: 
  assumes inv: "Inv(unread,max,flag,pc,num,nxt)"
  shows "MutualExclusion(pc)"
proof (auto simp: MutualExclusion_def)
  fix i j
  assume hyps: "i \<in> ProcSet" "j \<in> ProcSet" "(i = j) = FALSE" "pc[i] = ''p7''" "pc[j] = ''p7''"
  with inv have "IInv(i, unread, max, flag, pc, num, nxt)" 
    and "IInv(j, unread, max, flag, pc, num, nxt)"
    by (auto simp: Inv_def)
  with hyps have "After(i,j,unread,max,flag,pc,num,nxt)" 
    and "After(j,i,unread,max,flag,pc,num,nxt)"
    by (auto simp: IInv_def)
  with hyps show FALSE 
    by (auto simp: After_def)
qed


lemma leq_neq_trans' (*[dest!]*): "a \<le> b \<Longrightarrow> b \<noteq> a \<Longrightarrow> a < b"
  by (drule not_sym) (rule leq_neq_trans)

theorem InvInvariant:
  assumes inv: "Inv(unread,max,flag,pc,num,nxt)"
      and nxt: "Next(unread,max,flag,pc,num,nxt,unread',max',flag',pc',num',nxt')"
  shows "Inv(unread',max',flag',pc',num',nxt')"
using assms unfolding Next_def
proof auto
  fix self
  assume self: "self \<in> ProcSet"
     and p: "p(self, unread, max, flag, pc, num, nxt, unread', max', flag', pc', num', nxt')"
  with inv show ?thesis
  proof (auto simp: Inv_def elim: TypeOKInvariant)
    fix i
    assume type: "TypeOK(unread, max, flag, pc, num, nxt)"
       and iinv: "\<forall>j \<in> ProcSet: IInv(j, unread, max, flag, pc, num, nxt)"
       and i: "i \<in> ProcSet"
    -- {* auxiliary definition that is used in several places of the proof below *}
    def after \<equiv> "\<lambda>k. pc[k] = ''p1'' \<or>
               pc[k] = ''p2'' \<and> (i \<in> unread[k] \<or> num[i] \<le> max[k]) \<or>
               pc[k] = ''p3'' \<and> num[i] \<le> max[k] \<or>
               (pc[k] = ''p4'' \<or> pc[k] = ''p5'' \<or> pc[k] = ''p6'') \<and>
               GG(i, k, num) \<and> (pc[k] = ''p5'' \<or> pc[k] = ''p6'' \<Rightarrow> i \<in> unread[k])"
    from iinv i have iinvi: "IInv(i, unread, max, flag, pc, num, nxt)" ..

    -- {* iinv3 and iinv5: particular parts of the invariant, taken to the meta-level for then being instantiated with the proper variables, to ease the work of the classical reasoner. *}
    from iinv
    have iinv3: "\<And>i j. 
      \<lbrakk>pc[i] \<in> {''p5'', ''p6''}; i \<in> ProcSet; j \<in> ProcSet \\ unread[i] \\ {i}\<rbrakk> 
      \<Longrightarrow> After(j, i, unread, max, flag, pc, num, nxt)"
    proof -
      fix i j
      assume pci: "pc[i] \<in> {''p5'', ''p6''}" 
        and i: "i \<in> ProcSet" and j:"j \<in> ProcSet \\ unread[i] \\ {i}"
      from iinv i have iinvi: "IInv(i, unread, max, flag, pc, num, nxt)" ..
      hence "pc[i] \<in> {''p5'', ''p6''} \<Rightarrow>
        (\<forall>j \<in> ProcSet \\ unread[i] \\ {i} :
        After(j, i, unread, max, flag, pc, num, nxt))"
        unfolding IInv_def by auto
      with pci i j
      show "After(j, i, unread, max, flag, pc, num, nxt)"
        by auto
    qed

    from iinv
    have iinv5: "\<And>i j. 
      \<lbrakk>pc[i] \<in> {''p7'', ''p8''}; i \<in> ProcSet; j \<in> ProcSet \\ {i}\<rbrakk> 
      \<Longrightarrow> After(j, i, unread, max, flag, pc, num, nxt)"
    proof -
      fix i j
      assume pci: "pc[i] \<in> {''p7'', ''p8''}" 
        and i: "i \<in> ProcSet" and j:"j \<in> ProcSet \\ {i}"
      from iinv i have iinvi: "IInv(i, unread, max, flag, pc, num, nxt)" ..
      hence "pc[i] \<in> {''p7'', ''p8''} \<Rightarrow>
        (\<forall>j \<in> ProcSet \\ {i} :
        After(j, i, unread, max, flag, pc, num, nxt))"
        unfolding IInv_def by auto
      with pci i j
      show "After(j, i, unread, max, flag, pc, num, nxt)"
        by auto
    qed

    -- {* This also is an instantiation of a type invariant, since auto can't resolve it in a reasonable time. *}
    from type i
    have nxti: "pc[i] = ''p6'' \<Rightarrow> nxt[i] \<in> ProcSet \<and> nxt[i] \<noteq> i"
      by (auto simp: TypeOK_def)

    from p show "IInv(i, unread', max', flag', pc', num', nxt')"
    proof (auto simp: p_def)
      assume p1: "p1(self, unread, max, flag, pc, num, nxt, unread', max', flag', pc', num', nxt')"
      show ?thesis
      proof (cases "self = i")
        case True
        with p1 type iinvi i show ?thesis
          by (clarsimp simp: TypeOK_def IInv_def p1_def)
      next
        assume selfi: "self \<noteq> i"
        with p1 type iinvi self i 
        have 1: "(num'[i] = 0) = (pc'[i] \<in> {''p1'', ''p2'', ''p3''})"
          by (clarsimp simp: TypeOK_def IInv_def p1_def)
        from selfi p1 type iinvi self i
        have 2: "flag'[i] = (pc'[i] \<in> {''p2'', ''p3'', ''p4''})"
          by (clarsimp simp: TypeOK_def IInv_def p1_def)
        have 3: "pc'[i] \<in> {''p5'', ''p6''} \<Rightarrow> 
                 (\<forall>j \<in> (P \\ unread'[i]) \\ {i} : After(j,i,unread',max',flag',pc',num',nxt'))"
        proof (rule+)
          fix j
          assume pc': "pc'[i] \<in> {''p5'',''p6''}" and j: "j \<in> (ProcSet \\ unread'[i]) \\ {i}"
          show "After(j,i,unread',max',flag',pc',num',nxt')"
          proof (cases "self = j")
            case True with selfi p1 type iinvi self i pc' show ?thesis
              proof (clarsimp simp: TypeOK_def IInv_def After_def p1_def nat_gt0_not0)
              (** FIXME: "proof(..., auto)" doesn't finish in reasonable time **)
              assume "pc[i] = ''p5'' \<or> pc[i] = ''p6''"
              thus "(pc[i] = ''p1'') = FALSE \<and> (pc[i] = ''p2'') = FALSE \<and> (pc[i] = ''p3'') = FALSE"
              by auto
          qed
        next
          case False with selfi p1 type iinvi self i pc' j show ?thesis
          proof (clarsimp simp: TypeOK_def IInv_def After_def p1_def nat_gt0_not0)
            (** FIXME: "proof(..., auto/force) doesn't finish in reasonable time 
                and auto / force / blast cannot handle the following in one fell swoop
                so we have to resort to very low-level reasoning. **)
            assume "pc[i] = ''p5'' \<or> pc[i] = ''p6''"
            hence ii1: "pc[i] \<noteq> ''p1'' \<and> pc[i] \<noteq> ''p2'' \<and> pc[i] \<noteq> ''p3''" by auto
            assume "\<forall>k \<in> ProcSet \\ unread[i] \\ {i}:
                       pc[k] = ''p1'' \<or>
                       pc[k] = ''p2'' \<and> (i \<in> unread[k] \<or> num[i] \<le> max[k]) \<or>
                       pc[k] = ''p3'' \<and> num[i] \<le> max[k] \<or>
                       (pc[k] = ''p4'' \<or> pc[k] = ''p5'' \<or> pc[k] = ''p6'') \<and>
                       GG(i, k, num) \<and> (pc[k] = ''p5'' \<or> pc[k] = ''p6'' \<Rightarrow> i \<in> unread[k])"
            hence aft: "\<forall>k \<in> ProcSet \\ unread[i] \\ {i}: after(k)" unfolding after_def .
            assume "j \<in> ProcSet" "(j \<in> unread[i]) = FALSE" "(j = i) = FALSE"
            with aft have "after(j)" by auto
            hence "pc[j] = ''p1'' \<or>
                   pc[j] = ''p2'' \<and> (i \<in> unread[j] \<or> num[i] \<le> max[j]) \<or>
                   pc[j] = ''p3'' \<and> num[i] \<le> max[j] \<or>
                   (pc[j] = ''p4'' \<or> pc[j] = ''p5'' \<or> pc[j] = ''p6'') \<and>
                   GG(i, j, num) \<and> (pc[j] = ''p5'' \<or> pc[j] = ''p6'' \<Rightarrow> i \<in> unread[j])"
              unfolding after_def .
            with ii1
            show "(pc[i] = ''p1'') = FALSE 
                  \<and> (pc[i] = ''p2'') = FALSE
                  \<and> (pc[i] = ''p3'') = FALSE
                  \<and> (pc[j] = ''p1'' \<or>
                     pc[j] = ''p2'' \<and> (i \<in> unread[j] \<or> num[i] \<le> max[j]) \<or>
                     pc[j] = ''p3'' \<and> num[i] \<le> max[j] \<or>
                     (pc[j] = ''p4'' \<or> pc[j] = ''p5'' \<or> pc[j] = ''p6'') \<and>
                     GG(i, j, num) \<and> (pc[j] = ''p5'' \<or> pc[j] = ''p6'' \<Rightarrow> i \<in> unread[j]))"
              by simp
          qed
        qed
      qed
      have 4: "pc'[i] = ''p6''
               \<and> (  (pc'[nxt'[i]] = ''p2'') \<and> i \<notin> unread'[nxt'[i]]
                  \<or> (pc'[nxt'[i]] = ''p3''))
               \<Rightarrow> max'[nxt'[i]] \<ge> num'[i]"
      proof (cases "self = nxt[i]")
        case True
        with selfi p1 type iinvi self i show ?thesis
          by (clarsimp simp: TypeOK_def IInv_def p1_def)
      next
        case False
        with type self i have "pc[i] = ''p6'' \<Rightarrow> nxt[i] \<in> ProcSet"
          by (auto simp: TypeOK_def)
        with False selfi p1 type iinvi self i show ?thesis
          by (clarsimp simp: TypeOK_def IInv_def p1_def)
      qed
      have 5: "(pc'[i] \<in> {''p7'', ''p8''}) \<Rightarrow> (\<forall>j \<in> P \\ {i} : After(j,i,unread',max',flag',pc',num',nxt'))"
      proof (rule+)
        fix j
        assume pc': "pc'[i] \<in> {''p7'',''p8''}" and j: "j \<in> ProcSet \\ {i}"
        show "After(j,i,unread',max',flag',pc',num',nxt')"
        proof (cases "self = j")
          case True with selfi p1 type iinvi self i pc' show ?thesis
          proof (clarsimp simp: TypeOK_def IInv_def After_def p1_def nat_gt0_not0)
            (** FIXME: same problems as in 3 above **)
            assume "(j = i) = FALSE" "pc[i] = ''p7'' \<or> pc[i] = ''p8''"
            thus "(pc[i] = ''p1'') = FALSE \<and> (pc[i] = ''p2'') = FALSE \<and> (pc[i] = ''p3'') = FALSE"
              by auto
          qed
        next
          case False with selfi p1 type iinvi self i pc' j show ?thesis
          proof (clarsimp simp: TypeOK_def IInv_def After_def p1_def nat_gt0_not0)
            (** FIXME: again, similar problems **)
            assume "pc[i] = ''p7'' \<or> pc[i] = ''p8''"
            hence ii1: "pc[i] \<noteq> ''p1'' \<and> pc[i] \<noteq> ''p2'' \<and> pc[i] \<noteq> ''p3''" by auto
            assume "\<forall>k \<in> ProcSet \\ {i} :
                       pc[k] = ''p1'' \<or>
                       pc[k] = ''p2'' \<and> (i \<in> unread[k] \<or> num[i] \<le> max[k]) \<or>
                       pc[k] = ''p3'' \<and> num[i] \<le> max[k] \<or>
                       (pc[k] = ''p4'' \<or> pc[k] = ''p5'' \<or> pc[k] = ''p6'') \<and>
                       GG(i, k, num) \<and> (pc[k] = ''p5'' \<or> pc[k] = ''p6'' \<Rightarrow> i \<in> unread[k])"
            hence aft: "\<forall>k \<in> ProcSet \\ {i} : after(k)" unfolding after_def .
            with j have "after(j)" by blast
            hence "pc[j] = ''p1'' \<or>
                   pc[j] = ''p2'' \<and> (i \<in> unread[j] \<or> num[i] \<le> max[j]) \<or>
                   pc[j] = ''p3'' \<and> num[i] \<le> max[j] \<or>
                   (pc[j] = ''p4'' \<or> pc[j] = ''p5'' \<or> pc[j] = ''p6'') \<and>
                   GG(i, j, num) \<and> (pc[j] = ''p5'' \<or> pc[j] = ''p6'' \<Rightarrow> i \<in> unread[j])"
              unfolding after_def .
            with ii1
            show "(pc[i] = ''p1'') = FALSE 
                  \<and> (pc[i] = ''p2'') = FALSE
                  \<and> (pc[i] = ''p3'') = FALSE
                  \<and> (pc[j] = ''p1'' \<or>
                     pc[j] = ''p2'' \<and> (i \<in> unread[j] \<or> num[i] \<le> max[j]) \<or>
                     pc[j] = ''p3'' \<and> num[i] \<le> max[j] \<or>
                     (pc[j] = ''p4'' \<or> pc[j] = ''p5'' \<or> pc[j] = ''p6'') \<and>
                     GG(i, j, num) \<and> (pc[j] = ''p5'' \<or> pc[j] = ''p6'' \<Rightarrow> i \<in> unread[j]))"
              by simp
          qed
        qed
      qed
      from 1 2 3 4 5 show ?thesis
        unfolding IInv_def by blast
    qed
  next
      assume p2: "p2(self, unread, max, flag, pc, num, nxt, unread', max', flag', pc', num', nxt')"
      show ?thesis
      proof (cases "self = i")
        assume selfi: "self = i"
        show ?thesis
        proof (cases "unread[self] = {}")
          case True
          with selfi p2 type iinvi i show ?thesis
            by (clarsimp simp: TypeOK_def IInv_def p2_def)
        next
          case False
          from type have "isAFcn(pc)"
            (* FIXME: needed for proving that pc'=pc, but why doesn't "simp ..." suffice *)
            by (force simp add: TypeOK_def)
          with False p2 obtain k where
            k: "pc[self] = ''p2''" "k \<in> unread[self]"
               "unread' = [unread EXCEPT ![self] = unread[self] \\ {k}]"
               "max' = (IF num[k] > max[self] THEN [max EXCEPT ![self] = num[k]] ELSE max)"
               "pc' = pc" "num' = num" "flag' = flag" "nxt' = nxt"
            by (auto simp: p2_def)
          with selfi type iinvi i show ?thesis
            by (clarsimp simp: TypeOK_def IInv_def)
        qed
      next
        assume selfi: "self \<noteq> i"
        show ?thesis
        proof (cases "unread[self] = {}")
          assume empty: "unread[self] = {}"
          with selfi p2 type iinvi self i
          have 1: "(num'[i] = 0) = (pc'[i] \<in> {''p1'', ''p2'', ''p3''})"
            by (clarsimp simp: TypeOK_def IInv_def p2_def)
          from empty selfi p2 type iinvi self i
          have 2: "flag'[i] = (pc'[i] \<in> {''p2'', ''p3'', ''p4''})"
            by (clarsimp simp: TypeOK_def IInv_def p2_def)
          have 3: "pc'[i] \<in> {''p5'', ''p6''} \<Rightarrow> 
                   (\<forall>j \<in> (P \\ unread'[i]) \\ {i} : After(j,i,unread',max',flag',pc',num',nxt'))"
          proof (rule+)
            fix j
            assume pc': "pc'[i] \<in> {''p5'',''p6''}" and j: "j \<in> (ProcSet \\ unread'[i]) \\ {i}"
            from j type have mx: "pc[j] = ''p2'' \<Rightarrow> max[j] \<in> Nat"
              by (auto simp: TypeOK_def)
            show "After(j,i,unread',max',flag',pc',num',nxt')"
            proof (cases "self = j")
              case True with empty selfi p2 type iinvi self i pc' j mx show ?thesis
              proof (clarsimp simp: TypeOK_def IInv_def After_def p2_def nat_gt0_not0)
                (** FIXME: again, some manual help necessary **)
                assume "pc[i] = ''p5'' \<or> pc[i] = ''p6''"
                hence ii1: "pc[i] \<noteq> ''p1'' \<and> pc[i] \<noteq> ''p2'' \<and> pc[i] \<noteq> ''p3''"
                  by auto
                assume "j \<in> ProcSet" "(j = i) = FALSE" 
                       "(j \<in> unread[i]) = FALSE" "pc[j] = ''p2''"
                       "unread[j] = {}"
                       "\<forall>j \<in> ProcSet \\ unread[i] \\ {i}: 
                           pc[j] = ''p1'' \<or>
                           pc[j] = ''p2'' \<and> (i \<in> unread[j] \<or> num[i] \<le> max[j]) \<or>
                           pc[j] = ''p3'' \<and> num[i] \<le> max[j] \<or>
                           (pc[j] = ''p4'' \<or> pc[j] = ''p5'' \<or> pc[j] = ''p6'') \<and>
                           GG(i, j, num) \<and> (pc[j] = ''p5'' \<or> pc[j] = ''p6'' \<Rightarrow> i \<in> unread[j])"
                hence "num[i] \<le> max[j]" by auto
                with ii1 show "(pc[i] = ''p1'') = FALSE \<and> (pc[i] = ''p2'') = FALSE \<and> (pc[i] = ''p3'') = FALSE \<and> num[i] \<le> max[j]"
                  by simp
              qed
            next
              case False with empty selfi p2 type iinvi self i pc' j show ?thesis
              proof (clarsimp simp: TypeOK_def IInv_def After_def p2_def nat_gt0_not0)
                (** FIXME: similar problems **)
                assume "pc[i] = ''p5'' \<or> pc[i] = ''p6''"
                hence ii1: "pc[i] \<noteq> ''p1'' \<and> pc[i] \<noteq> ''p2'' \<and> pc[i] \<noteq> ''p3''"
                  by auto
                assume "\<forall>j \<in> ProcSet \\ unread[i] \\ {i}: 
                           pc[j] = ''p1'' \<or>
                           pc[j] = ''p2'' \<and> (i \<in> unread[j] \<or> num[i] \<le> max[j]) \<or>
                           pc[j] = ''p3'' \<and> num[i] \<le> max[j] \<or>
                           (pc[j] = ''p4'' \<or> pc[j] = ''p5'' \<or> pc[j] = ''p6'') \<and>
                           GG(i, j, num) \<and> (pc[j] = ''p5'' \<or> pc[j] = ''p6'' \<Rightarrow> i \<in> unread[j])"
                hence aft: "\<forall>j \<in> ProcSet \\ unread[i] \\ {i}: after(j)"
                  unfolding after_def .
                assume "j \<in> ProcSet" "(j = i) = FALSE" "(j \<in> unread[i]) = FALSE"
                with aft have "after(j)" by auto
                with ii1 
                show "(pc[i] = ''p1'') = FALSE 
                      \<and> (pc[i] = ''p2'') = FALSE
                      \<and> (pc[i] = ''p3'') = FALSE
                      \<and> (pc[j] = ''p1'' \<or>
                         pc[j] = ''p2'' \<and> (i \<in> unread[j] \<or> num[i] \<le> max[j]) \<or>
                         pc[j] = ''p3'' \<and> num[i] \<le> max[j] \<or>
                         (pc[j] = ''p4'' \<or> pc[j] = ''p5'' \<or> pc[j] = ''p6'') \<and>
                         GG(i, j, num) \<and> (pc[j] = ''p5'' \<or> pc[j] = ''p6'' \<Rightarrow> i \<in> unread[j]))"
                  by (simp add: after_def)
              qed
            qed
          qed
          have 4: "pc'[i] = ''p6''
                   \<and> (  (pc'[nxt'[i]] = ''p2'') \<and> i \<notin> unread'[nxt'[i]]
                      \<or> (pc'[nxt'[i]] = ''p3''))
                   \<Rightarrow> max'[nxt'[i]] \<ge> num'[i]"
          proof (cases "self = nxt[i]")
            case True
            with empty selfi p2 type iinvi self i show ?thesis
              by (clarsimp simp: TypeOK_def IInv_def p2_def)
          next
            case False
            with type self i have "pc[i] = ''p6'' \<Rightarrow> nxt[i] \<in> ProcSet"
              by (auto simp: TypeOK_def)
            with False empty selfi p2 type iinvi self i show ?thesis
              by (clarsimp simp: TypeOK_def IInv_def p2_def)
          qed
          have 5: "(pc'[i] \<in> {''p7'', ''p8''}) \<Rightarrow> (\<forall>j \<in> P \\ {i} : After(j,i,unread',max',flag',pc',num',nxt'))"
          proof (rule+)
            fix j
            assume pc': "pc'[i] \<in> {''p7'',''p8''}" and j: "j \<in> ProcSet \\ {i}"
            from j type have mx: "pc[j] = ''p2'' \<Rightarrow> max[j] \<in> Nat"
              by (auto simp: TypeOK_def)
            show "After(j,i,unread',max',flag',pc',num',nxt')"
            proof (cases "self = j")
              case True
              with empty selfi p2 type iinvi i pc' j mx show ?thesis
              proof (clarsimp simp: TypeOK_def IInv_def After_def p2_def nat_gt0_not0)
                (** FIXME: similar problems **)
                assume "pc[i] = ''p7'' \<or> pc[i] = ''p8''"
                hence ii1: "pc[i] \<noteq> ''p1'' \<and> pc[i] \<noteq> ''p2'' \<and> pc[i] \<noteq> ''p3''"
                  by auto
                assume "j \<in> ProcSet" "(j = i) = FALSE" "pc[j] = ''p2''"
                       "unread[j] = {}"
                       "\<forall>j \<in> ProcSet \\ {i}: 
                           pc[j] = ''p1'' \<or>
                           pc[j] = ''p2'' \<and> (i \<in> unread[j] \<or> num[i] \<le> max[j]) \<or>
                           pc[j] = ''p3'' \<and> num[i] \<le> max[j] \<or>
                           (pc[j] = ''p4'' \<or> pc[j] = ''p5'' \<or> pc[j] = ''p6'') \<and>
                           GG(i, j, num) \<and> (pc[j] = ''p5'' \<or> pc[j] = ''p6'' \<Rightarrow> i \<in> unread[j])"
                hence "num[i] \<le> max[j]" by auto
                with ii1 show "(pc[i] = ''p1'') = FALSE \<and> (pc[i] = ''p2'') = FALSE \<and> (pc[i] = ''p3'') = FALSE \<and> num[i] \<le> max[j]"
                  by simp
              qed
            next
              case False
              with empty selfi p2 type iinvi i pc' j show ?thesis
              proof (clarsimp simp: TypeOK_def IInv_def After_def p2_def nat_gt0_not0)
                (** FIXME: similar problems **)
                assume "pc[i] = ''p7'' \<or> pc[i] = ''p8''"
                hence ii1: "pc[i] \<noteq> ''p1'' \<and> pc[i] \<noteq> ''p2'' \<and> pc[i] \<noteq> ''p3''"
                  by auto
                assume "\<forall>j \<in> ProcSet \\ {i}: 
                           pc[j] = ''p1'' \<or>
                           pc[j] = ''p2'' \<and> (i \<in> unread[j] \<or> num[i] \<le> max[j]) \<or>
                           pc[j] = ''p3'' \<and> num[i] \<le> max[j] \<or>
                           (pc[j] = ''p4'' \<or> pc[j] = ''p5'' \<or> pc[j] = ''p6'') \<and>
                           GG(i, j, num) \<and> (pc[j] = ''p5'' \<or> pc[j] = ''p6'' \<Rightarrow> i \<in> unread[j])"
                hence aft: "\<forall>j \<in> ProcSet \\ {i}: after(j)"
                  unfolding after_def .
                assume "j \<in> ProcSet" "(j = i) = FALSE"
                with aft have "after(j)" by auto
                with ii1 
                show "(pc[i] = ''p1'') = FALSE \<and>
                      (pc[i] = ''p2'') = FALSE \<and>
                      (pc[i] = ''p3'') = FALSE \<and>
                      (pc[j] = ''p1'' \<or>
                       pc[j] = ''p2'' \<and> (i \<in> unread[j] \<or> num[i] \<le> max[j]) \<or>
                       pc[j] = ''p3'' \<and> num[i] \<le> max[j] \<or>
                       (pc[j] = ''p4'' \<or> pc[j] = ''p5'' \<or> pc[j] = ''p6'') \<and>
                       GG(i, j, num) \<and> (pc[j] = ''p5'' \<or> pc[j] = ''p6'' \<Rightarrow> i \<in> unread[j]))"
                  by (simp add: after_def)
              qed
            qed
          qed
          from 1 2 3 4 5 show ?thesis
            unfolding IInv_def by blast
        next
          assume nempty: "unread[self] \<noteq> {}"
          from type have "isAFcn(pc)"
            (* FIXME: needed for proving that pc'=pc, but why doesn't "simp ..." suffice *)
            by (force simp: TypeOK_def)
          with nempty p2 obtain k where
            k: "pc[self] = ''p2''" "k \<in> unread[self]"
               "unread' = [unread EXCEPT ![self] = unread[self] \\ {k}]"
               "max' = (IF num[k] > max[self] THEN [max EXCEPT ![self] = num[k]] ELSE max)"
               "pc' = pc" "num' = num" "flag' = flag" "nxt' = nxt"
            by (auto simp: p2_def)
          with type self have kproc: "k \<in> ProcSet"
            by (auto simp: TypeOK_def)
          from k selfi type iinvi self i
          have 1: "(num'[i] = 0) = (pc'[i] \<in> {''p1'', ''p2'', ''p3''})"
            by (clarsimp simp: TypeOK_def IInv_def)
          from k selfi type iinvi self i
          have 2: "flag'[i] = (pc'[i] \<in> {''p2'', ''p3'', ''p4''})"
            by (clarsimp simp: TypeOK_def IInv_def)
          have 3: "pc'[i] \<in> {''p5'', ''p6''} \<Rightarrow> 
                   (\<forall>j \<in> (P \\ unread'[i]) \\ {i} : After(j,i,unread',max',flag',pc',num',nxt'))"
          proof (rule+)
            fix j
            assume pc': "pc'[i] \<in> {''p5'',''p6''}" and j: "j \<in> (ProcSet \\ unread'[i]) \\ {i}"
            from j type have mx: "pc[j] = ''p2'' \<Rightarrow> max[j] \<in> Nat"
              by (auto simp: TypeOK_def)
            show "After(j,i,unread',max',flag',pc',num',nxt')"
            proof (cases "self = j")
              assume selfj: "self = j"
              show ?thesis
              proof (cases "max[j] < num[k]")
                assume less: "max[j] < num[k]"
                show ?thesis
                proof (cases "i=k")
                  case True
                  with k selfi selfj less type iinvi self i pc' j mx show ?thesis
                  proof (clarsimp simp: TypeOK_def IInv_def After_def nat_gt0_not0)
                    assume "pc[k] = ''p5'' \<or> pc[k] = ''p6''"
                    thus "(pc[k] = ''p1'') = FALSE \<and> (pc[k] = ''p2'') = FALSE \<and> (pc[k] = ''p3'') = FALSE"
                      by auto
                  qed
                next
                  case False
                  with k selfi selfj less type iinvi self i pc' j mx show ?thesis
                  proof (clarsimp simp: TypeOK_def IInv_def After_def nat_gt0_not0)
                    assume "pc[i] = ''p5'' \<or> pc[i] = ''p6''"
                    hence ii1: "pc[i] \<noteq> ''p1'' \<and> pc[i] \<noteq> ''p2'' \<and> pc[i] \<noteq> ''p3''"
                      by auto
                    assume "pc[j] = ''p2''" "j \<in> ProcSet" 
                           "(j \<in> unread[i]) = FALSE" "(j = i) = FALSE"
                           "\<forall>j \<in> ProcSet \\ unread[i] \\ {i} :
                               pc[j] = ''p1'' \<or>
                               pc[j] = ''p2'' \<and> (i \<in> unread[j] \<or> num[i] \<le> max[j]) \<or>
                               pc[j] = ''p3'' \<and> num[i] \<le> max[j] \<or>
                               (pc[j] = ''p4'' \<or> pc[j] = ''p5'' \<or> pc[j] = ''p6'') \<and>
                               GG(i, j, num) \<and> (pc[j] = ''p5'' \<or> pc[j] = ''p6'' \<Rightarrow> i \<in> unread[j])"
                    hence ii2: "i \<in> unread[j] \<or> num[i] \<le> max[j]"
                      by auto
                    assume "max[j] < num[k]" "num \<in> [ProcSet \<rightarrow> Nat]" "i \<in> ProcSet" 
                           "max[j] \<in> Nat"
                    with ii2 kproc have "i \<in> unread[j] \<or> num[i] \<le> num[k]"
                      by (auto dest: nat_leq_less_trans)
                    with ii1
                    show "(pc[i] = ''p1'') = FALSE \<and> (pc[i] = ''p2'') = FALSE
                          \<and> (pc[i] = ''p3'') = FALSE
                          \<and> (i \<in> unread[j] \<or> num[i] \<le> num[k])"
                      by simp
                  qed
                qed
              next
                assume nless: "\<not>(max[j] < num[k])"
                show ?thesis
                proof (cases "i=k")
                  case True
                  with k selfi selfj nless type iinvi self i pc' j mx show ?thesis
                  proof (clarsimp simp: TypeOK_def IInv_def After_def nat_gt0_not0 condElse nat_not_less[simplified])
                    assume "pc[k] = ''p5'' \<or> pc[k] = ''p6''"
                    thus "(pc[k] = ''p1'') = FALSE \<and> (pc[k] = ''p2'') = FALSE \<and> (pc[k] = ''p3'') = FALSE"
                      by auto
                  qed
                next
                  case False
                  with k selfi selfj nless type iinvi self i pc' j mx show ?thesis
                  proof (clarsimp simp: TypeOK_def IInv_def After_def nat_gt0_not0 condElse)
                    assume "pc[i] = ''p5'' \<or> pc[i] = ''p6''"
                    hence ii1: "pc[i] \<noteq> ''p1'' \<and> pc[i] \<noteq> ''p2'' \<and> pc[i] \<noteq> ''p3''"
                      by auto
                    assume "j \<in> ProcSet" "(j \<in> unread[i]) = FALSE" 
                           "(j = i) = FALSE" "pc[j] = ''p2''"
                           "\<forall>j \<in> ProcSet \\ unread[i] \\ {i} :
                               pc[j] = ''p1'' \<or>
                               pc[j] = ''p2'' \<and> (i \<in> unread[j] \<or> num[i] \<le> max[j]) \<or>
                               pc[j] = ''p3'' \<and> num[i] \<le> max[j] \<or>
                               (pc[j] = ''p4'' \<or> pc[j] = ''p5'' \<or> pc[j] = ''p6'') \<and>
                               GG(i, j, num) \<and> (pc[j] = ''p5'' \<or> pc[j] = ''p6'' \<Rightarrow> i \<in> unread[j])"
                    hence "i \<in> unread[j] \<or> num[i] \<le> max[j]"
                      by auto
                    with ii1 show "(pc[i] = ''p1'') = FALSE
                                   \<and> (pc[i] = ''p2'') = FALSE
                                   \<and> (pc[i] = ''p3'') = FALSE
                                   \<and> (i \<in> unread[j] \<or> num[i] \<le> max[j])"
                      by simp
                  qed
                qed
              qed
            next
              assume selfj: "self \<noteq> j"
              show ?thesis
              proof (cases "max[self] < num[k]")
                case True
                with k selfi selfj type iinvi self i pc' j show ?thesis
                proof (clarsimp simp: TypeOK_def IInv_def After_def nat_gt0_not0)
                  assume "pc[i] = ''p5'' \<or> pc[i] = ''p6''"
                  hence ii1: "pc[i] \<noteq> ''p1'' \<and> pc[i] \<noteq> ''p2'' \<and> pc[i] \<noteq> ''p3''"
                    by auto
                  assume "\<forall>j \<in> ProcSet \\ unread[i] \\ {i} :
                             pc[j] = ''p1'' \<or>
                             pc[j] = ''p2'' \<and> (i \<in> unread[j] \<or> num[i] \<le> max[j]) \<or>
                             pc[j] = ''p3'' \<and> num[i] \<le> max[j] \<or>
                             (pc[j] = ''p4'' \<or> pc[j] = ''p5'' \<or> pc[j] = ''p6'') \<and>
                             GG(i, j, num) \<and> (pc[j] = ''p5'' \<or> pc[j] = ''p6'' \<Rightarrow> i \<in> unread[j])"
                  hence aft: "\<forall>j \<in> ProcSet \\ unread[i] \\ {i} : after(j)"
                    unfolding after_def .
                  assume "j \<in> ProcSet" "(j \<in> unread[i]) = FALSE" "(j = i) = FALSE"
                  with aft have "after(j)" by auto
                  with ii1 show
                    "(pc[i] = ''p1'') = FALSE \<and>
                     (pc[i] = ''p2'') = FALSE \<and>
                     (pc[i] = ''p3'') = FALSE \<and>
                     (pc[j] = ''p1'' \<or>
                      pc[j] = ''p2'' \<and> (i \<in> unread[j] \<or> num[i] \<le> max[j]) \<or>
                      pc[j] = ''p3'' \<and> num[i] \<le> max[j] \<or>
                      (pc[j] = ''p4'' \<or> pc[j] = ''p5'' \<or> pc[j] = ''p6'') \<and>
                      GG(i, j, num) \<and> (pc[j] = ''p5'' \<or> pc[j] = ''p6'' \<Rightarrow> i \<in> unread[j]))"
                    by (simp add: after_def)
                qed
              next
                case False
                with k selfi selfj type iinvi self i pc' j show ?thesis
                proof (clarsimp simp: TypeOK_def IInv_def After_def nat_gt0_not0 condElse)
                  assume "pc[i] = ''p5'' \<or> pc[i] = ''p6''"
                  hence ii1: "pc[i] \<noteq> ''p1'' \<and> pc[i] \<noteq> ''p2'' \<and> pc[i] \<noteq> ''p3''"
                    by auto
                  assume "\<forall>j \<in> ProcSet \\ unread[i] \\ {i} :
                             pc[j] = ''p1'' \<or>
                             pc[j] = ''p2'' \<and> (i \<in> unread[j] \<or> num[i] \<le> max[j]) \<or>
                             pc[j] = ''p3'' \<and> num[i] \<le> max[j] \<or>
                             (pc[j] = ''p4'' \<or> pc[j] = ''p5'' \<or> pc[j] = ''p6'') \<and>
                             GG(i, j, num) \<and> (pc[j] = ''p5'' \<or> pc[j] = ''p6'' \<Rightarrow> i \<in> unread[j])"
                  hence aft: "\<forall>j \<in> ProcSet \\ unread[i] \\ {i} : after(j)"
                    unfolding after_def .
                  assume "j \<in> ProcSet" "(j \<in> unread[i]) = FALSE" "(j = i) = FALSE"
                  with aft have "after(j)" by auto
                  with ii1 show
                    "(pc[i] = ''p1'') = FALSE \<and> (pc[i] = ''p2'') = FALSE \<and> (pc[i] = ''p3'') = FALSE \<and>
                     (pc[j] = ''p1'' \<or>
                      pc[j] = ''p2'' \<and> (i \<in> unread[j] \<or> num[i] \<le> max[j]) \<or>
                      pc[j] = ''p3'' \<and> num[i] \<le> max[j] \<or>
                      (pc[j] = ''p4'' \<or> pc[j] = ''p5'' \<or> pc[j] = ''p6'') \<and>
                      GG(i, j, num) \<and> (pc[j] = ''p5'' \<or> pc[j] = ''p6'' \<Rightarrow> i \<in> unread[j]))"
                    by (simp add: after_def)
                qed
              qed
            qed
          qed
          have 4: "pc'[i] = ''p6''
                   \<and> (  (pc'[nxt'[i]] = ''p2'') \<and> i \<notin> unread'[nxt'[i]]
                      \<or> (pc'[nxt'[i]] = ''p3''))
                   \<Rightarrow> max'[nxt'[i]] \<ge> num'[i]"
          proof (cases "self = nxt[i]")
            assume nxt: "self = nxt[i]"
            from type k self have mx: "max[self] \<in> Nat"
              by (auto simp: TypeOK_def)
            show ?thesis
            proof (cases "max[self] < num[k]")
              case True
              with k selfi type iinvi self i nxt mx show ?thesis
              proof (clarsimp simp: TypeOK_def IInv_def, cases "i=k", simp, simp)
                assume "num \<in> [ProcSet \<rightarrow> Nat]" "num[i] \<le> max[nxt[i]]" "max[nxt[i]] < num[k]"
                with mx kproc i nxt show "num[i] \<le> num[k]"
                  by (auto dest: nat_leq_less_trans)
              qed
            next
              case False
              with k selfi type iinvi self i nxt mx show ?thesis
                by (clarsimp simp: TypeOK_def IInv_def nat_not_less[simplified])
            qed
          next
            assume nxt: "self \<noteq> nxt[i]"
            from type self i have pc6: "pc[i] = ''p6'' \<Rightarrow> nxt[i] \<in> ProcSet"
              by (auto simp: TypeOK_def)
            show ?thesis
            proof (cases "max[self] < num[k]")
              case True
              with k selfi type iinvi self i nxt pc6 show ?thesis
                by (clarsimp simp: TypeOK_def IInv_def)
            next
              case False
              with k selfi type iinvi self i nxt pc6 show ?thesis
                by (clarsimp simp: TypeOK_def IInv_def condElse)
            qed
          qed
          have 5: "(pc'[i] \<in> {''p7'', ''p8''}) \<Rightarrow> (\<forall>j \<in> P \\ {i} : After(j,i,unread',max',flag',pc',num',nxt'))"
          proof (rule+)
            fix j
            assume pc': "pc'[i] \<in> {''p7'',''p8''}" and j: "j \<in> ProcSet \\ {i}"
            from j type have mx: "pc[j] = ''p2'' \<Rightarrow> max[j] \<in> Nat"
              by (auto simp: TypeOK_def)
            show "After(j,i,unread',max',flag',pc',num',nxt')"
            proof (cases "self = j")
              assume selfj: "self = j"
              show ?thesis
              proof (cases "max[j] < num[k]")
                assume less: "max[j] < num[k]"
                show ?thesis
                proof (cases "i=k")
                  case True
                  with k selfi selfj less type iinvi i pc' j mx show ?thesis
                  proof (clarsimp simp: TypeOK_def IInv_def After_def nat_gt0_not0)
                    assume "pc[k] = ''p7'' \<or> pc[k] = ''p8''"
                    thus "(pc[k] = ''p1'') = FALSE
                          \<and> (pc[k] = ''p2'') = FALSE
                          \<and> (pc[k] = ''p3'') = FALSE"
                      by auto
                  qed
                next
                  case False
                  with k selfi selfj less type iinvi i pc' j mx show ?thesis
                  proof (clarsimp simp: TypeOK_def IInv_def After_def nat_gt0_not0)
                    assume "pc[i] = ''p7'' \<or> pc[i] = ''p8''"
                    hence ii1: "pc[i] \<noteq> ''p1'' \<and> pc[i] \<noteq> ''p2'' \<and> pc[i] \<noteq> ''p3''"
                      by auto
                    assume "j \<in> ProcSet" "(j = i) = FALSE" "pc[j] = ''p2''" 
                           "\<forall>j \<in> ProcSet \\ {i} :
                              pc[j] = ''p1'' \<or>
                              pc[j] = ''p2'' \<and> (i \<in> unread[j] \<or> num[i] \<le> max[j]) \<or>
                              pc[j] = ''p3'' \<and> num[i] \<le> max[j] \<or>
                              (pc[j] = ''p4'' \<or> pc[j] = ''p5'' \<or> pc[j] = ''p6'') \<and>
                              GG(i, j, num) \<and> (pc[j] = ''p5'' \<or> pc[j] = ''p6'' \<Rightarrow> i \<in> unread[j])"
                    hence ii2: "i \<in> unread[j] \<or> num[i] \<le> max[j]"
                      by auto
                    assume "max[j] < num[k]" "num \<in> [ProcSet \<rightarrow> Nat]" "max[j] \<in> Nat"
                    with i kproc ii2 have "i \<in> unread[j] \<or> num[i] \<le> num[k]"
                      by (auto dest: nat_leq_less_trans)
                    with ii1 show "(pc[i] = ''p1'') = FALSE
                                   \<and> (pc[i] = ''p2'') = FALSE
                                   \<and> (pc[i] = ''p3'') = FALSE
                                   \<and> (i \<in> unread[j] \<or> num[i] \<le> num[k])"
                      by simp
                  qed
                qed
              next
                assume nless: "\<not>(max[j] < num[k])"
                show ?thesis
                proof (cases "i=k")
                  case True
                  with k selfi selfj nless type iinvi i pc' j mx show ?thesis
                  proof (clarsimp simp: TypeOK_def IInv_def After_def nat_gt0_not0 nat_not_less[simplified])
                    assume "pc[k] = ''p7'' \<or> pc[k] = ''p8''"
                    thus "(pc[k] = ''p1'') = FALSE \<and> (pc[k] = ''p2'') = FALSE \<and> (pc[k] = ''p3'') = FALSE"
                      by auto
                  qed
                next
                  case False
                  with k selfi selfj nless type iinvi i pc' j mx show ?thesis
                  proof (clarsimp simp: TypeOK_def IInv_def After_def nat_gt0_not0)
                    assume "pc[i] = ''p7'' \<or> pc[i] = ''p8''"
                    hence ii1: "pc[i] \<noteq> ''p1'' \<and> pc[i] \<noteq> ''p2'' \<and> pc[i] \<noteq> ''p3''"
                      by auto
                    assume "j \<in> ProcSet" "(j = i) = FALSE" "pc[j] = ''p2''"
                           "\<forall>j \<in> ProcSet \\ {i} :
                               pc[j] = ''p1'' \<or>
                               pc[j] = ''p2'' \<and> (i \<in> unread[j] \<or> num[i] \<le> max[j]) \<or>
                               pc[j] = ''p3'' \<and> num[i] \<le> max[j] \<or>
                               (pc[j] = ''p4'' \<or> pc[j] = ''p5'' \<or> pc[j] = ''p6'') \<and>
                               GG(i, j, num) \<and> (pc[j] = ''p5'' \<or> pc[j] = ''p6'' \<Rightarrow> i \<in> unread[j])"
                    hence "i \<in> unread[j] \<or> num[i] \<le> max[j]"
                      by auto
                    with ii1 show "(pc[i] = ''p1'') = FALSE
                                   \<and> (pc[i] = ''p2'') = FALSE
                                   \<and> (pc[i] = ''p3'') = FALSE
                                   \<and> (i \<in> unread[j] \<or> num[i] \<le> max[j])"
                      by simp
                  qed
                qed
              qed
            next
              assume selfj: "self \<noteq> j"
              show ?thesis
              proof (cases "max[self] < num[k]")
                case True
                with k selfi selfj type iinvi self i pc' j show ?thesis
                proof (clarsimp simp: TypeOK_def IInv_def After_def nat_gt0_not0)
                  assume "pc[i] = ''p7'' \<or> pc[i] = ''p8''"
                  hence ii1: "pc[i] \<noteq> ''p1'' \<and> pc[i] \<noteq> ''p2'' \<and> pc[i] \<noteq> ''p3''"
                    by auto
                  assume "\<forall>j \<in> ProcSet \\ {i} :
                             pc[j] = ''p1'' \<or>
                             pc[j] = ''p2'' \<and> (i \<in> unread[j] \<or> num[i] \<le> max[j]) \<or>
                             pc[j] = ''p3'' \<and> num[i] \<le> max[j] \<or>
                             (pc[j] = ''p4'' \<or> pc[j] = ''p5'' \<or> pc[j] = ''p6'') \<and>
                             GG(i, j, num) \<and> (pc[j] = ''p5'' \<or> pc[j] = ''p6'' \<Rightarrow> i \<in> unread[j])"
                  hence aft: "\<forall>j \<in> ProcSet \\ {i} : after(j)"
                    unfolding after_def .
                  assume "j \<in> ProcSet" "(j = i) = FALSE"
                  with aft have "after(j)" by auto
                  with ii1 show
                    "(pc[i] = ''p1'') = FALSE \<and> (pc[i] = ''p2'') = FALSE \<and> (pc[i] = ''p3'') = FALSE \<and>
                     (pc[j] = ''p1'' \<or>
                      pc[j] = ''p2'' \<and> (i \<in> unread[j] \<or> num[i] \<le> max[j]) \<or>
                      pc[j] = ''p3'' \<and> num[i] \<le> max[j] \<or>
                      (pc[j] = ''p4'' \<or> pc[j] = ''p5'' \<or> pc[j] = ''p6'') \<and>
                      GG(i, j, num) \<and> (pc[j] = ''p5'' \<or> pc[j] = ''p6'' \<Rightarrow> i \<in> unread[j]))"
                    by (simp add: after_def)
                qed
              next
                case False
                with k selfi selfj type iinvi self i pc' j show ?thesis
                proof (clarsimp simp: TypeOK_def IInv_def After_def nat_gt0_not0)
                  assume "pc[i] = ''p7'' \<or> pc[i] = ''p8''"
                  hence ii1: "pc[i] \<noteq> ''p1'' \<and> pc[i] \<noteq> ''p2'' \<and> pc[i] \<noteq> ''p3''"
                    by auto
                  assume "\<forall>j \<in> ProcSet \\ {i} :
                             pc[j] = ''p1'' \<or>
                             pc[j] = ''p2'' \<and> (i \<in> unread[j] \<or> num[i] \<le> max[j]) \<or>
                             pc[j] = ''p3'' \<and> num[i] \<le> max[j] \<or>
                             (pc[j] = ''p4'' \<or> pc[j] = ''p5'' \<or> pc[j] = ''p6'') \<and>
                             GG(i, j, num) \<and> (pc[j] = ''p5'' \<or> pc[j] = ''p6'' \<Rightarrow> i \<in> unread[j])"
                  hence aft: "\<forall>j \<in> ProcSet \\ {i} : after(j)"
                    unfolding after_def .
                  assume "j \<in> ProcSet" "(j = i) = FALSE"
                  with aft have "after(j)" by auto
                  with ii1 show
                    "(pc[i] = ''p1'') = FALSE \<and> (pc[i] = ''p2'') = FALSE \<and> (pc[i] = ''p3'') = FALSE \<and>
                     (pc[j] = ''p1'' \<or>
                      pc[j] = ''p2'' \<and> (i \<in> unread[j] \<or> num[i] \<le> max[j]) \<or>
                      pc[j] = ''p3'' \<and> num[i] \<le> max[j] \<or>
                      (pc[j] = ''p4'' \<or> pc[j] = ''p5'' \<or> pc[j] = ''p6'') \<and>
                      GG(i, j, num) \<and> (pc[j] = ''p5'' \<or> pc[j] = ''p6'' \<Rightarrow> i \<in> unread[j]))"
                    by (simp add: after_def)
                qed
              qed
            qed
          qed
          from 1 2 3 4 5 show ?thesis
            unfolding IInv_def by blast
        qed
      qed
    next
      assume p3: "p3(self, unread, max, flag, pc, num, nxt, unread', max', flag', pc', num', nxt')"
      show ?thesis
      proof (cases "self = i")
        case True
        with p3 type iinvi i show ?thesis
          by (clarsimp simp: TypeOK_def IInv_def p3_def) auto
      next
        assume selfi: "self \<noteq> i"
        from selfi p3 type iinvi self i
        have 1: "(num'[i] = 0) = (pc'[i] \<in> {''p1'', ''p2'', ''p3''})"
          and 2: "flag'[i] = (pc'[i] \<in> {''p2'', ''p3'', ''p4''})"
          by (clarsimp simp: TypeOK_def IInv_def p3_def)+
        have 3: "pc'[i] \<in> {''p5'', ''p6''} \<Rightarrow> 
          (\<forall>j \<in> (P \\ unread'[i]) \\ {i} : After(j,i,unread',max',flag',pc',num',nxt'))"
        proof (rule+)
          fix j
          assume pc': "pc'[i] \<in> {''p5'',''p6''}" and j: "j \<in> (ProcSet \\ unread'[i]) \\ {i}"
          show "After(j,i,unread',max',flag',pc',num',nxt')"
          proof (cases "self = j")
            case True with selfi type p3 self i j iinv3[of i j] pc' show ?thesis
              by (clarsimp simp: TypeOK_def p3_def After_def GG_def) auto
                (** a bit slow, but it's not necessary to do case analysis on IF **)
          next
            case False with selfi p3 type self i j iinv3[of i j] pc'
            show ?thesis
              by (clarsimp simp: TypeOK_def p3_def After_def GG_def)
          qed
        qed
        have 4: "pc'[i] = ''p6''
               \<and> (  (pc'[nxt'[i]] = ''p2'') \<and> i \<notin> unread'[nxt'[i]]
                  \<or> (pc'[nxt'[i]] = ''p3''))
               \<Rightarrow> max'[nxt'[i]] \<ge> num'[i]"
        proof (cases "self = nxt[i]")
          case True
          with selfi p3 type self i show ?thesis
            by (clarsimp simp: TypeOK_def p3_def)
        next
          case False
          with selfi p3 type iinvi self i nxti show ?thesis
            by (clarsimp simp: TypeOK_def IInv_def p3_def)
        qed
        have 5: "(pc'[i] \<in> {''p7'', ''p8''}) \<Rightarrow> (\<forall>j \<in> P \\ {i} : After(j,i,unread',max',flag',pc',num',nxt'))"
        proof (rule+)
          fix j
          assume pc': "pc'[i] \<in> {''p7'',''p8''}" and j: "j \<in> ProcSet \\ {i}"
          show "After(j,i,unread',max',flag',pc',num',nxt')"
          proof (cases "self = j")
            case True 
            with selfi type p3 self i j pc' iinv5[of i j] show ?thesis
              by (clarsimp simp: TypeOK_def p3_def After_def GG_def) auto
          next
            case False 
            with selfi p3 type self i j pc' iinv5[of i j] show ?thesis
              by (clarsimp simp: TypeOK_def p3_def After_def GG_def)
          qed
        qed
        from 1 2 3 4 5 show ?thesis
          unfolding IInv_def by blast
      qed
    next
      assume p4: "p4(self, unread, max, flag, pc, num, nxt, unread', max', flag', pc', num', nxt')"
      show ?thesis
      proof (cases "self = i")
        case True
        with p4 type iinvi i show ?thesis
          by (clarsimp simp: TypeOK_def IInv_def p4_def)
      next
        assume selfi: "self \<noteq> i"
        with p4 type iinvi self i
        have 1: "(num'[i] = 0) = (pc'[i] \<in> {''p1'', ''p2'', ''p3''})"
          and 2: "flag'[i] = (pc'[i] \<in> {''p2'', ''p3'', ''p4''})"
          by (clarsimp simp: TypeOK_def IInv_def p4_def)+
        have 3: "pc'[i] \<in> {''p5'', ''p6''} \<Rightarrow> 
                 (\<forall>j \<in> (P \\ unread'[i]) \\ {i} : After(j,i,unread',max',flag',pc',num',nxt'))"
        proof (rule+)
          fix j
          assume pc': "pc'[i] \<in> {''p5'',''p6''}" and j: "j \<in> (ProcSet \\ unread'[i]) \\ {i}"
          with selfi type p4 self i iinv3[of i j]
          show "After(j,i,unread',max',flag',pc',num',nxt')"
            unfolding TypeOK_def p4_def After_def GG_def
            by(cases "self = j", clarsimp+)
        qed
        have 4: "pc'[i] = ''p6''
               \<and> (  (pc'[nxt'[i]] = ''p2'') \<and> i \<notin> unread'[nxt'[i]]
                  \<or> (pc'[nxt'[i]] = ''p3''))
               \<Rightarrow> max'[nxt'[i]] \<ge> num'[i]"
        proof (cases "self = nxt[i]")
          case True
          with selfi p4 type self i show ?thesis
            by (clarsimp simp: TypeOK_def p4_def)
        next
          case False
          with selfi p4 type iinvi self i nxti show ?thesis
            by (clarsimp simp: TypeOK_def IInv_def p4_def)
        qed
        have 5: "(pc'[i] \<in> {''p7'', ''p8''}) \<Rightarrow> (\<forall>j \<in> P \\ {i} : After(j,i,unread',max',flag',pc',num',nxt'))"
        proof (rule+)
          fix j
          assume pc': "pc'[i] \<in> {''p7'',''p8''}" and j: "j \<in> ProcSet \\ {i}"
          with selfi type p4 self i j pc' iinv5[of i j] 
          show "After(j,i,unread',max',flag',pc',num',nxt')"
            by (cases "self = j") (clarsimp simp: TypeOK_def p4_def After_def)+
        qed
        from 1 2 3 4 5 show ?thesis
          unfolding IInv_def by blast
      qed
    next
      assume p5: "p5(self, unread, max, flag, pc, num, nxt, unread', max', flag', pc', num', nxt')"
      show ?thesis
      proof (cases "unread[self] = {}")
        assume empty: "unread[self] = {}"
        from p5 type iinvi self i empty
        have 1: "(num'[i] = 0) = (pc'[i] \<in> {''p1'', ''p2'', ''p3''})"
          unfolding TypeOK_def IInv_def p5_def
          by(cases "self = i", clarsimp+)
        from p5 type iinvi self i empty
        have 2: "flag'[i] = (pc'[i] \<in> {''p2'', ''p3'', ''p4''})"
          unfolding TypeOK_def IInv_def p5_def
          by(cases "self = i", clarsimp+)
        have 3: "pc'[i] \<in> {''p5'', ''p6''} \<Rightarrow> 
          (\<forall>j \<in> (P \\ unread'[i]) \\ {i} : After(j,i,unread',max',flag',pc',num',nxt'))"
        proof (rule+)
          fix j
          assume pc': "pc'[i] \<in> {''p5'',''p6''}" and j: "j \<in> (ProcSet \\ unread'[i]) \\ {i}"
          with empty type p5 self i j iinv3[of i j]
          show "After(j,i,unread',max',flag',pc',num',nxt')"
            unfolding TypeOK_def After_def GG_def p5_def
            apply(cases "self = j", force, clarsimp)
            by(cases "self = i", simp+)
        qed
        have 4: "pc'[i] = ''p6''
          \<and> (  (pc'[nxt'[i]] = ''p2'') \<and> i \<notin> unread'[nxt'[i]]
          \<or> (pc'[nxt'[i]] = ''p3''))
          \<Rightarrow> max'[nxt'[i]] \<ge> num'[i]"
        proof -
          from empty p5 type iinvi self i show ?thesis
            unfolding TypeOK_def IInv_def p5_def
            apply(cases "self = i", clarsimp)
            by (cases "self = nxt[i]", (clarsimp simp: nxti)+)
        qed

        have 5: "(pc'[i] \<in> {''p7'', ''p8''}) \<Rightarrow> (\<forall>j \<in> P \\ {i} : After(j,i,unread',max',flag',pc',num',nxt'))"
        proof (rule+)
          fix j
          assume pc': "pc'[i] \<in> {''p7'',''p8''}" and j: "j \<in> ProcSet \\ {i}"
          show "After(j,i,unread',max',flag',pc',num',nxt')"
          proof (cases "self = i")
            case True
            with empty type p5 self i j iinv3[of i j] (** IInv part 3 is used, not part 5! **)
            show ?thesis
              apply (clarsimp simp: IInv_def TypeOK_def p5_def After_def)
              apply (cases "pc[j] = ''p2''", clarsimp)
              apply (cases "pc[j] = ''p3''", clarsimp+)
              done
          next
            from empty
            have unreadj: "j \<notin> unread[self]" by auto
            assume selfi: "self \<noteq> i"
            with empty type p5 self i j pc' iinv5[of i j]
            show ?thesis
              unfolding IInv_def TypeOK_def p5_def After_def
              using unreadj
              by (cases "self = j") force+
          qed
        qed
        from 1 2 3 4 5 show ?thesis
          unfolding IInv_def by blast
      next
        assume empty: "unread[self] \<noteq> {}"
        from p5 type iinvi self i empty
        have 1: "(num'[i] = 0) = (pc'[i] \<in> {''p1'', ''p2'', ''p3''})"
          unfolding TypeOK_def IInv_def p5_def
          by (cases "self = i") clarsimp+
        from p5 type iinvi self i empty
        have 2: "flag'[i] = (pc'[i] \<in> {''p2'', ''p3'', ''p4''})"
          unfolding TypeOK_def IInv_def p5_def
          by(cases "self = i") clarsimp+
        have 3: "pc'[i] \<in> {''p5'', ''p6''} \<Rightarrow> 
          (\<forall>j \<in> (P \\ unread'[i]) \\ {i} : After(j,i,unread',max',flag',pc',num',nxt'))"
        proof (rule+)
          fix j
          assume pc': "pc'[i] \<in> {''p5'',''p6''}" and j: "j \<in> (ProcSet \\ unread'[i]) \\ {i}"
          with empty type p5 self i j iinv3[of i j]
          show "After(j,i,unread',max',flag',pc',num',nxt')"
            unfolding TypeOK_def After_def GG_def p5_def
            apply(cases "self = j", clarsimp)
            apply (cases "self = i", clarsimp)
              apply (cases "pc[j] = ''p2''", clarsimp)
              apply (cases "pc[j] = ''p3''", clarsimp+)
              done
        qed
        have 4: "pc'[i] = ''p6''
          \<and> (  (pc'[nxt'[i]] = ''p2'') \<and> i \<notin> unread'[nxt'[i]]
          \<or> (pc'[nxt'[i]] = ''p3''))
          \<Rightarrow> max'[nxt'[i]] \<ge> num'[i]"
        proof -
          from empty p5
          obtain k where p5: 
            "pc[self] = ''p5''"
            "k \<in> unread[self]" "nxt' = [nxt EXCEPT ![self] = k]"
            "\<not> flag[nxt'[self]] \<and> pc' = [pc EXCEPT ![self] = ''p6'']"
            "num' = num" "flag' = flag" "unread' = unread" "max' = max"
            by(auto simp: p5_def)
          with type self have kproc: "k \<in> ProcSet"
            by (auto simp: TypeOK_def)
          with iinv have iinvk: "IInv(k, unread, max, flag, pc, num, nxt)" ..
          show ?thesis
          proof (cases "self = i")
            case True
            with empty p5 type iinvi self i iinvk kproc
            show ?thesis
              unfolding TypeOK_def IInv_def
              by (cases "self = k") clarsimp+
          next
            case False
            with empty p5 type iinvi self i
            show ?thesis
              unfolding TypeOK_def IInv_def
              using nxti
              by (cases "self = nxt[i]") clarsimp+
          qed
        qed
        have 5: "(pc'[i] \<in> {''p7'', ''p8''}) \<Rightarrow> (\<forall>j \<in> P \\ {i} : After(j,i,unread',max',flag',pc',num',nxt'))"
        proof (rule+)
          fix j
          assume pc': "pc'[i] \<in> {''p7'',''p8''}" and j: "j \<in> ProcSet \\ {i}"
          from j type have mx: "pc[j] = ''p2'' \<Rightarrow> max[j] \<in> Nat"
            by (auto simp: TypeOK_def)
          from j iinv have iinvj: "IInv(j, unread, max, flag, pc, num, nxt)" by auto
          from empty type p5 self i j pc' iinv5[of i j]
          show "After(j,i,unread',max',flag',pc',num',nxt')"
            apply (cases "self = j", clarsimp simp: TypeOK_def p5_def After_def)
            by (cases "self = i") (clarsimp simp: TypeOK_def p5_def After_def)+
        qed
        from 1 2 3 4 5 show ?thesis
          unfolding IInv_def by blast
      qed
    next
      assume p6: "p6(self, unread, max, flag, pc, num, nxt, unread', max', flag', pc', num', nxt')"
      from p6 iinvi type i 
      have 1: "(num'[i] = 0) = (pc'[i] \<in> {''p1'', ''p2'', ''p3''})"
       and 2: "flag'[i] = (pc'[i] \<in> {''p2'', ''p3'', ''p4''})"
        unfolding TypeOK_def IInv_def p6_def
        by (cases "self = i", clarsimp, clarsimp)+
      have 3: "pc'[i] \<in> {''p5'', ''p6''} \<Rightarrow> 
        (\<forall>j \<in> (P \\ unread'[i]) \\ {i} : After(j,i,unread',max',flag',pc',num',nxt'))"
      proof(rule+)
        fix j
        assume pc': "pc'[i] \<in> {''p5'', ''p6''}" and j: "j \<in> ProcSet \\ unread'[i] \\ {i}"
        from iinv j 
        have iinvj: "IInv(j, unread, max, flag, pc, num, nxt)" by auto
        from type j
        have nxtj: "pc[j] = ''p6'' \<Rightarrow> nxt[j] \<in> ProcSet \<and> nxt[j] \<noteq> j"
          by (auto simp: TypeOK_def)
        show "After(j, i, unread', max', flag', pc', num', nxt')"
        proof (cases "self = i")
          assume selfi: "self = i"
          show ?thesis
          proof (cases "j \<in> unread[self]")
            assume junread: "j \<in> unread[self]"
            show ?thesis
            proof(cases "num[j] = 0")
              case True
              with j selfi i pc' p6 type self iinvi junread iinvj (* FIXME: iinvj *)
              show ?thesis
                apply (clarsimp simp: p6_def TypeOK_def IInv_def After_def nat_gt0_not0)
                by (cases "pc[nxt[i]] = ''p2''", clarsimp+)
            next
              assume numj: "num[j] \<noteq> 0"
              show ?thesis
              proof (cases "pc[j] \<in> {''p4'', ''p5'', ''p6''}")
                assume pcj: "pc[j] \<in> {''p4'', ''p5'', ''p6''}"
                show ?thesis
                proof (cases "i \<in> unread[j]")
                  case True
                  with j selfi i pc' p6 type self iinvi junread numj pcj
                  show ?thesis
                    by (clarsimp simp: p6_def TypeOK_def IInv_def After_def GG_def nat_gt0_not0)
                next
                  assume notunread: "i \<notin> unread[j]"
                  show ?thesis
                  proof (cases "j < i")
                    case True
                    from True j selfi i pc' p6 type self iinvi junread numj pcj iinv3[of j i] nxti notunread
                    show ?thesis
                      using procInNat nat_less_antisym_false[of j i]
                      by (clarsimp simp: p6_def TypeOK_def IInv_def After_def GG_def nat_gt0_not0) (force simp: nat_less_antisym_leq_false)
                  next
                    case False
                    with j selfi i pc' p6 type self iinvi junread numj pcj iinv3[of j i] nxti notunread
                    show ?thesis
                      unfolding p6_def TypeOK_def IInv_def After_def GG_def
                      proof (clarsimp simp: nat_gt0_not0 nat_not_less[simplified] nat_less_not_sym procInNat
                                      dest!: leq_neq_trans'[of "i" "nxt[i]", simplified])
                        assume
                          "pc[nxt[i]] = ''p5'' \<or> pc[nxt[i]] = ''p6'' \<Longrightarrow> num[nxt[i]] < num[i]"
                          "num[i] \<le> num[nxt[i]]" "nxt[i] \<in> ProcSet" "i \<in> ProcSet"
                          "num \<in> [ProcSet \<rightarrow> Nat]"
                        thus "(pc[nxt[i]] = ''p5'') = FALSE \<and> (pc[nxt[i]] = ''p6'') = FALSE"
                          by (auto simp: nat_less_antisym_leq_false)
                      qed
                  qed
                qed
              next
                assume pcj: "pc[j] \<notin> {''p4'', ''p5'', ''p6''}"
                show ?thesis
                proof (cases "pc[j] \<in> {''p7'', ''p8''}")
                  assume pcj: "pc[j] \<in> {''p7'', ''p8''}"
                  show ?thesis
                  proof (cases "j < i")
                    case True
                    with j selfi i pc' p6 type self iinvi junread numj pcj iinvj nxti iinv5[of "nxt[i]" i] 
                    show ?thesis
                      unfolding p6_def TypeOK_def IInv_def After_def GG_def
                      using nat_less_antisym_false[of j i]
                      apply (clarsimp simp: nat_gt0_not0 procInNat)
                      by (clarsimp simp: nat_less_antisym_leq_false)
                  next
                    case False
                    with j selfi i pc' p6 type self iinvi junread numj pcj iinv5[of j i] nxti
                    show ?thesis
                      unfolding p6_def TypeOK_def IInv_def After_def GG_def 
                      by (clarsimp simp: nat_gt0_not0 nat_not_less[simplified] procInNat)
                         (clarsimp dest!: leq_neq_trans'[simplified] simp: nat_less_antisym_leq_false nat_less_not_sym)
                  qed
                next
                  assume pcj2: "pc[j] \<notin> {''p7'', ''p8''}"
                  with j selfi i pc' p6 type self iinvi junread numj pcj iinvj nxti
                  show ?thesis
                    apply (clarsimp simp: p6_def TypeOK_def IInv_def After_def GG_def nat_gt0_not0)
                    by (erule funcSetE[where f="pc" and x="nxt[i]"], simp+)
                qed
              qed
            qed
          next
            assume "j \<notin> unread[self]"
            with j selfi i pc' p6 type self iinv3[of i j] 
            show ?thesis
              apply (clarsimp simp: p6_def TypeOK_def After_def)
              by (cases "pc[j] = ''p2''", clarsimp+)
          qed
        next
          assume selfi: "self \<noteq> i"
          show ?thesis
          proof (cases "self = j")
            assume selfj: "self = j"
            show ?thesis
            proof (cases "j < nxt[j]")
              case True
              with j pc' selfi selfj i p6 type self iinv3[of i j]
              show ?thesis
                apply (clarsimp simp: p6_def TypeOK_def After_def GG_def nat_gt0_not0)
                by (auto dest: nat_less_trans nat_less_leq_trans)
              (** slow **)
            next
              case False
              with j pc' selfi selfj i p6 type self iinv3[of i j] 
              show ?thesis
                using nxtj nat_not_less procInNat
                by (clarsimp simp: p6_def TypeOK_def After_def GG_def nat_gt0_not0 leq_neq_iff_less[simplified])
                   (auto simp: nat_less_antisym_leq_false)
            qed
          next
            case False
            with j selfi i pc' p6 type self iinv3[of i j] 
            show ?thesis
              by (clarsimp simp: p6_def TypeOK_def After_def)
          qed
        qed
      qed
      have 4: "pc'[i] = ''p6''
        \<and> (  (pc'[nxt'[i]] = ''p2'') \<and> i \<notin> unread'[nxt'[i]]
        \<or> (pc'[nxt'[i]] = ''p3''))
        \<Rightarrow> max'[nxt'[i]] \<ge> num'[i]"
      proof (cases "self = nxt[i]")
        case True
        with p6 type self i show ?thesis
          by (clarsimp simp: p6_def TypeOK_def)
      next
        case False
        with p6 type iinvi self i nxti show ?thesis
          apply (clarsimp simp: TypeOK_def IInv_def p6_def)
          by (cases "self = i", simp+)
      qed
      have 5: "(pc'[i] \<in> {''p7'', ''p8''}) \<Rightarrow> (\<forall>j \<in> P \\ {i} : After(j,i,unread',max',flag',pc',num',nxt'))"
      proof (rule+)
        fix j
        assume pc': "pc'[i] \<in> {''p7'',''p8''}" and j: "j \<in> ProcSet \\ {i}"
        show "After(j,i,unread',max',flag',pc',num',nxt')"
        proof (cases "self = j")
          case True
          assume selfj: "self = j"
          show ?thesis
          proof (cases "j < i")
            case True
            with type p6 i pc' j self selfj iinv5[of i j] 
            show ?thesis
              using nat_less_antisym_false[of j i] procInNat
              apply (clarsimp simp: p6_def TypeOK_def IInv_def After_def GG_def nat_gt0_not0)
              by (cases "i = nxt[j]") (auto simp: nat_less_antisym_leq_false)
          next
            case False
            from i j type have num: "num[i] \<in> Nat" "num[j] \<in> Nat"
              by (auto simp: TypeOK_def)
            from False type p6 i pc' j self selfj iinv5[of i j]
            show ?thesis
              using nat_less_linear[of i j] procInNat
              by (clarsimp simp: p6_def TypeOK_def IInv_def After_def GG_def nat_gt0_not0)
                 (auto dest!: nat_leq_less_trans)
          qed
        next
          case False
          with type iinv5[of i j] p6 i pc' j show ?thesis
            apply (clarsimp simp: TypeOK_def IInv_def After_def p6_def)
            by (cases "self = i", simp, simp)
        qed
      qed
      from 1 2 3 4 5 show ?thesis
        unfolding IInv_def by blast
    next
      assume p7: "p7(self, unread, max, flag, pc, num, nxt, unread', max', flag', pc', num', nxt')"

      from p7 type iinvi self i
      have 1: "(num'[i] = 0) = (pc'[i] \<in> {''p1'', ''p2'', ''p3''})"
        and 2: "flag'[i] = (pc'[i] \<in> {''p2'', ''p3'', ''p4''})"
        unfolding TypeOK_def IInv_def p7_def
        by (cases "self = i", clarsimp, clarsimp)+
      have 3: "pc'[i] \<in> {''p5'', ''p6''} \<Rightarrow> 
        (\<forall>j \<in> (P \\ unread'[i]) \\ {i} : After(j,i,unread',max',flag',pc',num',nxt'))"
      proof (rule+)
        fix j
        assume pc': "pc'[i] \<in> {''p5'',''p6''}" and j: "j \<in> (ProcSet \\ unread'[i]) \\ {i}"
        show "After(j,i,unread',max',flag',pc',num',nxt')"
        proof (cases "self = i")
          case True
          with type p7 iinv3[of i j] j i pc'
          show ?thesis
            by (clarsimp simp: TypeOK_def p7_def)
        next
          assume selfi: "self \<noteq> i"
          with type p7 iinv3[of i j] j i pc' selfi
          show ?thesis
            unfolding TypeOK_def p7_def After_def
            by (cases "self = j") force+
        qed
      qed
      have 4: "pc'[i] = ''p6''
               \<and> (  (pc'[nxt'[i]] = ''p2'') \<and> i \<notin> unread'[nxt'[i]]
                  \<or> (pc'[nxt'[i]] = ''p3''))
               \<Rightarrow> max'[nxt'[i]] \<ge> num'[i]"
      proof (cases "self = i")
        case True
        with p7 type self i show ?thesis
          by (clarsimp simp: TypeOK_def p7_def)
      next
        case False
        with p7 type iinvi self i nxti show ?thesis
          unfolding TypeOK_def IInv_def p7_def
          by (cases "self = nxt[i]") clarsimp+
      qed
      have 5: "(pc'[i] \<in> {''p7'', ''p8''}) \<Rightarrow> (\<forall>j \<in> P \\ {i} : After(j,i,unread',max',flag',pc',num',nxt'))"
      proof (rule+)
        fix j
        assume pc': "pc'[i] \<in> {''p7'',''p8''}" and j: "j \<in> ProcSet \\ {i}"
        show "After(j, i, unread', max', flag', pc', num', nxt')"
        proof (cases "self = j")
          case True
          with p7 type iinv5[of i j] self i pc' j show ?thesis
            by (clarsimp simp: TypeOK_def p7_def After_def)
        next
          case False
          with p7 type iinv5[of i j] self i pc' j show ?thesis
            unfolding TypeOK_def p7_def After_def
            by (cases "self=i") force+
        qed
      qed
      from 1 2 3 4 5 show ?thesis
        unfolding IInv_def by blast
    next
      assume p8: "p8(self, unread, max, flag, pc, num, nxt, unread', max', flag', pc', num', nxt')"
      have 1: "(num'[i] = 0) = (pc'[i] \<in> {''p1'', ''p2'', ''p3''})"
        and 2: "flag'[i] = (pc'[i] \<in> {''p2'', ''p3'', ''p4''})"
        using p8 type iinvi self i
        unfolding p8_def TypeOK_def IInv_def
        by (cases "self = i", clarsimp, clarsimp)+
      have 3: "pc'[i] \<in> {''p5'', ''p6''} \<Rightarrow> 
     (\<forall>j \<in> (P \\ unread'[i]) \\ {i} : After(j,i,unread',max',flag',pc',num',nxt'))"
      proof (rule+)
        fix j
        assume pc': "pc'[i] \<in> {''p5'',''p6''}" and j: "j \<in> (ProcSet \\ unread'[i]) \\ {i}"
        show "After(j,i,unread',max',flag',pc',num',nxt')"
        proof (cases "self = i")
          case True
          with type p8 j i pc'
          show ?thesis
            by (clarsimp simp: TypeOK_def p8_def)
        next
          assume selfi: "self \<noteq> i"
          with type p8 iinv3[of i j] j i pc' selfi
          show ?thesis
            unfolding TypeOK_def p8_def After_def GG_def
            by (cases "self = j") clarsimp+
        qed
      qed
      have 4: "pc'[i] = ''p6''
               \<and> (  (pc'[nxt'[i]] = ''p2'') \<and> i \<notin> unread'[nxt'[i]]
                  \<or> (pc'[nxt'[i]] = ''p3''))
               \<Rightarrow> max'[nxt'[i]] \<ge> num'[i]"
      proof (cases "self = i")
        case True
        with p8 type self i show ?thesis
          by (clarsimp simp: p8_def TypeOK_def)
      next
        case False
        with p8 type iinvi self i nxti show ?thesis
          unfolding p8_def TypeOK_def IInv_def
          by (cases "self = nxt[i]") clarsimp+
      qed
      have 5: "(pc'[i] \<in> {''p7'', ''p8''}) \<Rightarrow> (\<forall>j \<in> P \\ {i} : After(j,i,unread',max',flag',pc',num',nxt'))"
      proof (rule+)
        fix j
        assume pc': "pc'[i] \<in> {''p7'',''p8''}" and j: "j \<in> ProcSet \\ {i}"
        show "After(j, i, unread', max', flag', pc', num', nxt')"
        proof (cases "self = i")
          case True
          with type self i p8 pc' j show ?thesis
            by (clarsimp simp: TypeOK_def p8_def)
        next
          case False
          with type self i p8 pc' j iinv5[of i j] show ?thesis
            unfolding TypeOK_def p8_def After_def GG_def
            by (cases "self = j") clarsimp+
        qed
      qed
      from 1 2 3 4 5 show ?thesis
        unfolding IInv_def by blast
    qed
  qed
qed

end
