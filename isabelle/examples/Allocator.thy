(*  Title:      TLA+/Allocator.thy
    Author:     Stephan Merz, Inria Nancy
    Copyright (C) 2009-2025  INRIA and Microsoft Corporation
    License:    BSD
    Version:    Isabelle2025
*)

section \<open>A Simple Resource Allocator\<close>

theory Allocator
imports Constant
begin

text \<open>
  We define and prove the safety of a simple-minded resource allocator
  where clients can request and return resources. The allocator can
  hand out resources that are available. Since the allocator does
  not keep track of the fact if clients will be able to satisfy all 
  their requests, it may get into a situation where clients hold
  part of their requested resources but will wait forever for the
  outstanding resources, held by other clients.
\<close>

declare funcSetValue [dest]

consts   \<comment> \<open> constant parameters of TLA+ SimpleAllocator module \<close>
  Client :: c
  Resource :: c

definition TypeInvariant where
  "TypeInvariant(unsat,alloc) \<equiv>
      unsat \<in> [Client \<rightarrow> SUBSET Resource]
   \<and> alloc \<in> [Client \<rightarrow> SUBSET Resource]"

definition Init where
  "Init(unsat,alloc) \<equiv> unsat = [c \<in> Client \<mapsto> {}] \<and> alloc = [c \<in> Client \<mapsto> {}]"

lemma InitTypeInvariant:
  "Init(unsat,alloc) \<Rightarrow> TypeInvariant(unsat,alloc)"
by (auto simp: Init_def TypeInvariant_def)

\<comment> \<open> Alternative formulation as proof rule (meta-level implication) \<close>
lemma InitTypeInvariant':
  assumes "Init(unsat,alloc)"
  shows "TypeInvariant(unsat,alloc)"
using assms by (auto simp: Init_def TypeInvariant_def)

definition available where
  "available(alloc) \<equiv> Resource \<setminus> (UNION {alloc[c] : c \<in> Client})"

definition Request where
  "Request(c,S,unsat,alloc,unsat',alloc') \<equiv>
      unsat[c] = {} \<and> alloc[c] = {} \<and> S \<noteq> {}
   \<and> unsat' = [unsat EXCEPT ![c] = S]
   \<and> alloc' = alloc"

lemma RequestTypeInvariant:
  "TypeInvariant(unsat,alloc) 
   \<and> c \<in> Client \<and> S \<in> SUBSET Resource \<and> Request(c,S,unsat,alloc,unsat',alloc')
   \<Rightarrow> TypeInvariant(unsat',alloc')"
unfolding TypeInvariant_def Request_def by auto

\<comment> \<open> Alternative formulation \<close>
lemma RequestTypeInvariant':
  assumes "TypeInvariant(unsat,alloc)" and "c \<in> Client" and "S \<in> SUBSET Resource"
    and "Request(c,S,unsat,alloc,unsat',alloc')"
  shows "TypeInvariant(unsat',alloc')"
using assms unfolding TypeInvariant_def Request_def by auto

definition Allocate where
  "Allocate(c,S,unsat,alloc,unsat',alloc') \<equiv>
      S \<noteq> {} \<and> S \<subseteq> available(alloc) \<inter> unsat[c]
   \<and> alloc' = [alloc EXCEPT ![c] = alloc[c] \<union> S]
   \<and> unsat' = [unsat EXCEPT ![c] = alloc[c] \<setminus> S]"

lemma AllocateTypeInvariant:
  "TypeInvariant(unsat,alloc) 
   \<and> c \<in> Client \<and> S \<in> SUBSET Resource \<and> Allocate(c,S,unsat,alloc,unsat',alloc')
   \<Rightarrow> TypeInvariant(unsat',alloc')"
unfolding TypeInvariant_def Allocate_def by auto

\<comment> \<open> Alternative formulation \<close>
lemma AllocateTypeInvariant':
  assumes "TypeInvariant(unsat,alloc)" and "c \<in> Client" and "S \<in> SUBSET Resource"
    and "Allocate(c,S,unsat,alloc,unsat',alloc')"
  shows "TypeInvariant(unsat',alloc')"
using assms unfolding TypeInvariant_def Allocate_def by auto

definition Return where
  "Return(c,S,unsat,alloc,unsat',alloc') \<equiv>
      S \<noteq> {} \<and> S \<subseteq> alloc[c]
   \<and> alloc' = [alloc EXCEPT ![c] = alloc[c] \<setminus> S]
   \<and> unsat' = unsat"

lemma ReturnTypeInvariant:
  "TypeInvariant(unsat,alloc) 
   \<and> c \<in> Client \<and> S \<in> SUBSET Resource \<and> Return(c,S,unsat,alloc,unsat',alloc')
   \<Rightarrow> TypeInvariant(unsat',alloc')"
unfolding TypeInvariant_def Return_def by auto

\<comment> \<open> Alternative formulation \<close>
lemma ReturnTypeInvariant':
  assumes "TypeInvariant(unsat,alloc)" and "c \<in> Client" and "S \<in> SUBSET Resource"
     and "Return(c,S,unsat,alloc,unsat',alloc')"
  shows "TypeInvariant(unsat',alloc')"
using assms unfolding TypeInvariant_def Return_def by auto

definition Next where
  "Next(unsat,alloc,unsat',alloc') \<equiv>
   \<exists>c \<in> Client : \<exists>S \<in> SUBSET Resource :
      Request(c,S,unsat,alloc,unsat',alloc')
   \<or> Allocate(c,S,unsat,alloc,unsat',alloc')
   \<or> Return(c,S,unsat,alloc,unsat',alloc')"

lemma NextTypeInvariant:
  "TypeInvariant(unsat,alloc) \<and> Next(unsat,alloc,unsat',alloc')
   \<Rightarrow> TypeInvariant(unsat',alloc')"
unfolding Next_def
by (blast intro: RequestTypeInvariant [rule_format]
                 AllocateTypeInvariant [rule_format]
                 ReturnTypeInvariant [rule_format])

\<comment> \<open> Alternative formulation, using the rule formats of the individual lemmas \<close>
lemma NextTypeInvariant':
  assumes "TypeInvariant(unsat,alloc)" and "Next(unsat,alloc,unsat',alloc')"
  shows "TypeInvariant(unsat',alloc')"
using assms unfolding Next_def
by (blast intro: RequestTypeInvariant' AllocateTypeInvariant' ReturnTypeInvariant')

\<comment> \<open> Direct proof, without use of lemmas for subactions \<close>
lemma NextTypeInvariant'':
  "TypeInvariant(unsat,alloc) \<and> Next(unsat,alloc,unsat',alloc')
   \<Rightarrow> TypeInvariant(unsat',alloc')"
unfolding TypeInvariant_def Next_def Request_def Allocate_def Return_def
by auto


text \<open> Proof of mutual exclusion: no two processes ever hold a common resource \<close>

definition Mutex where
  "Mutex(alloc) \<equiv>
   \<forall>c,c' \<in> Client : \<forall>r \<in> Resource : r \<in> alloc[c] \<inter> alloc[c'] \<Rightarrow> c' = c"

lemma InitMutex: "Init(unsat,alloc) \<Rightarrow> Mutex(alloc)"
unfolding Init_def Mutex_def by auto

text \<open> 
  The @{text Request} action trivially preserves mutual exclusion because 
  it leaves the value of @{text alloc} unchanged.
\<close>

lemma RequestMutex:
  "Mutex(alloc)
   \<and> c \<in> Client \<and> S \<in> SUBSET Resource \<and> Request(c,S,unsat,alloc,unsat',alloc')
   \<Rightarrow> Mutex(alloc')"
unfolding Request_def by auto

text \<open>
  The @{text Return} action decreases the set of allocated resources,
  so preservation of mutual exclusion follows easily. Note the use of the type invariant.
\<close>

lemma ReturnMutex:
  "Mutex(alloc) \<and> TypeInvariant(unsat,alloc)
   \<and> clt \<in> Client \<and> S \<in> SUBSET Resource \<and> Return(clt,S,unsat,alloc,unsat',alloc')
   \<Rightarrow> Mutex(alloc')"
proof (clarify)
  assume clt: "clt \<in> Client" and S: "S \<subseteq> Resource"
     and ret: "Return(clt,S,unsat,alloc,unsat',alloc')"
     and mux: "Mutex(alloc)"
     and tpg: "TypeInvariant(unsat,alloc)"
  show "Mutex(alloc')"
  proof (clarsimp simp add: Mutex_def)
    fix c c' r
    assume c: "c \<in> Client" and c': "c' \<in> Client" and r: "r \<in> Resource"
       and rc: "r \<in> alloc'[c]" and rc': "r \<in> alloc'[c']"
    from ret c tpg have "alloc'[c] \<subseteq> alloc[c]"
      by (auto simp add: Return_def TypeInvariant_def)
    moreover
    from ret c' tpg have "alloc'[c'] \<subseteq> alloc[c']"
      by (auto simp add: Return_def TypeInvariant_def)
    ultimately
    show "c' = c" using mux rc rc' c c' r
      by (force simp add: Mutex_def)
  qed
qed

text \<open>
  In fact, the proof is easy for Isabelle's automatic proof methods.
  Note the use of @{text clarsimp} to simplify the goal before the heavy lifting.
\<close>

lemma
  "Mutex(alloc) \<and> TypeInvariant(unsat,alloc)
   \<and> clt \<in> Client \<and> S \<in> SUBSET Resource \<and> Return(clt,S,unsat,alloc,unsat',alloc')
   \<Rightarrow> Mutex(alloc')"
by (clarsimp simp: Mutex_def TypeInvariant_def Return_def) auto

text \<open>
  The proof for the @{text Allocate} action requires some case analysis.
  Unfortunately, we need to prove two symmetric assertions.
\<close>

lemma AllocateMutex:
  "Mutex(alloc) \<and> TypeInvariant(unsat,alloc)
   \<and> clt \<in> Client \<and> S \<in> SUBSET Resource \<and> Allocate(clt,S,unsat,alloc,unsat',alloc')
   \<Rightarrow> Mutex(alloc')"
proof (clarify)
  assume clt: "clt \<in> Client" and S: "S \<subseteq> Resource"
     and all: "Allocate(clt,S,unsat,alloc,unsat',alloc')"
     and mux: "Mutex(alloc)"
     and tpg: "TypeInvariant(unsat,alloc)"
  show "Mutex(alloc')"
  proof (clarsimp simp: Mutex_def)
    fix c c' r
    assume c: "c \<in> Client" and c': "c' \<in> Client" and r: "r \<in> Resource"
       and rc: "r \<in> alloc'[c]" and rc': "r \<in> alloc'[c']"
    show "c' = c"
    proof (cases "c=clt \<or> c'=clt")
      case False \<comment> \<open> the simple case first \<close>
      with all c c' tpg have "alloc'[c] = alloc[c] \<and> alloc'[c'] = alloc[c']"
	by (auto simp: Allocate_def TypeInvariant_def)
      with mux rc rc' c c' r show "c' = c"
	by (auto simp: Mutex_def)
    next
      case True \<comment> \<open> one of @{term c} or @{term c'} is @{term clt} \<close>
      thus "c' = c"
      proof
	assume c1: "c = clt"
	show "c' = c"
	proof (rule contradiction)
	  assume c1': "c' \<noteq> c"
	  with c1 c' all tpg have c2': "alloc'[c'] = alloc[c']"
	    by (auto simp: Allocate_def TypeInvariant_def)
	  with mux r c rc' c' c1' have "r \<notin> alloc[c]"
	    by (force simp: Mutex_def)
	  moreover
	  from c2' rc' r c' have "r \<notin> available(alloc)"
	    by (auto simp: available_def)
	  with all have "r \<notin> S"
	    by (auto simp: Allocate_def)
	  ultimately
	  have "r \<notin> alloc'[c]"
	    using all c1 c tpg by (auto simp: Allocate_def TypeInvariant_def)
	  with rc show "FALSE" by auto
	qed
      next   \<comment> \<open> symmetric argument \<close>
	assume c1: "c' = clt"
	show "c' = c"
	proof (rule contradiction)
	  assume c1': "c' \<noteq> c"
	  with c1 c all tpg have c2': "alloc'[c] = alloc[c]"
	    by (auto simp: Allocate_def TypeInvariant_def)
	  with mux r c rc c' c1' have "r \<notin> alloc[c']"
	    by (force simp: Mutex_def)
	  moreover
	  from c2' rc r c have "r \<notin> available(alloc)"
	    by (auto simp: available_def)
	  with all have "r \<notin> S"
	    by (auto simp: Allocate_def)
	  ultimately
	  have "r \<notin> alloc'[c']"
	    using all c1 c' tpg by (auto simp: Allocate_def TypeInvariant_def)
	  with rc' show "FALSE" by auto
	qed
      qed
    qed
  qed
qed


text \<open>
  Using the above lemmas, it is straightforward to derive that the
  next-state action preserves mutual exclusion.
\<close>

lemma NextMutex:
  "Mutex(alloc) \<and> TypeInvariant(unsat,alloc) \<and> Next(unsat,alloc,unsat',alloc')
   \<Rightarrow> Mutex(alloc')"
unfolding Next_def
by (blast intro:  RequestMutex [rule_format] AllocateMutex [rule_format] ReturnMutex [rule_format])

end
