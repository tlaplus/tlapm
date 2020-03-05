(*  Copyright 2004 INRIA  *)

Require Export Classical.

Lemma zenon_notnot : forall P : Prop,
  P -> (~ P -> False).
Proof. tauto. Qed.

Lemma zenon_nottrue :
  (~True -> False).
Proof. tauto. Qed.

Lemma zenon_noteq : forall (T : Type) (t : T),
  ((t <> t) -> False).
Proof. tauto. Qed.

Lemma zenon_eqsym : forall (T : Type) (t u : T),
  t = u -> u <> t -> False.
Proof. auto. Qed.

Lemma zenon_and : forall P Q : Prop,
  (P -> Q -> False) -> (P /\ Q -> False).
Proof. tauto. Qed.

Lemma zenon_or : forall P Q : Prop,
  (P -> False) -> (Q -> False) -> (P \/ Q -> False).
Proof. tauto. Qed.

Lemma zenon_imply : forall P Q : Prop,
  (~P -> False) -> (Q -> False) -> ((P -> Q) -> False).
Proof. tauto. Qed.

Lemma zenon_equiv : forall P Q : Prop,
  (~P -> ~Q -> False) -> (P -> Q -> False) -> ((P <-> Q) -> False).
Proof. tauto. Qed.

Lemma zenon_notand : forall P Q : Prop,
  (~P -> False) -> (~Q -> False) -> (~(P /\ Q) -> False).
Proof. tauto. Qed.

Lemma zenon_notor : forall P Q : Prop,
  (~P -> ~Q -> False) -> (~(P \/ Q) -> False).
Proof. tauto. Qed.

Lemma zenon_notimply : forall P Q : Prop,
  (P -> ~Q -> False) -> (~(P -> Q) -> False).
Proof. tauto. Qed.

Lemma zenon_notequiv : forall P Q : Prop,
  (~P -> Q -> False) -> (P -> ~Q -> False) -> (~(P <-> Q) -> False).
Proof. tauto. Qed.

Lemma zenon_ex : forall (T : Type) (P : T -> Prop),
  (forall z : T, ((P z) -> False)) -> ((exists x : T, (P x)) -> False).
Proof. firstorder. Qed.

Lemma zenon_all : forall (T : Type) (P : T -> Prop) (t : T),
  ((P t) -> False) -> ((forall x : T, (P x)) -> False).
Proof. firstorder. Qed.

Lemma zenon_notex : forall (T : Type) (P : T -> Prop) (t : T),
  (~(P t) -> False) -> (~(exists x : T, (P x)) -> False).
Proof. firstorder. Qed.

Lemma zenon_notall : forall (T : Type) (P : T -> Prop),
  (forall z : T, (~(P z) -> False)) -> (~(forall x : T, (P x)) -> False).
Proof. intros T P Ha Hb. apply Hb. intro. apply NNPP. exact (Ha x). Qed.

Lemma zenon_notallex : forall (T : Type) (P : T -> Prop),
  ((exists x : T, ~ (P x)) -> False) -> (~(forall x : T, (P x)) -> False).
Proof.
  firstorder. apply H0. intro x. apply NNPP. intro nPx. apply (H x nPx).
Qed.
Implicit Arguments zenon_notallex [T].

Lemma zenon_subst :
  forall (T : Type) (P : T -> Prop) (a b : T),
  (a <> b -> False) -> (P b -> False) -> (P a -> False).
Proof. intros T P a b heq h1 h2. rewrite (NNPP (a = b)) in h2; auto. Qed.

Lemma zenon_pnotp : forall P Q : Prop,
  (P = Q) -> (P -> ~Q -> False).
Proof. intros P Q Ha. rewrite Ha. auto. Qed.

Lemma zenon_notequal : forall (T : Type) (a b : T),
  (a = b) -> (a <> b -> False).
Proof. auto. Qed.

Lemma zenon_congruence_lr :
  forall (T : Type) (P : T -> Type) (a b : T),
  (P b -> False) -> (P a -> a = b -> False).
Proof. intros T P a b h1 h2 heq. rewrite heq in h2; auto. Qed.

Lemma zenon_congruence_rl :
  forall (T : Type) (P : T -> Type) (a b : T),
  (P b -> False) -> (P a -> b = a -> False).
Proof. intros T P a b h1 h2 heq. rewrite <- heq in h2; auto. Qed.

Ltac zenon_intro id :=
  intro id || let nid := fresh in (intro nid; try clear nid)
.

Definition zenon_and_s := fun P Q c h => zenon_and P Q h c.
Definition zenon_or_s := fun P Q c h i => zenon_or P Q h i c.
Definition zenon_imply_s := fun P Q c h i => zenon_imply P Q h i c.
Definition zenon_equiv_s := fun P Q c h i => zenon_equiv P Q h i c.
Definition zenon_notand_s := fun P Q c h i => zenon_notand P Q h i c.
Definition zenon_notor_s := fun P Q c h => zenon_notor P Q h c.
Definition zenon_notimply_s := fun P Q c h => zenon_notimply P Q h c.
Definition zenon_notequiv_s := fun P Q c h i => zenon_notequiv P Q h i c.
Definition zenon_ex_s := fun T P c h => zenon_ex T P h c.
Definition zenon_notall_s := fun T P c h => zenon_notall T P h c.
Definition zenon_notallex_s := fun T P c h => @zenon_notallex T P h c.
Implicit Arguments zenon_notallex_s [T].

Definition zenon_subst_s := fun T P x y c h i => zenon_subst T P x y h i c.
Definition zenon_pnotp_s := fun P Q c h i => zenon_pnotp P Q h i c.
Definition zenon_notequal_s := fun T x y c h => zenon_notequal T x y h c.

Definition zenon_congruence_lr_s :=
  fun T P a b c1 c2 h => zenon_congruence_lr T P a b h c1 c2.
Definition zenon_congruence_rl_s :=
  fun T P a b c1 c2 h => zenon_congruence_rl T P a b h c1 c2.

Lemma zenon_equal_base : forall (T : Type) (f : T), f = f.
Proof. auto. Qed.

Lemma zenon_equal_step :
  forall (S T : Type) (fa fb : S -> T) (a b : S),
  (fa = fb) -> (a <> b -> False) -> ((fa a) = (fb b)).
Proof. intros. rewrite (NNPP (a = b)). congruence. auto. Qed.

(* ------------------------------------------------------------ *)

Lemma zenon_recfun_unfold :
  forall (A : Type) (P : A -> Prop) (a b : A) (eqn : a = b),
  (P b -> False) -> P a -> False.
Proof.
  intros A P a b eqn H pa.
  apply H.
  rewrite <- eqn.
  auto.
Qed.

Implicit Arguments zenon_recfun_unfold [A].

Definition zenon_recfun_unfold_s :=
  fun A P a b eqn c h => @zenon_recfun_unfold A P a b eqn h c
.
Implicit Arguments zenon_recfun_unfold_s [A].
