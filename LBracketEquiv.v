Require Import Terms.
Require Import LBracketSyntax.

(** * Equivalences *)

(** Low-equivalence judgments. *)
Inductive eq_atom : Atom -> Atom -> Lab -> Prop :=
| eq_a : forall v1 l1 v2 l2 l,
  l1 = l2 ->
  ((l1 <: l \/ l2 <: l) -> eq_val v1 v2 l) ->
  eq_atom (v1,l1) (v2,l2) l
with eq_val : Val -> Val -> Lab -> Prop :=
| eq_vconst : forall c' l, eq_val (VConst c') (VConst c') l
| eq_vinx : forall d a a' l, 
  eq_atom a a' l -> 
  eq_val (VInx d a) (VInx d a') l
| eq_vclos : forall r1 r2 x t l,
  eq_env r1 r2 l ->
  eq_val (VClos r1 x t) (VClos r2 x t) l
with eq_env : Env -> Env -> Lab -> Prop :=
| eq_e_nil : forall l, eq_env nil nil l
| eq_e_cons : forall x a1 a2 r1 r2 l,
  eq_atom a1 a2 l -> eq_env r1 r2 l -> eq_env ((x,a1)::r1) ((x,a2)::r2) l.
Hint Constructors eq_atom eq_val eq_env.
Scheme eq_atom_ind' := Minimality for eq_atom Sort Prop
with eq_val_ind' := Minimality for eq_val Sort Prop
with eq_env_ind' := Minimality for eq_env Sort Prop.

Combined Scheme eq_mutind from eq_val_ind', eq_atom_ind', eq_env_ind'.

(** Low-equivalence judgments, that take the pc label into account. *)
Definition eq_atom' a1 pc1 a2 pc2 l :=
  (pc1 <: l \/ pc2 <: l) ->
  (pc1 = pc2 /\ eq_atom a1 a2 l).
Definition eq_env' r1 pc1 r2 pc2 l :=
  (pc1 <: l \/ pc2 <: l) ->
  (pc1 = pc2 /\ eq_env r1 r2 l).

(** * Preliminary lemmas. *)

Lemma maps_eq_env : forall x a1 a2 r1 r2 l,
  eq_env r1 r2 l ->
  maps r1 x a1 ->
  maps r2 x a2 ->
  eq_atom a1 a2 l.
Proof.
  intros x a1 a2 r1 r2 l Heq_env Hmaps1 Hmaps2.
  induction Heq_env. invs Hmaps1.
  invs Hmaps1; invs Hmaps2. destruct (beq_nat x x0).
  congruence. auto.
Qed.

Lemma maps_eq_env' : forall x a1 a2 r1 r2 pc1 pc2 l,
  eq_env' r1 pc1 r2 pc2 l ->
  maps r1 x a1 ->
  maps r2 x a2 ->
  eq_atom' a1 pc1 a2 pc2 l.
Proof.
  intros x a1 a2 r1 r2 pc1 pc2 l Heq_env' Hmaps1 Hmaps2 Hflows.
  apply Heq_env' in Hflows. intuition eauto using maps_eq_env.
Qed.

Lemma eq_env'_cons_inv_env : forall x a1 a2 r1 r2 pc1 pc2 l,
  eq_env' ((x,a1) :: r1) pc1 ((x,a2) :: r2) pc2 l ->
  eq_env' r1 pc1 r2 pc2 l.
Proof.
  intros x a1 a2 r1 r2 pc1 pc2 l H Hflows. apply H in Hflows as [? Henv].
  invsc Henv. auto.
Qed.

Lemma eq_env'_cons_inv_atom : forall x a1 a2 r1 r2 pc1 pc2 l,
  eq_env' ((x,a1) :: r1) pc1 ((x,a2) :: r2) pc2 l ->
  eq_atom' a1 pc1 a2 pc2 l.
Proof.
  intros x a1 a2 r1 r2 pc1 pc2 l H Hflows. apply H in Hflows as [? Henv].
  invsc Henv. auto.
Qed.

Lemma cons_eq_env' : forall x a1 a2 r1 r2 pc1 pc2 l,
  eq_atom' a1 pc1 a2 pc2 l ->
  eq_env' r1 pc1 r2 pc2 l ->
  eq_env' ((x,a1) :: r1) pc1 ((x,a2) :: r2) pc2 l.
Proof.
  intros x a1 a2 r1 r2 pc1 pc2 l Hatom Henv Hflows.
  specialize (Hatom Hflows). specialize (Henv Hflows).
  intuition auto.
Qed.

(** Reflexivity of low-equivalence. Later, we prove this is actually an
    equivalence relation. *)
Lemma eq_refl :
  (forall v l, eq_val v v l) /\
  (forall a l, eq_atom a a l) /\
  (forall r l, eq_env r r l).
Proof. apply val_atom_env_mutind; eauto. Qed.

Lemma eq_val_refl : forall v l, eq_val v v l.
Proof. pose proof eq_refl. intuition. Qed.

Lemma eq_atom_refl : forall a l, eq_atom a a l.
Proof. pose proof eq_refl. intuition. Qed.

Lemma eq_env_refl : forall r l, eq_env r r l.
Proof. pose proof eq_refl. intuition. Qed.

Lemma intro_and2 : forall (P P1 P2: Prop),
  (P -> (P1 /\ P2)) ->
  (P -> P1) /\ (P -> P2).
Proof. tauto. Qed.

Lemma eq_val_eq_tag : forall v1 v2 l,
  eq_val v1 v2 l ->
  tag_of v1 = tag_of v2.
Proof.
  intros v1 v2 l Heq.
  inversion Heq; eauto.
Qed.

Lemma or_introrefl : forall (P : Prop),
  P -> P \/ P.
Proof. left. assumption. Qed.

Lemma or_elimrefl : forall (P : Prop),
  P \/ P -> P.
Proof. intros P H. destruct H; assumption. Qed.