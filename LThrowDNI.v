Require Import Terms.
Require Import LNaVSyntax.
Require Import LThrowDBigStep.

(** * Equivalences *)

(** Low-equivalence judgments. *)
Inductive eq_res : Result -> Result -> Lab -> Prop :=
| eq_suc : forall a1 a2 l, eq_atom a1 a2 l -> eq_res (Suc a1) (Suc a2) l
| eq_throw : forall e l, eq_res (Throw e) (Throw e) l
with eq_atom : Atom -> Atom -> Lab -> Prop :=
| eq_a : forall b1 l1 b2 l2 l,
  l1 = l2 ->
  ((l1 <: l \/ l2 <: l) -> eq_box b1 b2 l) ->
  eq_atom (b1,l1) (b2,l2) l
with eq_box : Box -> Box -> Lab -> Prop :=
| eq_v : forall v1 v2 l, eq_val v1 v2 l -> eq_box (V v1) (V v2) l
| eq_d : forall e l, eq_box (D e) (D e) l
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
Hint Constructors eq_res eq_atom eq_box eq_val eq_env.
Scheme eq_res_ind' := Minimality for eq_res Sort Prop
with eq_atom_ind' := Minimality for eq_atom Sort Prop
with eq_box_ind' := Minimality for eq_box Sort Prop
with eq_val_ind' := Minimality for eq_val Sort Prop
with eq_env_ind' := Minimality for eq_env Sort Prop.

Combined Scheme eq_mutind from eq_val_ind', eq_box_ind', eq_atom_ind', eq_res_ind', eq_env_ind'.

(** Low-equivalence judgments, that take the pc label into account. *)
Definition eq_atom' a1 pc1 a2 pc2 l :=
  (pc1 <: l \/ pc2 <: l) ->
  (pc1 = pc2 /\ eq_atom a1 a2 l).
Definition eq_res' res1 pc1 res2 pc2 l :=
  (pc1 <: l \/ pc2 <: l) ->
  (pc1 = pc2 /\ eq_res res1 res2 l).
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
  (forall b l, eq_box b b l) /\
  (forall a l, eq_atom a a l) /\
  (forall r l, eq_env r r l).
Proof. apply val_box_atom_env_mutind; eauto. Qed.

Lemma eq_res_refl : forall res l, eq_res res res l.
Proof. pose proof eq_refl. destruct res; firstorder. Qed.

Lemma eq_val_refl : forall v l, eq_val v v l.
Proof. pose proof eq_refl. intuition. Qed.

Lemma eq_box_refl : forall b l, eq_box b b l.
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

(** Monotonicity of the pc label. This property is essential for the
    non-interference proof to go through. *)
Lemma pc_eval_monotonic : forall r t pc a pc',
  r |- t, pc ==> a, pc' -> pc <: pc'.
Proof.
  intros r t pc a pc' Heval.
  (eval_cases (induction Heval) Case);
  eauto 4 using flows_refl, flows_trans, join_1_rev.
Qed.

(* Binary operations respect equality *)

Lemma eq_box_eq_bop : forall b b11 b12 b21 b22 l,
  eq_box b11 b21 l ->
  eq_box b12 b22 l ->
  bop_res b b11 b12 = bop_res b b21 b22.
Proof.
  intros b b11 b12 b21 b22 l Heq1 Heq2.
  invsc Heq1; eauto; invsc Heq2; eauto;
  destruct b; invsc H; try invsc H0; eauto.
Qed.

Lemma eq_res_inversion_st : forall a e l,
  ~ (eq_res (Suc a) (Throw e) l).
Proof. intros a e l H. inversion H. Qed.

Lemma eq_res_inversion_ts : forall a e l,
  ~ (eq_res (Throw e) (Suc a)  l).
Proof. intros a e l H. inversion H. Qed.

Lemma eq_res'_inversion_st : forall a pc1 e pc2 l,
  pc1 <: l \/ pc2 <: l -> ~ (eq_res' (Suc a) pc1 (Throw e) pc2 l).
Proof.
  intros a pc1 e pc2 l Hpc H. destruct (H Hpc) as [_ Heq]. 
  eapply eq_res_inversion_st. eassumption.
Qed.

Lemma eq_res'_inversion_ts : forall a pc1 e pc2 l,
  pc1 <: l \/ pc2 <: l -> ~ (eq_res' (Throw e) pc1 (Suc a) pc2 l).
Proof.
  intros a pc1 e pc2 l Hpc H. destruct (H Hpc) as [_ Heq]. 
  eapply eq_res_inversion_ts. eassumption.
Qed.

Lemma eq_box_eq_propagate : forall b1 b2 l,
  eq_box b1 b2 l ->
  propagate_d b1 = propagate_d b2.
Proof. intros b1 b2 l Heq. invsc Heq; eauto. Qed.

Lemma eq_box_eq_tag : forall b1 b2 l,
  eq_box b1 b2 l ->
  eq_res (tag_res b1) (tag_res b2) l.
Proof. intros b1 b2 l Heq. invsc Heq; econstructor; eauto. invsc H; eauto. Qed.

Ltac withPc Hpc := apply intro_and2; intro Hpc.
Ltac unprime H Hpc := specialize (H Hpc); destruct H as [Heqpc H]; invsc Heqpc.
Ltac solve_var Henv Hmap1 Hmap2 := pose proof (maps_eq_env _ _ _ _ _ _ Henv Hmap1 Hmap2); eauto.
Ltac useIH IH l H := apply (IH _ _ _ _ l) in H; try solve [intro; eauto]; 
  destruct H.
Ltac absurdTag H := simpl in H; exfalso; auto.

(** Strengthened version of non-interference. *)
Lemma non_interference_strong :
  forall r1 t pc1 res1 pc1',
    r1 |- t, pc1 ==> res1, pc1' ->
      forall r2 pc2 res2 pc2' l,
        r2 |- t, pc2 ==> res2, pc2' ->
          eq_env' r1 pc1 r2 pc2 l ->
          (eq_env' r1 pc1' r2 pc2' l /\
            eq_res' res1 pc1' res2 pc2' l).
Proof.
intros r1 t pc1 res1 pc1' H.
(eval_cases (induction H) Case);
intros r2 pc2 res2 pc2'; try (rename l into l1); intros l Heval2 Heq_env.
Case "eval_var".
  withPc Hpc. invsc Heval2. unprime Heq_env Hpc. solve_var Heq_env H H2.
Case "eval_const". invsc Heval2.
  split. auto. intros Hpc. unprime Heq_env Hpc. auto.
Case "eval_let".
  withPc Hpc.
  pose proof (pc_eval_monotonic _ _ _ _ _ H).
  pose proof (pc_eval_monotonic _ _ _ _ _ H0).
  invsc Heval2.
  SCase "Suc".
    pose proof (pc_eval_monotonic _ _ _ _ _ H10).
    pose proof (pc_eval_monotonic _ _ _ _ _ H11).
    assert (pc <: l \/ pc2 <: l) by (destruct Hpc; eauto using flows_trans).
    unprime Heq_env H5. useIH IHeval1 l H10.
    assert (pc' <: l \/ pc'0 <: l) by (destruct Hpc; eauto using flows_trans).
    unprime H8 H9. apply IHeval2 with (l:=l) in H11. destruct H11.
    unprime H11 Hpc. eauto.
    invsc H8. constructor; auto.
  SCase "Throw". (* spurious *)
    pose proof (pc_eval_monotonic _ _ _ _ _ H10).
    assert (pc <: l \/ pc2 <: l) by (destruct Hpc; eauto using flows_trans).
    unprime Heq_env H4. useIH IHeval1 l H10.
    assert (pc' <: l \/ pc2' <: l) by (destruct Hpc; eauto using flows_trans).
    pose proof (eq_res'_inversion_st a _ ex _ _ H8). contradiction.
Case "eval_let_fail".
  withPc Hpc.
  pose proof (pc_eval_monotonic _ _ _ _ _ H).
  invsc Heval2.
  SCase "Suc". (* spurious *)
    pose proof (pc_eval_monotonic _ _ _ _ _ H8).
    pose proof (pc_eval_monotonic _ _ _ _ _ H9).
    assert (pc <: l \/ pc2 <: l) by (destruct Hpc; eauto using flows_trans).
    unprime Heq_env H3. useIH IHeval l H8.
    assert (pc' <: l \/ pc'0 <: l) by (destruct Hpc; eauto using flows_trans).
    pose proof (eq_res'_inversion_ts a _ ex _ _ H7). contradiction.
  SCase "Throw".
    pose proof (pc_eval_monotonic _ _ _ _ _ H8).
    assert (pc <: l \/ pc2 <: l) by (destruct Hpc; eauto using flows_trans).
    unprime Heq_env H2. useIH IHeval l H8.
    unprime H5 Hpc. unprime H4 Hpc. eauto.
Case "eval_abs". invsc Heval2.
  split. auto. intros Hpc. unprime Heq_env Hpc.
  split; auto.
Case "eval_app".
  withPc Hpc.
  pose proof (pc_eval_monotonic _ _ _ _ _ H1).
  pose proof (pc_eval_monotonic _ _ _ _ _ Heval2).
  assert (pc <: l \/ pc2 <: l) by
    (destruct Hpc; eauto using flows_trans, join_1_rev).
  unprime Heq_env H4. invsc Heval2.
  SCase "Suc". 
    solve_var Heq_env H H8. solve_var Heq_env H0 H10.
    invsc H6. pose proof (pc_eval_monotonic _ _ _ _ _ H14).
    assert (l0 <: l \/ l0 <: l) by (destruct Hpc; eauto using flows_trans, join_2_rev).
    specialize (H17 H9). invsc H17. invsc H13.
    useIH IHeval l H14. unprime H11 Hpc. unprime H12 Hpc. auto.
  SCase "Throw". (* spurious *)
    solve_var Heq_env H H9. 
    invsc H6. 
    assert (l0 <: l \/ l0 <: l) by (destruct Hpc; eauto using flows_trans, join_2_rev).
    specialize (H15 H6). invsc H15. invsc H8.
    absurdTag H13.
Case "eval_app_no_abs".
  withPc Hpc.
  pose proof (pc_eval_monotonic _ _ _ _ _ Heval2).
  assert (pc <: l \/ pc2 <: l) by
    (destruct Hpc; eauto using flows_trans, join_1_rev).
  unprime Heq_env H2. invsc Heval2.
  SCase "Suc". (* spurious *)
    solve_var Heq_env H H6. invsc H4. 
    pose proof (pc_eval_monotonic _ _ _ _ _ H12).
    assert (l0 <: l \/ l0 <: l) by (destruct Hpc; eauto using flows_trans, join_2_rev).
    specialize (H14 H5). invsc H14. invsc H10. absurdTag H0.
  SCase "Throw".
    solve_var Heq_env H H7. 
    invsc H4. 
    assert (l0 <: l \/ l0 <: l) by (destruct Hpc; eauto using join_2_rev).
    specialize (H13 H4). apply eq_box_eq_propagate in H13. rewrite H13. auto.
Case "eval_inx". invsc Heval2.
  split. auto. intros Hpc. unprime Heq_env Hpc. solve_var Heq_env H H6.
  split; eauto.
Case "eval_match".
  withPc Hpc.
  pose proof (pc_eval_monotonic _ _ _ _ _ H0).
  pose proof (pc_eval_monotonic _ _ _ _ _ Heval2).
  assert (pc <: l \/ pc2 <: l) by
    (destruct Hpc; eauto using flows_trans, join_1_rev).
  unprime Heq_env H3. invsc Heval2.
  SCase "Suc".
    pose proof (pc_eval_monotonic _ _ _ _ _ H14). solve_var Heq_env H H13.
    invsc H6.
    assert (l0 <: l \/ l0 <: l) by (destruct Hpc; eauto using flows_trans, join_2_rev).
    specialize (H15 H6). invsc H15. invsc H9. useIH IHeval l H14.
    unprime H7 Hpc. unprime H8 Hpc. eauto.
  SCase "Throw". (* spurious *)
    solve_var Heq_env H H13. invsc H5.
    assert (l0 <: l \/ l0 <: l) by (destruct Hpc; eauto using flows_trans, join_2_rev).
    specialize (H12 H5). invsc H12. invsc H7.
    absurdTag H14.
Case "eval_match_no_sum".
  withPc Hpc.
  pose proof (pc_eval_monotonic _ _ _ _ _ Heval2).
  assert (pc <: l \/ pc2 <: l) by
    (destruct Hpc; eauto using flows_trans, join_1_rev).
  unprime Heq_env H2. invsc Heval2.
  SCase "Suc". (* spurious *)
    solve_var Heq_env H H12. invsc H4.
    pose proof (pc_eval_monotonic _ _ _ _ _ H13).
    assert (l0 <: l \/ l0 <: l) by (destruct Hpc; eauto using flows_trans, join_2_rev).
    specialize (H11 H5). invsc H11. invsc H8.
    absurdTag H0.
  SCase "Throw".
    solve_var Heq_env H H12. invsc H4.
    assert (l0 <: l \/ l0 <: l) by (destruct Hpc; eauto using join_2_rev).
    specialize (H11 H4). apply eq_box_eq_propagate in H11. rewrite H11. auto.
Case "eval_tag". 
  invsc Heval2. withPc Hpc. 
  assert (pc <: l \/ pc2 <: l) by (destruct Hpc; eauto using join_1_rev).
  unprime Heq_env H0. solve_var Heq_env H H2.
  invsc H3. assert (l0 <: l \/ l0 <: l) by (destruct Hpc; eauto using join_2_rev).
  auto using eq_box_eq_tag. 
Case "eval_bop". invsc Heval2. withPc Hpc. 
  assert (pc <: l \/ pc2 <: l) by (destruct Hpc; eauto using join_1_rev).
  unprime Heq_env H1. solve_var Heq_env H H8. solve_var Heq_env H0 H9.
  invsc H3. invsc H4.
  assert (l'0 <: l \/ l'0 <: l) by (destruct Hpc; eauto using join_1_rev, join_2_rev).
  assert (l''0 <: l \/ l''0 <: l) by (destruct Hpc; eauto using join_1_rev, join_2_rev).
  specialize (H13 H3). specialize (H12 H4).
  pose proof (eq_box_eq_bop bo _ _ _ _ _ H13 H12). rewrite H5. eauto using eq_res_refl.
Case "eval_bracket".
  pose proof (pc_eval_monotonic _ _ _ _ _ H0).
  pose proof (pc_eval_monotonic _ _ _ _ _ Heval2).
  withPc Hpc. assert (pc <: l \/ pc2 <: l) by 
    (destruct Hpc; eauto using flows_trans, join_1_rev).
  unprime Heq_env H3. invsc Heval2.
  SCase "Suc".
    pose proof (pc_eval_monotonic _ _ _ _ _ H12).
    solve_var Heq_env H H8. invsc H6.
    assert (l'0 <: l \/ l'0 <: l) by (destruct Hpc; eauto using join_2_rev).
    specialize (H15 H6). split. eauto. split. reflexivity. invsc H15. invsc H10.
    constructor. constructor; auto. intro. useIH IHeval l H12; try eauto.
    unfold bracket_box.
    destruct res; destruct res0.
    SSCase "Suc".
      SSSCase "Suc".
        destruct a. destruct a0.
        remember (flows_dec (l1 \_/pc') (l0\_/(pc2\_/l'0))) as f1.
        destruct f1.
        SSSSCase "first check succeeds".
          assert (pc' <: l \/ pc'0 <: l)
            by (destruct Hpc; destruct H7; eauto using flows_trans, join_2_rev, join_minimal).
          unprime H9 H11. unprime H10 H11. invsc H10. invsc H16.
          assert (l2 <: l \/ l2 <: l)
            by (destruct Hpc; destruct H7; 
                eauto using flows_trans, join_1_rev, join_2_rev, join_minimal).
          rewrite <- Heqf1. auto.
        SSSSCase "first check fails".
          remember (flows_dec (l2 \_/pc'0) (l0\_/(pc2\_/l'0))) as f2. destruct f2; try auto.
          assert (pc' <: l \/ pc'0 <: l)
            by (destruct Hpc; destruct H7; eauto using flows_trans, join_2_rev, join_minimal).
          unprime H9 H11. unprime H10 H11. invsc H10. invsc H16.
          contradiction.
      SSSCase "Throw". (* spurious *)
        destruct a. 
        remember (flows_dec (l1 \_/pc') (l0\_/(pc2\_/l'0))) as f1.
        destruct f1.
        SSSSCase "first check succeeds".
          assert (pc' <: l \/ pc'0 <: l)
            by (destruct Hpc; destruct H7; eauto using flows_trans, join_2_rev, join_minimal).
          pose proof (eq_res'_inversion_st (b,l1) _ e _ _ H11). contradiction.
        SSSSCase "first check fails".
          remember (flows_dec pc'0 (l0\_/(pc2\_/l'0))) as f2. destruct f2; try auto.
          assert (pc' <: l \/ pc'0 <: l)
            by (destruct Hpc; destruct H7; eauto using flows_trans, join_2_rev, join_minimal).
          pose proof (eq_res'_inversion_st (b,l1) _ e _ _ H11). contradiction.
    SSCase "Throw". 
      SSSCase "Suc". (* spurious *)
        destruct a.
        remember (flows_dec pc' (l0\_/(pc2\_/l'0))) as f1.
        destruct f1.
        SSSSCase "first check succeeds".
          assert (pc' <: l \/ pc'0 <: l)
            by (destruct Hpc; destruct H7; eauto using flows_trans, join_2_rev, join_minimal).
          pose proof (eq_res'_inversion_ts (b,l1) _ e _ l H11). contradiction.
        SSSSCase "first check fails".
          remember (flows_dec (l1\_/pc'0) (l0\_/(pc2\_/l'0))) as f2. destruct f2; try auto.
          assert (pc' <: l \/ pc'0 <: l)
            by (destruct Hpc; destruct H7; eauto using flows_trans, join_2_rev, join_minimal).
          pose proof (eq_res'_inversion_ts (b,l1) _ e _ l H11). contradiction.
      SSSCase "Throw".
        remember (flows_dec pc' (l0\_/(pc2\_/l'0))) as f1. 
        remember (flows_dec pc'0 (l0\_/(pc2\_/l'0))) as f2.
        destruct f1; destruct f2; try auto; 
        assert (pc' <: l \/ pc'0 <: l) as Hpcfinal
          by (destruct Hpc; destruct H7; eauto using flows_trans, join_2_rev, join_minimal);
        unprime H10 Hpcfinal; invsc H10; eauto using eq_box_refl; try contradiction.
  SCase "Throw". (* spurious *)
    solve_var Heq_env H H8. invsc H5.
    assert (l'0 <: l \/ l'0 <: l) by (destruct Hpc; eauto using join_2_rev).
    specialize (H14 H5). invsc H14. invsc H7. absurdTag H12.
Case "eval_bracket_no_lab". 
  withPc Hpc. pose proof (pc_eval_monotonic _ _ _ _ _ Heval2).
  assert (pc <: l \/ pc2 <: l) by (destruct Hpc; eauto using join_1_rev, flows_trans).
  unprime Heq_env H2. invsc Heval2.
  SCase "Suc". (* spurious *)
    solve_var Heq_env H H7. invsc H4.
    assert (l'0 <: l \/ l'0 <: l) by (destruct Hpc; eauto using join_2_rev).
    specialize (H13 H4). invsc H13. invsc H8. absurdTag H0.
  SCase "Throw".
    solve_var Heq_env H H7. invsc H4.
    assert (l'0 <: l \/ l'0 <: l) by (destruct Hpc; eauto using join_2_rev).
    specialize (H13 H4). apply eq_box_eq_propagate in H13. rewrite H13.
    eauto using eq_res_refl.
Case "eval_label_of". invsc Heval2. withPc Hpc.
  unprime Heq_env Hpc. solve_var Heq_env H H2. invsc H1.
  split; auto.
Case "eval_get_pc". invsc Heval2. withPc Hpc.
  unprime Heq_env Hpc. split; auto.
Case "eval_to_sum". invsc Heval2. withPc Hpc. unprime Heq_env Hpc.
  solve_var Heq_env H H2. invsc H1.
  split; eauto. split; auto. constructor. constructor; auto. intro. 
  specialize (H9 H1). invsc H9; unfold to_sum_box; try invsc H3; 
  eauto; constructor; constructor; eauto.
Case "eval_throw". invsc Heval2. withPc Hpc. 
  assert (pc <: l \/ pc2 <: l) by (destruct Hpc; eauto using join_1_rev).
  unprime Heq_env H0. solve_var Heq_env H H2. invsc H3; auto.
  assert (l0 <: l \/ l0 <: l) by (destruct Hpc; eauto using join_2_rev).
  specialize (H10 H3). invsc H10; unfold throw_excp; try invsc H4; eauto.
Case "eval_catch_no_excp".
  withPc Hpc. pose proof (pc_eval_monotonic _ _ _ _ _ H).
  pose proof (pc_eval_monotonic _ _ _ _ _ Heval2).
  assert (pc <: l \/ pc2 <: l) by (destruct Hpc; eauto using flows_trans).
  unprime Heq_env H2. invsc Heval2.
  SCase "Suc".
    useIH IHeval l H11. unprime H5 Hpc. eauto.
  SCase "Throw". (* spurious *)
    useIH IHeval l H11.
    pose proof (pc_eval_monotonic _ _ _ _ _ H12).
    assert (pc' <: l \/ pc'0 <: l) by (destruct Hpc; eauto using flows_trans).
    pose proof (eq_res'_inversion_st a _ ex _ _ H7). contradiction.
Case "eval_catch_excp".
  withPc Hpc. pose proof (pc_eval_monotonic _ _ _ _ _ H).
pose proof (pc_eval_monotonic _ _ _ _ _ H0).
  pose proof (pc_eval_monotonic _ _ _ _ _ Heval2).
  assert (pc <: l \/ pc2 <: l) by (destruct Hpc; eauto using flows_trans).
  unprime Heq_env H4. invsc Heval2.
  SCase "Suc". (* spurious *)
    useIH IHeval1 l H13.
    assert (pc' <: l \/ pc2' <: l) by (destruct Hpc; eauto using flows_trans).
    pose proof (eq_res'_inversion_ts a _ ex _ _ H8). contradiction.
  SCase "Throw".
    useIH IHeval1 l H13.
    pose proof (pc_eval_monotonic _ _ _ _ _ H14).
    assert (pc' <: l \/ pc'0 <: l) by (destruct Hpc; eauto using flows_trans).
    unprime H7 H9. invsc H7.
    useIH IHeval2 l H14.
    unprime H11 Hpc. eauto.
Qed.

Theorem non_interference: forall r1 t pc1 res1 pc1' r2 pc2 res2 pc2' l,
    eq_env' r1 pc1 r2 pc2 l ->
    r1 |- t, pc1 ==> res1, pc1' ->
    r2 |- t, pc2 ==> res2, pc2' ->
    eq_res' res1 pc1' res2 pc2' l.
Proof.
  intros r1 t pc1 res1 pc1' r2 pc2 res2 pc2' l
    Hequiv_env Heval1 Heval2.
  assert (eq_env' r1 pc1' r2 pc2' l /\ eq_res' res1 pc1' res2 pc2' l) by
    eauto using non_interference_strong.
  intuition.
Qed.
