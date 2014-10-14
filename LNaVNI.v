Require Import Terms.
Require Import LNaVSyntax.
Require Import LNaVBigStep.

(** * Equivalences *)

(** Low-equivalence judgments. *)
Inductive eq_atom : Atom -> Atom -> Lab -> Prop :=
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
Hint Constructors eq_atom eq_box eq_val eq_env.
Scheme eq_atom_ind' := Minimality for eq_atom Sort Prop
with eq_box_ind' := Minimality for eq_box Sort Prop
with eq_val_ind' := Minimality for eq_val Sort Prop
with eq_env_ind' := Minimality for eq_env Sort Prop.

Combined Scheme eq_mutind from eq_val_ind', eq_box_ind', eq_atom_ind', eq_env_ind'.

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
  (forall b l, eq_box b b l) /\
  (forall a l, eq_atom a a l) /\
  (forall r l, eq_env r r l).
Proof. apply val_box_atom_env_mutind; eauto. Qed.

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
  bop_box b b11 b12 = bop_box b b21 b22.
Proof.
  intros b b11 b12 b21 b22 l Heq1 Heq2.
  invsc Heq1; eauto; invsc Heq2; eauto;
  destruct b; invsc H; try invsc H0; eauto.
Qed.

(** * Non-interference *)

(** Strengthened version of non-interference. *)
Lemma non_interference_strong :
  forall r1 t pc1 a1 pc1',
    r1 |- t, pc1 ==> a1, pc1' ->
      forall r2 pc2 a2 pc2' l,
        r2 |- t, pc2 ==> a2, pc2' ->
          eq_env' r1 pc1 r2 pc2 l ->
          (eq_env' r1 pc1' r2 pc2' l /\
            eq_atom' a1 pc1' a2 pc2' l).
Proof.
  intros r1 t pc1 a1 pc1' H.
  (eval_cases (induction H) Case);
  intros r2 pc2 a2 pc2'; try (rename l into l1); intro l;
    intros Heval2 Heq_env; invsc Heval2.
  Case "eval_var". eauto using maps_eq_env'.
  Case "eval_const". intuition.
    intros Hpc. specialize (Heq_env Hpc). invsc Heq_env; eauto.
  Case "eval_let".
    apply intro_and2. intro Hpc.
    pose proof (pc_eval_monotonic _ _ _ _ _ H).
    pose proof (pc_eval_monotonic _ _ _ _ _ H0).
    pose proof (pc_eval_monotonic _ _ _ _ _ H8).
    pose proof (pc_eval_monotonic _ _ _ _ _ H9).
    assert (pc <: l \/ pc2 <: l) by (destruct Hpc; eauto using flows_trans).
    assert (pc' <: l \/ pc2' <: l) by (destruct Hpc; eauto using flows_trans).
    specialize (Heq_env H5). invsc Heq_env.
    apply IHeval1 with (l:=l) in H8; try (intro; eauto). destruct H8.
    apply IHeval2 with (l:=l) in H9; eauto using cons_eq_env'. destruct H9.
    specialize (H11 Hpc). invsc H11; eauto.
  Case "eval_abs". intuition.
    intros Hpc. specialize (Heq_env Hpc). invsc Heq_env; eauto.
    apply intro_and2. intro Hpc.
    pose proof (pc_eval_monotonic _ _ _ _ _ H1).
    pose proof (pc_eval_monotonic _ _ _ _ _ H10).
    pose proof (maps_eq_env' _ _ _ _ _ _ _ _ Heq_env H H4).
    pose proof (maps_eq_env' _ _ _ _ _ _ _ _ Heq_env H0 H6).
    assert (pc <: l \/ pc2 <: l) by 
      (destruct Hpc; eauto using join_1_rev, flows_trans).
    specialize (H5 H8). invsc H5. specialize (H7 H8). invsc H7.
    invsc H11. assert (l0 <: l \/ l0 <: l) by
      (destruct Hpc; eauto using join_2_rev, flows_trans).
    specialize (H17 H7). invsc H17. invsc H13.
    specialize (Heq_env H8). invsc Heq_env.
    apply IHeval with (l:=l) in H10. invsc H10.
    specialize (H14 Hpc). invsc H14; eauto.
    apply cons_eq_env'; intro; eauto.
    SCase "type error". (* spurious *)
      apply intro_and2. intro Hpc.
      pose proof (pc_eval_monotonic _ _ _ _ _ H1).
      assert (pc <: l \/ pc2 <: l) by 
        (destruct Hpc; eauto using join_1_rev, flows_trans).
      pose proof (maps_eq_env' _ _ _ _ _ _ _ _ Heq_env H H5).
      specialize (H4 H3). invsc H4. invsc H7.
      assert (l0 <: l \/ l0 <: l) by 
        (destruct Hpc; eauto using join_2_rev, flows_trans).
      specialize (H13 H4). invsc H13. invsc H7.
      simpl in H9. exfalso; auto.
  Case "eval_app_no_abs".
    SCase "no type error". (* spurious *)
      apply intro_and2. intro Hpc.
      pose proof (pc_eval_monotonic _ _ _ _ _ H9).
      assert (pc <: l \/ pc2 <: l) by 
        (destruct Hpc; eauto using join_1_rev, flows_trans).
      pose proof (maps_eq_env' _ _ _ _ _ _ _ _ Heq_env H H3).
      specialize (H4 H2). invsc H4. invsc H7.
      assert (l0 <: l \/ l0 <: l) by 
        (destruct Hpc; eauto using join_2_rev, flows_trans).
      specialize (H13 H4). invsc H13. invsc H8.
      simpl in H0. exfalso; auto.
    SCase "eval_app_no_abs".
      apply intro_and2. intro Hpc.
      assert (pc <: l \/ pc2 <: l) by 
        (destruct Hpc; eauto using join_1_rev, flows_trans).
      specialize (Heq_env H1). invsc Heq_env.
      pose proof (maps_eq_env _ _ _ _ _ _ H3 H H4).
      invsc H2.
      assert (l0 <: l \/ l0 <: l) by 
        (destruct Hpc; eauto using join_2_rev, flows_trans).
      specialize (H12 H2). invsc H12; eauto.
  Case "eval_inx". intuition.
    intros Hpc. specialize (Heq_env Hpc). invsc Heq_env.  
    pose proof (maps_eq_env _ _ _ _ _ _ H1 H H6). eauto using maps_eq_env.
  Case "eval_match".
    pose proof (pc_eval_monotonic _ _ _ _ _ H0).
    pose proof (pc_eval_monotonic _ _ _ _ _ H10).
    apply intro_and2. intro Hpc.
    assert (pc <: l \/ pc2 <: l) by 
      (destruct Hpc; eauto using flows_trans, join_1_rev).
    specialize (Heq_env H3). invsc Heq_env.
    pose proof (maps_eq_env _ _ _ _ _ _ H5 H H9).
    invsc H4. assert (l0 <: l \/ l0 <: l) by 
      (destruct Hpc; eauto using flows_trans, join_2_rev).
    specialize (H14 H4). invsc H14. invsc H8.
    apply IHeval with (l:=l) in H10. invsc H10. specialize (H7 Hpc).
    invsc H7. eauto. eapply cons_eq_env'; intro; eauto.
    SCase "type error". (* spurious *)
      pose proof (pc_eval_monotonic _ _ _ _ _ H0).
      apply intro_and2. intro Hpc.
      assert (pc <: l \/ pc2 <: l) by 
        (destruct Hpc; eauto using flows_trans, join_1_rev).
      specialize (Heq_env H2). invsc Heq_env.
      pose proof (maps_eq_env _ _ _ _ _ _ H4 H H9).
      invsc H3. assert (l0 <: l \/ l0 <: l) by 
        (destruct Hpc; eauto using flows_trans, join_2_rev).
      specialize (H13 H3). invsc H13. invsc H6.
      simpl in H10. exfalso; auto.
  Case "eval_match_no_sum". SCase "no type error". (* spurious *)
    pose proof (pc_eval_monotonic _ _ _ _ _ H10).
    apply intro_and2. intro Hpc.
    assert (pc <: l \/ pc2 <: l) by 
      (destruct Hpc; eauto using flows_trans, join_1_rev).
    specialize (Heq_env H2). invsc Heq_env.
    pose proof (maps_eq_env _ _ _ _ _ _ H4 H H9).
    invsc H3. assert (l0 <: l \/ l0 <: l) by 
      (destruct Hpc; eauto using flows_trans, join_2_rev).
    specialize (H13 H3). invsc H13. invsc H7.
    simpl in H0. exfalso; auto.
    SCase "type error".
      apply intro_and2. intro Hpc.
      assert (pc <: l \/ pc2 <: l) by 
        (destruct Hpc; eauto using flows_trans, join_1_rev).
      specialize (Heq_env H1). invsc Heq_env.
      pose proof (maps_eq_env _ _ _ _ _ _ H3 H H9).
      invsc H2. assert (l0 <: l \/ l0 <: l) by 
        (destruct Hpc; eauto using flows_trans, join_2_rev).
      specialize (H12 H2). invsc H12; eauto. 
  Case "eval_tag".
    apply intro_and2. intro Hpc. specialize (Heq_env Hpc).
    invsc Heq_env. pose proof (maps_eq_env _ _ _ _ _ _ H1 H H2).
    invsc H0. split. auto. split. reflexivity.
    constructor. reflexivity. intro. specialize (H9 H0).
    unfold tag_box; invsc H9; eauto. invsc H3; eauto.
  Case "eval_bop".
    apply intro_and2. intro Hpc. specialize (Heq_env Hpc). invsc Heq_env. 
    pose proof (maps_eq_env _ _ _ _ _ _ H2 H H8).
    pose proof (maps_eq_env _ _ _ _ _ _ H2 H0 H9).
    split. intuition. split. reflexivity. invsc H1. invsc H3.
    constructor. reflexivity. intro.
    assert (l'0 <: l \/ l'0 <: l) by 
      (destruct H1; eauto using flows_trans, join_1_rev).
    assert (l''0 <: l \/ l''0 <: l) by 
      (destruct H1; eauto using flows_trans, join_2_rev).
    specialize (H12 H3). specialize (H11 H4).
    pose proof (eq_box_eq_bop bo _ _ _ _ l H12 H11).
    rewrite H5. apply eq_box_refl.
  Case "eval_bracket".
    pose proof (pc_eval_monotonic _ _ _ _ _ H0).
    pose proof (pc_eval_monotonic _ _ _ _ _ H8).
    apply intro_and2. intro Hpc.
    assert (pc <: l \/ pc2 <: l) by (destruct Hpc; eauto using join_1_rev).
    specialize (Heq_env H3). invsc Heq_env. 
    pose proof (maps_eq_env _ _ _ _ _ _ H6 H H4).
    invsc H5.
    assert (l'0 <: l \/ l'0 <: l) by (destruct Hpc; eauto using join_2_rev).
    specialize (H14 H5). invsc H14. invsc H10. split. intuition. split. reflexivity.
    apply IHeval with (l:=l) in H8; try (intro; eauto). invsc H8.
    remember (flows_dec (l'' \_/ pc') (l0 \_/ (pc2 \_/ l'0))) as f1.
    remember (flows_dec (l''0 \_/ pc'0) (l0 \_/ (pc2 \_/ l'0))) as f2.
    destruct f1; destruct f2; constructor; auto; intro.
    SCase "flow, flow".
      assert (pc' <: l \/ pc'0 <: l) by 
        (destruct H8; destruct Hpc; eauto using join_2_rev, flows_trans, join_minimal).
      specialize (H9 H10). invsc H9. invsc H12. 
      apply H17. 
      destruct H8; destruct Hpc; eauto using join_1_rev, flows_trans, join_minimal. 
    SCase "flow, no flow". (* spurious *)
      assert (pc' <: l \/ pc'0 <: l) by 
        (destruct H8; destruct Hpc; eauto using join_2_rev, flows_trans, join_minimal).
      specialize (H9 H10). invsc H9. invsc H12. 
      contradiction.
    SCase "no flow, flow". (* spurious *)
      assert (pc' <: l \/ pc'0 <: l) by 
        (destruct H8; destruct Hpc; eauto using join_2_rev, flows_trans, join_minimal).
      specialize (H9 H10). invsc H9. invsc H12. 
      contradiction.
  Case "eval_bracket". SCase "type error". (* spurious *)
    apply intro_and2. intro Hpc.
    pose proof (pc_eval_monotonic _ _ _ _ _ H0).
    assert (pc <: l \/ pc2 <: l) by 
      (destruct Hpc; eauto using join_1_rev, flows_trans).
    specialize (Heq_env H2). invsc Heq_env.
    pose proof (maps_eq_env _ _ _ _ _ _ H5 H H4).
    invsc H3.
    assert (l'0 <: l \/ l'0 <: l) by 
      (destruct Hpc; eauto using join_2_rev, flows_trans).
    specialize (H13 H3). invsc H13. invsc H7.
    simpl in H8. exfalso; auto.
  Case "eval_bracket_no_lab". SCase "no type error". (* spurious *)
    apply intro_and2. intro Hpc.
    pose proof (pc_eval_monotonic _ _ _ _ _ H8).
    assert (pc <: l \/ pc2 <: l) by 
      (destruct Hpc; eauto using join_1_rev, flows_trans).
    specialize (Heq_env H2). invsc Heq_env.
    pose proof (maps_eq_env _ _ _ _ _ _ H5 H H4).
    invsc H3.
    assert (l'0 <: l \/ l'0 <: l) by 
      (destruct Hpc; eauto using join_2_rev, flows_trans).
    specialize (H13 H3). invsc H13. invsc H9.
    simpl in H0. exfalso; auto.
  Case "eval_bracket_no_lab".
    apply intro_and2. intro Hpc.
    assert (pc <: l \/ pc2 <: l) by (destruct Hpc; eauto using join_1_rev).
    specialize (Heq_env H1). invsc Heq_env.
    pose proof (maps_eq_env _ _ _ _ _ _ H3 H H4).
    invsc H2.
    assert (l'0 <: l \/ l'0 <: l) by (destruct Hpc; eauto using join_2_rev).
    specialize (H12 H2). invsc H12; eauto.
  Case "eval_label_of".
    apply intro_and2. intro Hpc.
    specialize (Heq_env Hpc). invsc Heq_env.
    pose proof (maps_eq_env _ _ _ _ _ _ H1 H H2).
    invsc H0. split; eauto.
  Case "eval_get_pc".
    apply intro_and2. intro Hpc.
    specialize (Heq_env Hpc). invsc Heq_env.
    split; eauto.
  Case "eval_mk_nav".
    apply intro_and2. intro Hpc.
    specialize (Heq_env Hpc). invsc Heq_env.
    pose proof (maps_eq_env _ _ _ _ _ _ H1 H H2).
    invsc H0. split. intuition. split. reflexivity. constructor. reflexivity.
    intro. specialize (H9 H0). invsc H9; unfold mk_nav_box; try invsc H3; eauto;
    destruct c'; auto.
  Case "eval_to_sum".
    apply intro_and2. intro Hpc. specialize (Heq_env Hpc). invsc Heq_env.
    pose proof (maps_eq_env _ _ _ _ _ _ H1 H H2).
    invsc H0. split. intuition. split. reflexivity. constructor. reflexivity.
    intro. specialize (H9 H0). unfold to_sum_box. invsc H9; constructor; constructor; eauto.
Qed.

(** Finally, non-interference. *)

Theorem non_interference: forall r1 t pc1 a1 pc1' r2 pc2 a2 pc2' l,
    eq_env' r1 pc1 r2 pc2 l ->
    r1 |- t, pc1 ==> a1, pc1' ->
    r2 |- t, pc2 ==> a2, pc2' ->
    eq_atom' a1 pc1' a2 pc2' l.
Proof.
  intros r1 t pc1 a1 pc1' r2 pc2 a2 pc2' l
    Hequiv_env Heval1 Heval2.
  assert (eq_env' r1 pc1' r2 pc2' l /\ eq_atom' a1 pc1' a2 pc2' l) by
    eauto using non_interference_strong.
  intuition.
Qed.
