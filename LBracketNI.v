Require Import Terms.
Require Import LBracketSyntax.
Require Import LBracketBigStep.
Require Import LBracketEquiv.

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
Lemma eq_val_eq_bop : forall b v11 v12 v21 v22 l,
  eq_val v11 v21 l ->
  eq_val v12 v22 l ->
  do_bop b v11 v12 = do_bop b v21 v22.
Proof.
  intros b v11 v12 v21 v22 l Heq1 Heq2.
  inversion Heq1; eauto.
  inversion Heq2; eauto.
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
  Case "eval_var". intuition. eauto using maps_eq_env'.
  Case "eval_const". intuition.
    intro H. apply Heq_env in H. intuition.
  Case "eval_let". 
    rename r into r1.
    rename pc into pc1. rename pc' into pc1'. rename pc'' into pc1''.
    rename a into a1. rename a' into a1'.
    rename pc2' into pc2''. rename pc'0 into pc2'. 
    rename a2 into a2'. rename a0 into a2.
    rename H into Heval1. rename H0 into Heval1'.
    rename H8 into Heval2. rename H9 into Heval2'.
      (* applying the IHs *)
    apply (IHeval1 _ _ _ _ l) in Heval2. 
    destruct Heval2 as [Heq_env1 Heq_atom1].
    apply (IHeval2 _ _ _ _ l) in Heval2'.
    destruct Heval2' as [Heq_env2 Heq_atom2].
    apply eq_env'_cons_inv_env in Heq_env2.
    split; assumption.
    apply cons_eq_env'; assumption.
    assumption.
  Case "eval_abs". intuition.
    intro G. specialize (Heq_env G). destruct Heq_env. subst. auto.
  Case "eval_app".
    rename r into r1. rename pc into pc1. rename pc' into pc1'.
    rename r' into r1'. rename x into x1. rename t into t1.
    rename a into a1. rename a' into a1'.
    rename x0 into x2. rename a2 into a2'. rename a0 into a2.
    rename t0 into t2. rename l0 into l2. rename r'0 into r2'.
    rename H into Hclo1. rename H0 into Harg1. rename H1 into Heval1.
    rename H4 into Hclo2. rename H6 into Harg2. rename H10 into Heval2.
      (* extracting the equalities we need *)
    pose proof (maps_eq_env' _ _ _ _ _ _ _ _ Heq_env Hclo1 Hclo2) as Heq_clo.
    pose proof (maps_eq_env' _ _ _ _ _ _ _ _ Heq_env Harg1 Harg2) as Heq_arg.
    apply intro_and2. intro Hpc'.
    assert (pc1 <: l \/ pc2 <: l) as Hpc.
      destruct Hpc'; [left | right].
      SCase "left".
        eapply join_1_rev. eapply flows_trans.
        apply pc_eval_monotonic in Heval1; apply Heval1; assumption. 
        assumption.
      SCase "right".
        eapply join_1_rev. eapply flows_trans.
        apply pc_eval_monotonic in Heval2; apply Heval2; assumption. 
        assumption.
    pose proof (Heq_clo Hpc) as [Heqpc Heq_clo_atom]. subst. 
    rename pc2 into pc.
    inversion Heq_clo_atom; subst. rename H5 into Heq_clo_val.
    assert (l2 <: l \/ l2 <: l) as Hflows'
      by (destruct Hpc'; eauto using pc_eval_monotonic, flows_trans, flows_join_left).
    specialize (Heq_clo_val Hflows').
    inversion Heq_clo_val. subst. rename x2 into x. rename t2 into t.
    rename H6 into Heq_clo_env.
      (* apply the IH *)
    apply (IHeval _ _ _ _ l) in Heval2.
    destruct Heval2 as [Heq_env' Heq_result].
    pose proof (Heq_env' Hpc') as Heq_env''.
    destruct Heq_env'' as [Heq_pc Heq_env'']. subst.
    specialize (Heq_result Hpc').
    destruct Heq_result as [_ Heq_result].
    inversion Heq_env''. subst. specialize (Heq_env Hpc). destruct Heq_env. eauto.
      (* prove the final environment equality *)
    intros Hpc''.
    assert (pc \_/ l2 <: l) as Hflow by (inversion Hpc''; auto). clear Hpc''.
    split; auto.
    specialize (Heq_env Hpc). destruct Heq_env as [_ Heq_env].
    specialize (Heq_arg Hpc). destruct Heq_arg as [_ Heq_arg].
    eauto.
  Case "eval_inx". intuition.
    pose proof (maps_eq_env' _ _ _ _ _ _ _ _ Heq_env H H6) as Heq_arg.
    intros Hpc. specialize (Heq_arg Hpc). intuition.
  Case "eval_match".
    rename H0 into Heval1. rename H10 into Heval2.
    rename r into r1. rename d into d1. rename a into a1. rename a' into a1'.
    rename pc into pc1. rename pc' into pc1'. rename H into Ha1. 
    rename d0 into d2. rename a2 into a2'. rename a0 into a2.
    rename l0 into l2. rename H9 into Ha2.
      (* extract the equivalence on a1 and a2 *)
    pose proof (maps_eq_env' _ _ _ _ _ _ _ _ Heq_env Ha1 Ha2) as Heq_a.
    apply intro_and2. intros Hpc'.
    assert (pc1 <: l \/ pc2 <: l) as Hpc.
        destruct Hpc'; [left | right].
        SCase "left".
          eapply join_1_rev. eapply flows_trans.
          apply pc_eval_monotonic in Heval1; apply Heval1; assumption. 
          assumption.
        SCase "right".
          eapply join_1_rev. eapply flows_trans.
          apply pc_eval_monotonic in Heval2; apply Heval2; assumption. 
          assumption.
    specialize (Heq_a Hpc). destruct Heq_a as [Heq Heq_a].
    subst. rename pc2 into pc.
    inversion Heq_a; subst. rename H5 into Heq_val.
    assert (l2 <: l \/ l2 <: l) as Hflows'
      by (destruct Hpc'; eauto using pc_eval_monotonic, 
          flows_trans, flows_join_left).
    specialize (Heq_val Hflows').
    inversion Heq_val; subst.
    rename d2 into d. rename a1 into a. rename l2 into l'.
      (* apply the IH *)
    apply (IHeval _ _ _ _ l) in Heval2.
    destruct Heval2 as [Heq_env' Heq_result].
    specialize (Heq_env Hpc). destruct Heq_env as [_ Heq_env].
    specialize (Heq_result Hpc'). specialize (Heq_env' Hpc').
    destruct Heq_env' as [Heq_pc' Heq_env'].
    destruct Heq_result as [_ Heq_result].
    subst. eauto.
      (* prove final environment equality *)
    intros Hpc''.
    assert (pc \_/ l' <: l) as Hflow by (inversion Hpc''; auto). clear Hpc''.
    split; auto.
    specialize (Heq_env Hpc). destruct Heq_env as [_ Heq_env].
    inversion Heq_val. subst.
    eauto. 
  Case "eval_tag".
    rename r into r1. rename pc into pc1. rename v into v1.
    rename v0 into v2. rename pc2' into pc2. rename l0 into l2.
    rename H into Hv1. rename H2 into Hv2.
    pose proof (maps_eq_env' _ _ _ _ _ _ _ _ Heq_env Hv1 Hv2) as Heq_a.
    apply intro_and2. intros Hpc.
    specialize (Heq_env Hpc). specialize (Heq_a Hpc).
    destruct Heq_env as [Heq_pc Heq_env]. destruct Heq_a as [_ Heq_a].
    subst. rename pc2 into pc.
    split; eauto. split. reflexivity.
    inversion Heq_a. subst. rename H5 into Heq_val.
    econstructor. reflexivity. intros Hl2.
    specialize (Heq_val Hl2).
    pose proof (eq_val_eq_tag v1 v2 l Heq_val) as Heq_tag.
    rewrite Heq_tag. eauto.
  Case "eval_bop".
    rename r into r1.
    rename v' into v11. rename l0' into l11. rename H into Hv11.
    rename v'' into v12. rename l0'' into l12. rename H0 into Hv12.
    rename H1 into Htag11. rename H2 into Htag12.
    rename v'0 into v21. rename l0'0 into l21. rename H6 into Hv21.
    rename v''0 into v22. rename l0''0 into l22. rename H8 into Hv22.
    rename H12 into Htag21. rename H13 into Htag22.
    rename pc into pc1. rename pc2' into pc2.
      (* extract the equivalences *)
    pose proof (maps_eq_env' _ _ _ _ _ _ _ _ Heq_env Hv11 Hv21) as Heq_v1.
    pose proof (maps_eq_env' _ _ _ _ _ _ _ _ Heq_env Hv12 Hv22) as Heq_v2.
    apply intro_and2. intros Hpc.
    specialize (Heq_v1 Hpc). destruct Heq_v1 as [Heqpc Heq_a1].
    specialize (Heq_v2 Hpc). destruct Heq_v2 as [_ Heq_a2]. subst.
    split. eauto. split. reflexivity.
    inversion Heq_a1. inversion Heq_a2. subst.
    rename H12 into Heq_v1'. rename H5 into Heq_v2'.
    econstructor. reflexivity. intros Hl. 
    assert (l21 <: l /\ l22 <: l) as [Hl21 Hl22] by (destruct Hl; eauto using or_introl, pc_eval_monotonic, flows_trans, flows_join_left, flows_join_right).
    assert (eq_val v11 v21 l) as Heq_v1 by eauto.
    assert (eq_val v12 v22 l) as Heq_v2 by eauto.
    pose proof (eq_val_eq_bop b v11 v12 v21 v22 l Heq_v1 Heq_v2) as Heq_bop.
    rewrite Heq_bop. apply eq_val_refl.
  Case "eval_bracket".
    rename r into r1. rename l' into l1'. rename pc into pc1.
    rename v into v1. rename l'' into l1''. rename pc' into pc1'.
    rename H into Hl1. rename H0 into Heval1. rename H1 into Hcheck1.
    rename l0 into l2. rename l'0 into l2'. rename l''0 into l2''.
    rename pc'0 into pc2'.
    rename H4 into Hl2. rename H6 into Heval2. rename H10 into Hcheck2.
      (* extracting equalities (this is getting familiar!) *)
    pose proof (maps_eq_env' _ _ _ _ _ _ _ _ Heq_env Hl1 Hl2) as Heq_l.
    apply intro_and2. intros Hpc.
    assert (pc1 <: l \/ pc2 <: l) as Hpclow by (destruct Hpc; eauto using or_introl, pc_eval_monotonic, flows_trans, flows_join_left, flows_join_right).
    specialize (Heq_l Hpclow). destruct Heq_l as [Heqpc Heq_l].
    subst. rename pc2 into pc. inversion Heq_l. subst. rename H5 into Heq_v.
    assert (l2' <: l \/ l2' <: l) as Hl2' by (destruct Hpc; eauto using or_introl, pc_eval_monotonic, flows_trans, flows_join_left, flows_join_right).
    specialize (Heq_v Hl2'). inversion Heq_v. subst.
    rename l2 into l'. rename l2' into l''.
    pose proof (pc_eval_monotonic _ _ _ _ _ Heval1) as Hpc1.
    pose proof (pc_eval_monotonic _ _ _ _ _ Heval2) as Hpc2.
      (* apply the IH *)
    apply (IHeval _ _ _ _ l) in Heval2. destruct Heval2 as [Heq_env' Heq_a].
    split. split. reflexivity.
    specialize (Heq_env Hpclow). destruct Heq_env; auto.
    split. reflexivity.
    econstructor; auto. intros Hl'.
      (* AUGH why do I need to do this so manually?! *)
    assert (pc1' <: l \/ pc2' <: l) as Hpc' by (destruct Hpc; destruct Hl'; eauto using join_2_rev, flows_trans, join_minimal).
    specialize (Heq_a Hpc'). destruct Heq_a as [Heq_pc Heq_v']. subst.
    inversion Heq_v'. subst. rename l2'' into l_result. rename H5 into Heq_v''.
    apply or_elimrefl in Hl'.
    apply or_elimrefl in Hpc'. clear Hpc2. rename pc2' into pc'.
    apply or_elimrefl in Hl2'.
    apply or_elimrefl in Hpc.
    assert (l_result <: l \/ l_result <: l) as Hlr by (eauto using join_1_rev, flows_trans, join_minimal).
    apply Heq_v''. assumption.
      (* final env proof... *)
    intros Hpcl''. split. reflexivity.
    apply Heq_env. assumption.
  Case "eval_label_of".
    rename l0 into l2. rename v0 into v2.
    rename pc into pc1. rename r into r1. rename v into v1.
    rename H into Hv1. rename H2 into Hv2.
    pose proof (maps_eq_env' _ _ _ _ _ _ _ _ Heq_env Hv1 Hv2) as Heq_v.
    apply intro_and2. intros Hpc.
    specialize (Heq_env Hpc). specialize (Heq_v Hpc).
    destruct Heq_env as [Heq_pc Heq_env]. destruct Heq_v as [_ Heq_v].
    subst. rename pc2' into pc.
    split. split. reflexivity. assumption. split. reflexivity.
    inversion Heq_v. subst. eauto.
  Case "eval_get_pc". split. assumption.
    intros Hpc. apply Heq_env in Hpc. destruct Hpc. subst. 
    split. reflexivity.
    apply eq_a. auto. intros. apply eq_vconst.
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
  assert (eq_env' r1 pc1' r2 pc2' l /\
    eq_atom' a1 pc1' a2 pc2' l) by eauto using non_interference_strong.
  intuition.
Qed.

(** Simpler non-interference statement  *)
Theorem simpler_non_interference: forall t pc r1 a1 pc1' r2 a2 pc2' l,
    eq_env r1 r2 l ->
    r1 |- t, pc ==> a1, pc1' ->
    r2 |- t, pc ==> a2, pc2' ->
    pc1' <: l \/ pc2' <: l ->
    pc1' = pc2' /\ eq_atom a1 a2 l.
Proof.
  intros t pc r1 a1 pc1' r2 a2 pc2' l
    Hequiv_env Heval1 Heval2.
  eapply non_interference. unfold eq_env'. intro.
  split; [reflexivity | apply Hequiv_env].
  eassumption. eassumption.
Qed.

(* Note: formally non_interference is not implied by
   simpler_non_interference because non_interference quantifies over 2
   initial pc's. One can convincingly argue though, that one doesn't
   need two pcs in the final theorem, and that if one starts with
   equal pcs then this invariant is preserved. *)

(* Showing that simpler_non_interference_two_pcs implies
   non_interference *)

Definition simpler_non_interference_two_pcs_def :=
  forall t pc1 pc2 r1 a1 pc1' r2 a2 pc2' l,
    eq_env r1 r2 l ->
    r1 |- t, pc1 ==> a1, pc1' ->
    r2 |- t, pc2 ==> a2, pc2' ->
    pc1' <: l \/ pc2' <: l ->
    pc1' = pc2' /\ eq_atom a1 a2 l.

Definition non_interference_def :=
  forall r1 t pc1 a1 pc1' r2 pc2 a2 pc2' l,
    eq_env' r1 pc1 r2 pc2 l ->
    r1 |- t, pc1 ==> a1, pc1' ->
    r2 |- t, pc2 ==> a2, pc2' ->
    eq_atom' a1 pc1' a2 pc2' l.

Lemma simpler_non_interference_two_pcs_implies_non_interference:
  simpler_non_interference_two_pcs_def ->
  non_interference_def.
Proof. unfold non_interference_def, simpler_non_interference_two_pcs_def.
  intro simpler_non_interference_two_pcs.
  intros. intro Hflows.
  eapply simpler_non_interference_two_pcs; try eassumption.
  apply H. destruct Hflows as [Hflows|Hflows].
  left. eapply flows_trans. eapply pc_eval_monotonic. eassumption. trivial.
  right. eapply flows_trans. eapply pc_eval_monotonic. eassumption. trivial.
Qed.

(* Showing that non_interference implies non_interference_strong *)

Definition non_interference_strong_def :=
  forall r1 t pc1 a1 pc1',
    r1 |- t, pc1 ==> a1, pc1' ->
      forall r2 pc2 a2 pc2' l,
        r2 |- t, pc2 ==> a2, pc2' ->
          eq_env' r1 pc1 r2 pc2 l ->
          (eq_env' r1 pc1' r2 pc2' l /\
            eq_atom' a1 pc1' a2 pc2' l).

Lemma non_interference_implies_non_interference_strong:
  non_interference_def ->
  non_interference_strong_def.
Proof. unfold non_interference_def, non_interference_strong_def.
  intro non_interference.
  intros. split.
  intro Hflows. unfold eq_env' in H1.
    split.
      unfold eq_atom' in non_interference.
        eapply non_interference; eassumption.
      apply H1. destruct Hflows as [Hflows|Hflows].
        left. eapply flows_trans. eapply pc_eval_monotonic.
          eassumption. trivial.
        right. eapply flows_trans. eapply pc_eval_monotonic.
          eassumption. trivial.
  eapply non_interference; eassumption.
Qed.
