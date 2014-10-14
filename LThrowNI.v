Require Import Terms.
Require Import LBracketSyntax.
Require Import LThrowBigStep.
Require Import LBracketEquiv.

(** Monotonicity of the pc label. This property is essential for the
    non-interference proof to go through. *)
Lemma pc_eval_monotonic: forall r t pc a pc', 
  r |- t, pc ==> a, pc' -> pc <: pc'.
Proof.
  intros r t pc a pc' Heval.
  (eval_cases (induction Heval) Case);
    intros; eauto 4 using flows_refl, flows_trans, join_1_rev.
Qed.

(* Various helpers respect equality *)
Lemma eq_val_eq_bop : forall b v11 v12 v21 v22 l,
  eq_val v11 v21 l ->
  eq_val v12 v22 l ->
  bop_result b v11 v12 = bop_result b v21 v22.
Proof.
  intros b v11 v12 v21 v22 l Heq1 Heq2.
  inversion Heq1; eauto.
  inversion Heq2; eauto.
Qed.

Inductive eq_res : Result -> Result -> Lab -> Prop :=
| eq_s : forall a1 a2 l,
         eq_atom a1 a2 l ->
         eq_res (Suc a1) (Suc a2) l
| eq_t : forall e l, eq_res (Throw e) (Throw e) l.
Hint Constructors eq_res.

Definition eq_res' res1 pc1 res2 pc2 l :=
  (pc1 <: l \/ pc2 <: l) ->
  (pc1 = pc2 /\ eq_res res1 res2 l).

Lemma eq_res_refl : forall res l, eq_res res res l.
Proof. pose proof eq_refl. destruct res; intuition. Qed.

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

(*
Lemma eq_val_eq_bracket_val : forall r1 r2 l pc l',
  eq_res r1 r2 l ->
  eq_val (bracket_val r1 pc l') (bracket_val r2 pc l') l.
Proof.
  intros r1 r2 l pc l' Heq.
  inversion Heq; unfold bracket_val; subst.
  Case "Suc".
    rename H into Hflow; rename H0 into Heq_a.
    inversion Heq_a. subst. rename l2 into la. rename H5 into Heq_v.
    specialize (Heq_v Hflow).
    destruct (flows_dec (la \_/ pc) l'); econstructor; eauto.
  Case "Throw".
    destruct (flows_dec pc l'); econstructor; eauto.
Qed.
*)

(* random label helper *)

Lemma lt_disj:
  forall l1 l2 l1' l2' l,
    (l1 <: l \/ l2 <: l) -> l1' <: l1 -> l2' <: l2 ->
    (l1' <: l \/ l2' <: l).
intros. destruct H.
 assert (h: l1' <: l) by (eapply (flows_trans _ _ _ H0 H)). tauto.
 assert (h: l2' <: l) by (eapply (flows_trans _ _ _ H1 H)). tauto.
Qed. 

(** * Non-interference *)

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
    intros r2 pc2 res2 pc2'; try (rename l into l1); 
    intros l Heval2 Heq_env.
  Case "eval_var". invsc Heval2.
    rename H into Hv1. rename H2 into Hv2. intuition. 
    pose proof (maps_eq_env' _ _ _ _ _ _ _ _ Heq_env Hv1 Hv2); 
    econstructor; specialize (H H0); invsc H; eauto.
  Case "eval_const". invsc Heval2. intuition.
    intro H. apply Heq_env in H. intuition.
  Case "eval_let".
    rename r into r1. rename a into a1. rename pc into pc1. 
    rename pc' into pc1'. rename pc'' into pc1''. rename res into res1.
    rename H into Heval11. rename H0 into Heval12.
    invsc Heval2; rename pc2' into pc2''; rename H6 into Heval21.
    SCase "Suc".
      rename a into a2. rename H7 into Heval22.
        (* IH *)
      apply IHeval1 with (l:=l) in Heval21; try assumption.
      destruct Heval21 as [Heq_env1 Heq_res1].
      apply IHeval2 with (l:=l) in Heval22.
      destruct Heval22 as [Heq_env2 Heq_res2].
      intuition. eapply eq_env'_cons_inv_env; try assumption. apply Heq_env2.
      apply cons_eq_env'.
      intros Hpc. specialize (Heq_res1 Hpc). invsc Heq_res1.
      split. reflexivity. invsc H0. assumption.
      assumption.
    SCase "Throw". (* spurious case due to inversion of Heval21... *)
      apply IHeval1 with (l:=l) in Heval21; try assumption.
      invsc Heval21. apply intro_and2. intros Hpc.
      pose proof (pc_eval_monotonic _ _ _ _ _ Heval12) as Hpc1'.
      apply eq_res'_inversion_st in H0. inversion H0.
      destruct Hpc; eauto using flows_trans.
  Case "eval_let_fail".
    rename r into r1. rename pc into pc1. rename pc' into pc1'.
    rename H into Heval1. invsc Heval2; rename H6 into Heval21.
    SCase "Suc". (* spurious case due to inversion... *)
      apply IHeval with (l:=l) in Heval21; eauto.
      apply intro_and2. intros Hpc.
      destruct Heval21 as [Heq_env' Heq_res'].
      apply eq_res'_inversion_ts in Heq_res'. inversion Heq_res'.
      pose proof (pc_eval_monotonic _ _ _ _ _ H7) as Hpc1'.
      destruct Hpc; eauto using flows_trans.      
    SCase "Throw".
      rename ex into ex1. rename ex0 into ex2.
      apply IHeval with (l := l) in Heval21; eauto.
  Case "eval_abs". invsc Heval2. 
    rename r into r1. rename pc into pc1. intuition.
    intros Hpc. specialize (Heq_env Hpc).
    invsc Heq_env. rename H0 into Heq_env.
    intuition.
  Case "eval_app".
    rename r into r1. rename r' into rc1. rename x into x1. rename t into t1.
    rename H into Hc1. rename H0 into Ha1. rename H1 into Heval1.
    rename pc into pc1. rename pc' into pc1'. rename a into a1. 
    invsc Heval2.
    SCase "Suc".
      rename r' into rc2. rename x into x2. rename t into t2. 
      rename l0 into l2. rename a into a2.
      rename H1 into Hc2. rename H3 into Ha2. rename H7 into Heval2.
        (* get the equalities we want *)
      pose proof (maps_eq_env' _ _ _ _ _ _ _ _ Heq_env Hc1 Hc2) as Heq_clo.
      pose proof (maps_eq_env' _ _ _ _ _ _ _ _ Heq_env Ha1 Ha2) as Heq_arg.
      apply intro_and2. intro Hpc'.
      assert (pc1 <: l \/ pc2 <: l) as Hpc by 
        (destruct Hpc'; eauto using pc_eval_monotonic, flows_trans).
      specialize (Heq_clo Hpc). specialize (Heq_arg Hpc).
      destruct Heq_clo as [Heqpc Heq_clo].
      invsc Heqpc. rename pc2 into pc. clear H.
      destruct Heq_arg as [_ Heq_arg].
        (* get deeper equality on the closure *)
      invsc Heq_clo. rename H5 into Heq_clo.
      assert (l2 <: l \/ l2 <: l) as Hflows' by 
        (destruct Hpc'; eauto using pc_eval_monotonic, flows_trans, 
          flows_join_left).
      specialize (Heq_clo Hflows'). clear Hflows'.
      invsc Heq_clo. rename H6 into Heq_envc.
      rename x2 into x. rename t2 into t. rename l2 into lc.
        (* apply the IH *)
      apply IHeval with (l:=l) in Heval2.
      destruct Heval2 as [Heq_env' Heq_res].
      specialize (Heq_env' Hpc'). specialize (Heq_res Hpc').
      destruct Heq_env' as [Heqpc Heq_env'].
      invsc Heqpc. rename pc2' into pc'. clear H.
      destruct Heq_res as [_ Heq_res].
      specialize (Heq_env Hpc). destruct Heq_env as [_ Heq_env].
      eauto.
        (* resolve last env equality *)
      apply cons_eq_env'; intros Hpclc; eauto.
    SCase "Throw". (* spurious case due to inversion of Heval2... *)
      rename l0 into l2. rename v' into v2.
      rename H2 into Hc2. rename H6 into Htag.
        (* get the closure (in)equality we want *)
      pose proof (maps_eq_env' _ _ _ _ _ _ _ _ Heq_env Hc1 Hc2) as Heq_clo.
      apply intro_and2. intros Hpc'.
      assert (pc1 <: l \/ pc2 <: l) as Hpc by 
        (destruct Hpc'; eauto using pc_eval_monotonic, flows_trans).
      specialize (Heq_clo Hpc).
      destruct Heq_clo as [Heqpc Heq_clo]. invsc Heqpc. rename pc2 into pc.
      invsc Heq_clo. rename H6 into Heq_clo.
      assert (l2 <: l \/ l2 <: l) as Hflows' by 
        (destruct Hpc'; eauto using pc_eval_monotonic, flows_trans, 
          flows_join_left).
      specialize (Heq_clo Hflows'). clear Hflows'.
      invsc Heq_clo. simpl in Htag. 
      assert (TagFun = TagFun) as Htag' by reflexivity.
      contradiction.
  Case "eval_app_etype".
    rename v' into v1. rename r into r1. 
    rename H into Hv1. rename H0 into Htag1. rename pc into pc1.
    invsc Heval2.
    SCase "Suc". (* spurious *)
      rename H1 into Hv2. rename l0 into l2. 
      pose proof (maps_eq_env' _ _ _ _ _ _ _ _ Heq_env Hv1 Hv2) as Heq_clo.
      apply intro_and2. intros Hpc'.
      assert (pc1 <: l \/ pc2 <: l) as Hpc by
        (destruct Hpc'; eauto using pc_eval_monotonic, flows_trans, 
          flows_join_left).
      specialize (Heq_clo Hpc). destruct Heq_clo as [Heqpc Heq_clo].
      invsc Heqpc. clear H. rename pc2 into pc.
      invsc Heq_clo. rename H6 into Heq_clo.
      apply pc_eval_monotonic in H7. apply join_2_rev in H7.
      (* why can't eauto figure this out? *)
      assert (l2 <: l \/ l2 <: l) as Hflows'.
        left. destruct Hpc'. eapply join_2_rev. eassumption.
        eapply flows_trans. eassumption. assumption.
      specialize (Heq_clo Hflows'). clear Hflows'.
      invsc Heq_clo. simpl in Htag1.
      assert (TagFun = TagFun) as Htag' by reflexivity.
      contradiction.
    SCase "Throw".
      rename v' into v2. rename l0 into l2. 
      rename H2 into Hv2. rename H6 into Htag2.
      apply intro_and2. intros Hpc'.
      assert (pc1 <: l \/ pc2 <: l) as Hpc by
        (destruct Hpc'; eauto using pc_eval_monotonic, flows_trans, 
          flows_join_left).
      specialize (Heq_env Hpc). destruct Heq_env as [Heq_pc Heq_env].
      invsc Heq_pc. rename pc2 into pc. clear H.
      pose proof (maps_eq_env _ _ _ _ _ _ Heq_env Hv1 Hv2) as Heq_clo.
      invsc Heq_clo; eauto.
  Case "eval_inx". invsc Heval2.
    rename r into r1. rename a into a1. rename H into Ha1. rename pc into pc1.
    rename a0 into a2. rename pc2' into pc2. rename H6 into Ha2.
    split. assumption.
    intros Hpc. specialize (Heq_env Hpc). destruct Heq_env as [Heqpc Heq_env].
    invsc Heqpc. rename pc2 into pc. clear H.
    split. reflexivity.
    eauto using maps_eq_env.
  Case "eval_match".
    rename r into r1. rename d into d1. rename a into a1.
    rename pc into pc1. rename pc' into pc1'. rename H into Ha1.
    rename H0 into Heval1. invsc Heval2.
    SCase "Suc".
      rename a into a2. rename l0 into l2. rename d into d2.
      rename H7 into Ha2. rename H8 into Heval2.
      apply intro_and2. intros Hpc'.
      pose proof (pc_eval_monotonic _ _ _ _ _ Heval1) as Hpc1.
      pose proof (pc_eval_monotonic _ _ _ _ _ Heval2) as Hpc2.
      assert (pc1 <: l \/ pc2 <: l) as Hpc.
        destruct Hpc'; [left | right].
          eapply join_1_rev. eapply flows_trans. apply Hpc1. assumption. 
          eapply join_1_rev. eapply flows_trans. apply Hpc2. assumption.
      specialize (Heq_env Hpc). destruct Heq_env as [Heqpc Heq_env].
      invsc Heqpc. rename pc2 into pc. clear H.
      pose proof (maps_eq_env _ _ _ _ _ _ Heq_env Ha1 Ha2) as Heq_a.
      invsc Heq_a. rename H5 into Heq_a.
      assert (l2 <: l \/ l2 <: l) as Hflows by
        (destruct Hpc'; eauto using pc_eval_monotonic, flows_trans, 
          flows_join_left).
      specialize (Heq_a Hflows). invsc Heq_a.
      rename H4 into Heq_a. rename d2 into d. rename l2 into la.
      apply IHeval with (l:=l) in Heval2.
      destruct Heval2 as [Heq_env' Heq_res'].
      specialize (Heq_env' Hpc'). specialize (Heq_res' Hpc').
      destruct Heq_env' as [Heqpc Heq_env']. invsc Heqpc; eauto.
      apply cons_eq_env'; intros Hpcla; eauto.
   SCase "Throw". (* spurious *)
      rename v into v2. rename l0 into l2. 
      rename H7 into Ha2. rename H8 into Htag2.
      apply intro_and2. intros Hpc'.
      assert (pc1 <: l \/ pc2 <: l) as Hpc.
        destruct Hpc'.
          left. eapply join_1_rev. eapply flows_trans.
          eapply pc_eval_monotonic. apply Heval1. assumption.
          right. eapply join_1_rev. apply H.
      specialize (Heq_env Hpc). destruct Heq_env as [Heqpc Heq_env].
      invsc Heqpc. rename pc2 into pc. clear H.
      pose proof (maps_eq_env _ _ _ _ _ _ Heq_env Ha1 Ha2) as Heq_a.
      invsc Heq_a. rename H5 into Heq_a.
      assert (l2 <: l \/ l2 <: l) as Hflows by
        (destruct Hpc'; eauto using pc_eval_monotonic, flows_trans, 
          flows_join_left). 
      specialize (Heq_a Hflows). invsc Heq_a. rename H3 into Heq_a.
      simpl in Htag2.
      contradict Htag2; reflexivity.
  Case "eval_match_etype".
    rename v into v1. rename r into r1. rename pc into pc1.
    rename H into Ha1. rename H0 into Htag. invsc Heval2.
    SCase "Suc". (* spurious *)
      rename a into a2. rename l0 into l2. 
      rename H7 into Ha2. rename H8 into Heval2. rename Htag into Htag1.
      apply intro_and2. intros Hpc'.
      pose proof (pc_eval_monotonic _ _ _ _ _ Heval2) as Hpc2.
      assert (pc1 <: l \/ pc2 <: l) as Hpc.
        destruct Hpc'; [left | right].
          eapply join_1_rev. apply H. 
          eapply join_1_rev. eapply flows_trans. apply Hpc2. assumption.
      specialize (Heq_env Hpc). destruct Heq_env as [Heqpc Heq_env].
      invsc Heqpc. rename pc2 into pc. clear H.
      pose proof (maps_eq_env _ _ _ _ _ _ Heq_env Ha1 Ha2) as Heq_a.
      invsc Heq_a. rename H5 into Heq_a.
      assert (l2 <: l \/ l2 <: l) as Hflows by
        (destruct Hpc'; eauto using pc_eval_monotonic, flows_trans, 
          flows_join_left).
      specialize (Heq_a Hflows). invsc Heq_a. rename H3 into Heq_a.
      simpl in Htag1.
      contradict Htag1; reflexivity.
    SCase "Throw".
      rename v into v2. rename l0 into l2.
      rename H7 into Ha2. rename H8 into Htag2.
      apply intro_and2. intros Hpc'.
      assert (pc1 <: l \/ pc2 <: l) as Hpc by
        (destruct Hpc'; eauto using pc_eval_monotonic, flows_trans, 
          flows_join_left).
      specialize (Heq_env Hpc). destruct Heq_env as [Heqpc Heq_env].
      invsc Heqpc. rename pc2 into pc. clear H.
      pose proof (maps_eq_env _ _ _ _ _ _ Heq_env Ha1 Ha2) as Heq_a.
      invsc Heq_a. eauto.
  Case "eval_tag". invsc Heval2.
    rename v into v1. rename r into r1. rename H into Ha1.
    rename v0 into v2. rename l0 into l2. rename H2 into Ha2.
    apply intro_and2. intros Hpc'.
    specialize (Heq_env Hpc'). invsc Heq_env. rename H0 into Heq_env.
    split; eauto.
    pose proof (maps_eq_env _ _ _ _ _ _ Heq_env Ha1 Ha2) as Heq_a.
    split. reflexivity. invsc Heq_a. rename H5 into Heq_a. constructor. 
    constructor; auto. intros Hl2. specialize (Heq_a Hl2).
    assert (tag_of v1 = tag_of v2) as Heq_tag by eauto using eq_val_eq_tag.
    rewrite Heq_tag. eauto.
  Case "eval_bop".
    rename pc into pc1, v' into v11, v'' into v12, H into Hv11, H0 into Hv12,
      l0' into l11, l0'' into l12, r into r1.
    invsc Heval2. rename v' into v21, v'' into v22, l0' into l21, 
      l0'' into l22, H6 into Hv21, H7 into Hv22.
    apply intro_and2. intros Hpc'.
    assert (pc1 <: l \/ pc2 <: l) as Hpc by 
      (destruct Hpc'; eauto using join_1_rev).
    specialize (Heq_env Hpc). invsc Heq_env.
    rename H0 into Heq_env, pc2 into pc.
    pose proof (maps_eq_env _ _ _ _ _ _ Heq_env Hv11 Hv21) as Heq_a1.
    pose proof (maps_eq_env _ _ _ _ _ _ Heq_env Hv12 Hv22) as Heq_a2.
    invsc Heq_a1. rename H5 into Heq_v1, l21 into l1.
    invsc Heq_a2. rename H5 into Heq_v2, l22 into l2.
    split; eauto. split. reflexivity.
    assert (l1 <: l \/ l1 <: l) as Hl1 by 
      (destruct Hpc'; eauto using join_1_rev, join_2_rev).
    assert (l2 <: l \/ l2 <: l) as Hl2 by 
      (destruct Hpc'; eauto using join_2_rev).
    assert (bop_result b v11 v12 = bop_result b v21 v22) as Heq_bop by
      eauto using eq_val_eq_bop. rewrite Heq_bop. eauto using eq_res_refl.
  Case "eval_bracket".
    rename l' into l1', r into r1, pc into pc1, pc' into pc1', res into res1, 
      H0 into Heval1, H into Hl1.
    invsc Heval2.
    SCase "Suc".
      rename l0 into l2, l' into l2', res into res2, pc' into pc2', 
        H2 into Hl2, H6 into Heval2.
      apply intro_and2. intros Hpc'.
      assert (pc1 <: l \/ pc2 <: l) as Hpc by 
        (destruct Hpc'; eauto using join_1_rev).
      specialize (Heq_env Hpc). invsc Heq_env.
      rename H0 into Heq_env, pc2 into pc.
      pose proof (maps_eq_env _ _ _ _ _ _ Heq_env Hl1 Hl2) as Heq_l.
      invsc Heq_l. rename H5 into Heq_l.
      assert (l2' <: l \/ l2' <: l) as Hflows by
        (destruct Hpc'; eauto using pc_eval_monotonic, flows_trans, 
          flows_join_left).
      specialize (Heq_l Hflows). invsc Heq_l. 
      rename l2 into la, l2' into la'.
      split. eauto. split. reflexivity.
        (* apply the IH! *)
      pose proof (pc_eval_monotonic _ _ _ _ _ Heval1) as Hpc1'.
      pose proof (pc_eval_monotonic _ _ _ _ _ Heval2) as Hpc2'.
      apply IHeval with (l:=l) in Heval2.
      destruct Heval2 as [Heq_env' Heq_res].
      constructor. constructor. reflexivity. intros Hla.
        (* lengthy case analysis on the results, opening up bracket_val *)
      destruct res1.
      SSCase "Suc1".
        destruct res2.
        SSSCase "Suc2".
          destruct a as [v1 l1]. destruct a0 as [v2 l2].
          remember (flows_dec (l1 \_/ pc1') (la \_/ (pc \_/ la'))) as f1.
          destruct f1 as [Hflow1 | Hnotflow1].
          SSSSCase "pc1' flow check succeeds".
            assert (pc1' <: l \/ pc2' <: l) as Hpc'' by
              (destruct Hpc'; destruct Hla; 
                eauto using join_2_rev, flows_trans, join_minimal).
            specialize (Heq_res Hpc''). invsc Heq_res. rename H0 into Heq_res.
            invsc Heq_res. rename H1 into Heq_a. invsc Heq_a.
            rename H5 into Heq_v.
            apply or_elimrefl in Hpc. apply or_elimrefl in Hflows.
            apply or_elimrefl in Hpc'. apply or_elimrefl in Hpc''.
            apply or_elimrefl in Hla.
            simpl. rewrite <- Heqf1. clear Heqf1.
            assert (l2 <: l \/ l2 <: l) as Hl2f by 
              eauto using join_minimal, flows_join_left, flows_trans, 
                join_1_rev.
            specialize (Heq_v Hl2f). econstructor; eauto.
          SSSSCase "pc1' flow check fails".
            simpl. rewrite <- Heqf1.
            remember (flows_dec (l2 \_/ pc2') (la \_/ (pc \_/ la'))) as f2.
            destruct f2 as [Hflow2 | Hnotflow2].
            SSSSSCase "pc2' flow check succeeds". (* spurious *)
              assert (pc1' <: l \/ pc2' <: l) as Hpc'' by
                (destruct Hpc'; destruct Hla; 
                  eauto using join_2_rev, flows_trans, join_minimal).
              specialize (Heq_res Hpc''). invsc Heq_res. 
              rename H0 into Heq_res. invsc Heq_res. 
              rename H1 into Heq_a. invsc Heq_a. contradiction.
            SSSSSCase "pc2' flow check fails".
              econstructor; eauto.
        SSSCase "Throw2". 
          remember (flows_dec pc2' (la \_/ (pc \_/ la'))) as f2.
          destruct f2 as [Hflow2 | Hnotflow2].
          SSSSCase "pc2' flow check succeeds". (* spurious *)
            assert (pc1' <: l \/ pc2' <: l) as Hpc'' by
              (destruct Hpc'; destruct Hla; 
                eauto using join_2_rev, flows_trans, join_minimal).
              specialize (Heq_res Hpc''). invsc Heq_res. 
              rename H0 into Heq_res. apply eq_res_inversion_st in Heq_res. 
              inversion Heq_res.
          SSSSCase "pc2' flow check fails".
            destruct a as [v1 l1].
            remember (flows_dec (l1 \_/ pc1') (la \_/ (pc \_/ la'))) as f1.
            destruct f1 as [Hflow1 | Hnotflow1].
            SSSSSCase "pc1' flow check succeeds". (* spurious *)
              assert (pc1' <: l \/ pc2' <: l) as Hpc'' by
                (destruct Hpc'; destruct Hla; 
                  eauto using join_2_rev, flows_trans, join_minimal).
              specialize (Heq_res Hpc''). invsc Heq_res. 
              rename H0 into Heq_res. apply eq_res_inversion_st in Heq_res. 
              inversion Heq_res.
            SSSSSCase "pc1' flow check fails".
              unfold bracket_val.
              rewrite <- Heqf1. rewrite <- Heqf2.
              econstructor; eauto.
      SSCase "Throw1".
        destruct res2.
        SSSCase "Suc2".
          destruct a as [v2 l2].
          remember (flows_dec (l2 \_/ pc2') (la \_/ (pc \_/ la'))) as f2.
          destruct f2 as [Hflow2 | Hnotflow2].
          SSSSCase "pc2' flow check succeeds". (* spurious *)
            assert (pc1' <: l \/ pc2' <: l) as Hpc'' by
              (destruct Hpc'; destruct Hla; 
                eauto using join_2_rev, flows_trans, join_minimal).
              specialize (Heq_res Hpc''). invsc Heq_res. 
              rename H0 into Heq_res. apply eq_res_inversion_ts in Heq_res. 
              inversion Heq_res.
          SSSSCase "pc2' flow check fails".
            remember (flows_dec pc1' (la \_/ (pc \_/ la'))) as f1.
            destruct f1 as [Hflow1 | Hnotflow1].
            SSSSSCase "pc1' flow check succeeds". (* spurious *)
              assert (pc1' <: l \/ pc2' <: l) as Hpc'' by
                (destruct Hpc'; destruct Hla; 
                  eauto using join_2_rev, flows_trans, join_minimal).
              specialize (Heq_res Hpc''). invsc Heq_res. 
              rename H0 into Heq_res. apply eq_res_inversion_ts in Heq_res. 
              inversion Heq_res.
            SSSSSCase "pc1' flow check fails".
              unfold bracket_val.
              rewrite <- Heqf1. rewrite <- Heqf2.
              econstructor; eauto.
        SSSCase "Throw2".
          remember (flows_dec pc1' (la \_/ (pc \_/ la'))) as f1.
          destruct f1 as [Hflow1 | Hnotflow1].
          SSSSSCase "pc1' flow check succeeds".
            remember (flows_dec pc2' (la \_/ (pc \_/ la'))) as f2.
            destruct f2 as [Hflow2 | Hnotflow2];
              (assert (pc1' <: l \/ pc2' <: l) as Hpc'' by
                 (destruct Hpc'; destruct Hla; 
                   eauto using join_2_rev, flows_trans, join_minimal);
               specialize (Heq_res Hpc''); invsc Heq_res;
               rename H0 into Heq_res; invsc Heq_res; 
               unfold bracket_val; rewrite <- Heqf1;
               econstructor; eauto).
          SSSSSCase "pc1' flow check fails".
            remember (flows_dec pc2' (la \_/ (pc \_/ la'))) as f2.
            destruct f2 as [Hflow2 | Hnotflow2].
            SSSSSSCase "pc2' flow check succeeds".
              (assert (pc1' <: l \/ pc2' <: l) as Hpc'' by
                   (destruct Hpc'; destruct Hla; 
                     eauto using join_2_rev, flows_trans, join_minimal);
                 specialize (Heq_res Hpc''); invsc Heq_res;
                 rename H0 into Heq_res; invsc Heq_res; 
                 unfold bracket_val; rewrite <- Heqf1;
                 econstructor; eauto).
            SSSSSSCase "pc2' flow check fails".
              unfold bracket_val. rewrite <- Heqf1. rewrite <- Heqf2.
              econstructor; eauto.
        (* final env obligation *)
      intros _. eauto.
    SCase "Throw". (* spurious *)
      rename v into v2, l0 into l2, H2 into Hl2, H6 into Htag2.
      apply intro_and2. intro Hpc'.
      assert (pc1 <: l \/ pc2 <: l) as Hpc by 
        (destruct Hpc'; eauto using join_1_rev).
      specialize (Heq_env Hpc). invsc Heq_env.
      rename H0 into Heq_env, pc2 into pc.
      pose proof (maps_eq_env _ _ _ _ _ _ Heq_env Hl1 Hl2) as Heq_l.
      invsc Heq_l. rename H5 into Heq_l.
      assert (l2 <: l \/ l2 <: l) as Hflows by
        (destruct Hpc'; eauto using pc_eval_monotonic, flows_trans, 
          flows_join_left).
      specialize (Heq_l Hflows). invsc Heq_l. 
      contradict Htag2. reflexivity.
  Case "eval_bracket_etype".
    rename v into v1, r into r1, H into Hv1, H0 into Htag1, pc into pc1.
    invsc Heval2.
    SCase "Suc". (* spurious *)
      rename res into res2, l0 into l2, l' into l2', H2 into Hv2, 
        H6 into Heval2.
      apply intro_and2. intro Hpc'.
      assert (pc1 <: l \/ pc2 <: l) as Hpc by 
        (destruct Hpc'; eauto using join_1_rev).
      specialize (Heq_env Hpc). invsc Heq_env.
      rename H0 into Heq_env, pc2 into pc.
      pose proof (maps_eq_env _ _ _ _ _ _ Heq_env Hv1 Hv2) as Heq_v.
      invsc Heq_v. rename H5 into Heq_l.
      assert (l2' <: l \/ l2' <: l) as Hflows by
        (destruct Hpc'; eauto using join_2_rev).
      specialize (Heq_l Hflows). invsc Heq_l.
      contradict Htag1. reflexivity.
    SCase "Throw".
      rename v into v2, l0 into l2, H2 into Hv2, H6 into Htag2.
      apply intro_and2. intro Hpc'.
      assert (pc1 <: l \/ pc2 <: l) as Hpc by 
        (destruct Hpc'; eauto using join_1_rev).
      specialize (Heq_env Hpc). invsc Heq_env.
      rename H0 into Heq_env, pc2 into pc.
      pose proof (maps_eq_env _ _ _ _ _ _ Heq_env Hv1 Hv2) as Heq_v.
      invsc Heq_v. eauto.
  Case "eval_label_of". invsc Heval2.
    rename H into Hv1, H2 into Hv2.
    apply intro_and2. intro Hpc'.
    specialize (Heq_env Hpc').
    invsc Heq_env. rename H0 into Heq_env.
    pose proof (maps_eq_env _ _ _ _ _ _ Heq_env Hv1 Hv2) as Heq_v.
    invsc Heq_v. split; eauto.
  Case "eval_get_pc". invsc Heval2.
    split; intros Hpc; eauto.
    specialize (Heq_env Hpc). invsc Heq_env; eauto.
  Case "eval_throw". invsc Heval2.
    rename pc into pc1, r into r1, v into v1, H into Hv1, v0 into v2,
      l0 into l2, H2 into Hv2.
    apply intro_and2. intro Hpc'.
    assert (pc1 <: l \/ pc2 <: l) as Hpc by 
      (destruct Hpc'; eauto using join_1_rev).
    specialize (Heq_env Hpc).
    invsc Heq_env. rename H0 into Heq_env.
    pose proof (maps_eq_env _ _ _ _ _ _ Heq_env Hv1 Hv2) as Heq_v.
    invsc Heq_v. rename H5 into Heq_v.
    assert (l2 <: l \/ l2 <: l) as Hl2 by 
      (destruct Hpc'; eauto using join_2_rev).
    specialize (Heq_v Hl2). invsc Heq_v; eauto.
  Case "eval_catch_no_excp".
    rename r into r1, pc into pc1, pc' into pc1', a into a1, H into Heval1.
    invsc Heval2.
    SCase "Suc".
      rename a into a2, H6 into Heval2.
      apply intro_and2. intro Hpc'.
      assert (pc1 <: l \/ pc2 <: l) as Hpc by 
        (destruct Hpc'; eauto using pc_eval_monotonic, flows_trans).
      specialize (Heq_env Hpc). invsc Heq_env. rename H0 into Heq_env.
      apply IHeval with (l:=l) in Heval2; try (intros _; eauto).
      destruct Heval2 as [Heq_env' Heq_res].
      specialize (Heq_env' Hpc'). specialize (Heq_res Hpc').
      invsc Heq_env'. rename H0 into Heq_env'. destruct Heq_res as [_ Heq_res].
      eauto.      
    SCase "Throw". (* spurious *)
      rename pc2' into pc2'', pc' into pc2', H6 into Heval2, H7 into Heval2'.
      apply intro_and2. intro Hpc'.
      assert (pc1 <: l \/ pc2 <: l) as Hpc by 
        (destruct Hpc'; eauto using pc_eval_monotonic, flows_trans).
      specialize (Heq_env Hpc). invsc Heq_env. rename H0 into Heq_env.
      apply IHeval with (l:=l) in Heval2; try (intros _; eauto).
      destruct Heval2 as [Heq_env' Heq_res].
      apply eq_res'_inversion_st in Heq_res. inversion Heq_res.
      destruct Hpc'; eauto using pc_eval_monotonic, flows_trans.
  Case "eval_catch_excp".
    rename r into r1, pc into pc1, pc' into pc1', pc'' into pc1'',
      ex into ex1, H into Heval11, H0 into Heval12.
    invsc Heval2.
    SCase "Suc". (* spurious *)
      rename a into a2, H6 into Heval2.
      apply intro_and2. intro Hpc'.
      assert (pc1 <: l \/ pc2 <: l) as Hpc by 
        (destruct Hpc'; eauto using pc_eval_monotonic, flows_trans).
      specialize (Heq_env Hpc). invsc Heq_env. rename H0 into Heq_env.
      apply IHeval1 with (l:=l) in Heval2; try (intros _; eauto).
      destruct Heval2 as [Heq_env' Heq_res].
      apply eq_res'_inversion_ts in Heq_res. inversion Heq_res.
      destruct Hpc'; eauto using pc_eval_monotonic, flows_trans.
    SCase "Throw". 
      rename ex into ex2, pc2' into pc2'', pc' into pc2', 
        H6 into Heval21, H7 into Heval22.
      apply intro_and2. intro Hpc''.
      assert (pc1 <: l \/ pc2 <: l) as Hpc by 
        (destruct Hpc''; eauto using pc_eval_monotonic, flows_trans).
      pose proof (pc_eval_monotonic _ _ _ _ _ Heval12) as Hpc1'.
      pose proof (pc_eval_monotonic _ _ _ _ _ Heval22) as Hpc2'.
      assert (pc1' <: l \/ pc2' <: l) as Hpc' by 
        (destruct Hpc''; eauto using flows_trans).
      specialize (Heq_env Hpc). invsc Heq_env. rename H0 into Heq_env.
      apply IHeval1 with (l:=l) in Heval21; try (intros _; eauto).
      destruct Heval21 as [Heq_env' Heq_res]. rename pc2 into pc.
      specialize (Heq_env' Hpc'). specialize (Heq_res Hpc').
      invsc Heq_env'. rename H0 into Heq_env'. destruct Heq_res as [_ Heq_res].
      rename pc2' into pc'.
      apply IHeval2 with (l:=l) in Heval22.
      destruct Heval22 as [Heq_env'' Heq_res'].
      specialize (Heq_env'' Hpc''). specialize (Heq_res' Hpc'').
      invsc Heq_res'; eauto.
      invsc Heq_res. apply cons_eq_env'; intros _; eauto.
Qed.


(** Finally, non-interference. *)

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
