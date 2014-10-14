Require Import Terms.
Require Import LNaVSyntax.
Require Import LNaVBigStep. (* reusing helpers *)

(** * Small-step Semantics *)

Inductive Frame : Type :=
| RLet : Var -> Tm -> Frame
| RRet : Env -> Frame
| RBrk : Lab -> Lab -> Frame. (* final label + original pc *)

Definition Cont := list Frame.

Inductive RCfg : Type :=
| CR : Tm -> RCfg    (* term to be reduced *)
| CA : (prod Box Lab) -> RCfg.  (* return atom *)

Definition Cfg := prod (prod (prod Lab Env) Cont) RCfg.

Notation "<< pc , r , k , X >>" := (((pc, r), k), X) (at level 5).

(** The reduction relation. *)
Reserved Notation "c1 --> c2" (at level 80).
Inductive step : Cfg -> Cfg -> Prop :=
  (* var *)
  | step_var : forall pc r k x a,
    maps r x a ->
    <<pc, r, k, CR (TVar x)>> --> <<pc, r, k, CA a>>
  (* const *)
  | step_const : forall pc r k c,
    <<pc, r, k, CR (TConst c)>> --> <<pc, r, k, CA (V (VConst c),bot)>>
  (* let *)
  | step_let_start : forall pc r k x t1 t2,
    << pc, r, k, CR (TLet x t1 t2) >> --> << pc, r, RLet x t2 :: k, CR t1 >>
  | step_let_bind : forall pc r k x t a,
    << pc, r, RLet x t :: k, CA a >> --> << pc, (x,a) :: r, RRet r :: k, CR t >>
  (* abs *)
  | step_abs : forall pc r k x t,
    << pc, r, k, CR (TAbs x t) >> --> << pc, r, k, CA (V (VClos r x t),bot) >>
  (* app *)
  | step_app : forall pc r k x1 x2 r' x t l a2,
    maps r x1 (V (VClos r' x t),l) ->
    maps r x2 a2 ->
    << pc, r, k, CR (TApp x1 x2) >> --> << pc\_/l, (x,a2) :: r', RRet r :: k, CR t >>
  | step_app_error : forall pc r k x1 x2 b l,
    maps r x1 (b,l) ->
    ~ is_box is_abs b ->
    << pc, r, k, CR (TApp x1 x2) >> --> << pc\_/l, r, k, CA (D (propagate_nav b),bot) >>
  (* return *)
  | step_ret : forall pc r k r' a,
    << pc, r, RRet r' :: k, CA a >> --> << pc, r', k, CA a >>
  (* inx *)
  | step_inx : forall pc r k d x a,
    maps r x a ->
    << pc, r, k, CR (TInx d x) >> --> << pc, r, k, CA (V (VInx d a),bot) >>
  (* match *)
  | step_match : forall pc r k x y t1 t2 d a l,
    maps r x (V (VInx d a),l) ->
    << pc, r, k, CR (TMatch x y t1 t2) >> -->
    << pc\_/l, (y,a) :: r, RRet r :: k, CR (d_choose d t1 t2) >>
  | step_match_error : forall pc r k x y t1 t2 b l,
    maps r x (b,l) ->
    ~ is_box is_sum b ->
    << pc, r, k, CR (TMatch x y t1 t2) >> -->
    << pc\_/l, r, k, CA (D (propagate_nav b),bot) >>
  (* tag *)
  | step_tag : forall pc r k x b l,
    maps r x (b,l) ->
    << pc, r, k, CR (TTag x) >> --> << pc, r, k, CA (tag_box b,l) >>
  (* bop *)
  | step_bop : forall pc r k bo x1 x2 b1 l1 b2 l2,
    maps r x1 (b1,l1) ->
    maps r x2 (b2,l2) ->
    << pc, r, k, CR (TBOp bo x1 x2) >> --> << pc, r, k, CA (bop_box bo b1 b2, l1 \_/ l2) >>
  (* brackets *)
  | step_bracket_start : forall pc r k x t l l',
    maps r x (V (VConst (CLab l)),l') ->
    << pc, r, k, CR (TBracket x t) >> --> << pc\_/l', r, RBrk l (pc\_/l') :: k, CR t >>
  | step_bracket_start_error : forall pc r k x t b l',
    maps r x (b,l') ->
    ~ is_box is_lab b ->
    << pc, r, k, CR (TBracket x t) >> --> << pc\_/l', r, k, CA (D (propagate_nav b),bot) >>
  | step_bracket_end : forall pc r k l' pc' b l'',
    << pc, r, RBrk l' pc' :: k, CA (b,l'') >> -->
    << pc', r, k, CA ((if flows_dec (l'' \_/ pc) (l' \_/ pc') then b else D eBracket),l') >>
  (* label_of *)
  | step_labelof : forall pc r k x b l,
    maps r x (b,l) ->
    << pc, r, k, CR (TLabelOf x) >> --> << pc, r, k, CA (V (VConst (CLab l)),bot) >>
  (* get_pc *)
  | step_getpc : forall pc r k,
    << pc, r, k, CR TGetPc >> --> << pc, r, k, CA (V (VConst (CLab pc)),bot) >>
  (* mk_nav *)
  | step_mknav : forall pc r k x b l, 
    maps r x (b,l) ->
    << pc, r, k, CR (TMkNav x) >> --> << pc, r, k, CA (mk_nav_box b,l) >>
  (* to_sum *)
  | step_tosum : forall pc r k x b l,
    maps r x (b,l) ->
    << pc, r, k, CR (TToSum x) >> --> << pc, r, k, CA (to_sum_box b,l) >>
where "c1 --> c2" := (step c1 c2).
Hint Constructors step.

Tactic Notation "step_cases" tactic(first) ident(c) :=
  first; [
    Case_aux c "step_var"
  | Case_aux c "step_const"
  | Case_aux c "step_let_start"
  | Case_aux c "step_let_bind"
  | Case_aux c "step_abs"
  | Case_aux c "step_app"
  | Case_aux c "step_app_error"
  | Case_aux c "step_ret"
  | Case_aux c "step_inx"
  | Case_aux c "step_match"
  | Case_aux c "step_match_error"
  | Case_aux c "step_tag"
  | Case_aux c "step_bop"
  | Case_aux c "step_bracket_start"
  | Case_aux c "step_bracket_start_error"
  | Case_aux c "step_bracket_end"
  | Case_aux c "step_labelof"
  | Case_aux c "step_getpc"
  | Case_aux c "step_mknav"
  | Case_aux c "step_tosum"
  ].

Require Import Relation_Operators.
Definition steps := clos_refl_trans Cfg step.
Notation "c1 '-->*' c2" := (steps c1 c2) (at level 55, c2 at next level).

Inductive final : Cfg -> Prop :=
  | fa : forall pc r a,
    final << pc, r, [], CA a >>.
Hint Constructors final.

(** Checking that final_cfgs are really stuck (sanity check)
-- the original unwind rule could be applied forever.
*)
Lemma final_stuck : forall c,
  final c ->
  ~(exists c', c --> c').
Proof.
  intros c H Hc. destruct Hc as [c' Hc].
  (step_cases (destruct Hc) Case); invsc H.
Qed.

Definition binds r x := exists a:Atom, maps r x a.
Definition extending r x (P:Env->Tm->Prop) := (fun tm => forall a:Atom, P ((x,a)::r) tm).

Inductive wf_tm : Env -> Tm -> Prop :=
  (* var *)
  | wf_var : forall r x, binds r x -> wf_tm r (TVar x)
  (* const *)
  | wf_const : forall r c, wf_tm r (TConst c)
  (* let *)
  | wf_let : forall r x t1 t2, wf_tm r t1 -> extending r x wf_tm t2 -> wf_tm r (TLet x t1 t2)
  (* abs *)
  | wf_abs : forall r x t, extending r x wf_tm t -> wf_tm r (TAbs x t)
  (* app *)
  | wf_app : forall r x1 x2, binds r x1 -> binds r x2 -> wf_tm r (TApp x1 x2)
  (* inx *)
  | wf_inx : forall r d x, binds r x -> wf_tm r (TInx d x)
  (* match *)
  | wf_match : forall r x y t1 t2,
    binds r x -> extending r y wf_tm t1 -> extending r y wf_tm t2 -> wf_tm r (TMatch x y t1 t2)
  (* tag *)
  | wf_tag : forall r x, binds r x -> wf_tm r (TTag x)
  (* bop *)
  | wf_bop : forall r bo x1 x2, binds r x1 -> binds r x2 -> wf_tm r (TBOp bo x1 x2)
  (* brackets *)
  | wf_bracket : forall r x t, binds r x -> wf_tm r t -> wf_tm r (TBracket x t)
  (* label_of *)
  | wf_labelof : forall r x, binds r x -> wf_tm r (TLabelOf x)
  (* get_pc *)
  | wf_getpc : forall r, wf_tm r TGetPc
  (* mk_nav *)
  | wf_mknav : forall r x, binds r x -> wf_tm r (TMkNav x)
  (* to_sum *)
  | wf_tosum : forall r x, binds r x -> wf_tm r (TToSum x).

Inductive wf_atom : Env -> Atom -> Prop :=
  | wf_a : forall r b l, wf_box r b -> wf_atom r (b,l)
with wf_box : Env -> Box -> Prop :=
  | wfb_d : forall r e, wf_box r (D e)
  | wfv_const : forall r c, wf_box r (V (VConst c))
  | wfv_inx : forall r d a, wf_atom r a -> wf_box r (V (VInx d a))
  | wfv_clos : forall r r' x t, 
    extending r' x wf_tm t -> wf_env r' -> wf_box r (V (VClos r' x t))
with wf_env : Env -> Prop := 
  | wfe_nil : wf_env []
  | wfe_cons : forall x a r, wf_atom r a -> wf_env r -> wf_env ((x,a)::r).

Inductive wf_cont : Env -> Cont -> Prop :=
  | wfk_nil : forall r, wf_cont r []
  | wf_rlet : forall r x t k, extending r x wf_tm t -> wf_cont r k -> wf_cont r (RLet x t :: k)
  | wf_rbrk : forall r l pc k, wf_cont r k -> wf_cont r (RBrk l pc :: k)
  | wf_rret : forall r r' k, wf_cont r' k -> wf_cont r (RRet r' :: k).

Inductive wf_config : Cfg -> Prop :=
  | wf_cr : forall pc r k t, wf_env r -> wf_tm r t -> wf_cont r k -> wf_config <<pc,r,k,CR t>>
  | wf_ca : forall pc r k a, wf_env r -> wf_atom r a -> wf_cont r k -> wf_config <<pc,r,k,CA a>>.

Hint Constructors wf_tm wf_atom wf_box wf_env wf_cont wf_config.

Ltac binding H := unfold binds in H; destruct H.

Ltac by_rule Hrule := eexists; eapply Hrule; eauto; simpl; auto.

Theorem progress_imp : forall c,
  wf_config c -> final c \/ exists c', c --> c'.
Proof.
  intros c Hwf. invsc Hwf.
  Case "CR".
    right.
    (Tm_cases (destruct t) SCase); invsc H0; eauto.
    SCase "TVar". binding H4. by_rule step_var.
    SCase "TApp".
      binding H5. binding H6. destruct x. destruct b.
      destruct v1; try solve [by_rule step_app_error].
      by_rule step_app.
      by_rule step_app_error.
    SCase "TInx". binding H4. by_rule step_inx.
    SCase "TMatch". binding H6. destruct x. destruct b.
      destruct v1; try solve [by_rule step_match_error].
      by_rule step_match.
      by_rule step_match_error.
    SCase "TTag". binding H4. destruct x. by_rule step_tag.
    SCase "TBOp". binding H5. binding H7. destruct x. destruct x0. by_rule step_bop.
    SCase "TBracket". binding H5. destruct x. destruct b.
      destruct v0; try solve [by_rule step_bracket_start_error].
      destruct c; try solve [by_rule step_bracket_start_error].
      by_rule step_bracket_start.
      by_rule step_bracket_start_error.
    SCase "TLabelOf". binding H4. destruct x. by_rule step_labelof.
    SCase "TMkNav". binding H4. destruct x. by_rule step_mknav.
    SCase "TToSum". binding H4. destruct x. by_rule step_tosum.
  Case "CA".
    destruct k.
    SCase "Done".
      left. auto.
    SCase "Has frame". destruct f; invsc H1; right.
      SSCase "RLet". by_rule step_let_bind.
      SSCase "RRet". by_rule step_ret.
      SSCase "RBrk". destruct a. by_rule step_bracket_end.
Qed.      

(** * Proving this small-step semantics equivalent to the big-step one *)

Lemma big_to_small : forall r t pc a pc' k,
  r |- t, pc ==> a, pc' ->
  <<pc, r, k, CR t>> -->* <<pc', r, k, CA a>>.
Proof.
  intros r t pc a pc' k He. generalize dependent k.
  (eval_cases (induction He) Case); intro k; try solve [apply rt_step; eauto].
  Case "eval_let".
    eapply rt_trans. auto using rt_step, step_let_start. 
    eapply rt_trans. apply IHHe1.
    eapply rt_trans. auto using rt_step, step_let_bind. 
    eapply rt_trans. apply IHHe2.
    auto using rt_step, step_ret.
  Case "eval_app".
    eapply rt_trans. apply rt_step. eapply step_app; eauto.
    eapply rt_trans. apply IHHe.
    auto using rt_step, step_ret.
  Case "eval_match".
    eapply rt_trans. apply rt_step. eapply step_match; eauto.
    eapply rt_trans. apply IHHe.
    auto using rt_step, step_ret.
  Case "eval_bracket".
    eapply rt_trans. apply rt_step. eapply step_bracket_start; eauto.
    eapply rt_trans. apply IHHe.
    apply  rt_step. eapply step_bracket_end; eauto.
Qed.

Reserved Notation "r |= cfg , pc1 ==> a , pc2" (at level 80).
Inductive evalCfg : Env -> Cfg -> Lab -> Atom -> Lab -> Prop :=
| evalCfgT : forall r pc r' pc' k t a a' pc'' pc''',
    r' |- t, pc' ==> a, pc'' ->
    r |= << pc'', r', k, CA a >>, pc ==> a', pc''' ->
    r |= << pc', r', k, CR t >>, pc ==> a', pc'''
| evalCfgNilA : forall r pc pc' a,
    r |= << pc, r, nil, CA a >>, pc' ==> a, pc
| evalCfgLetA : forall r pc r' pc' x t k a1 a pcfinal,
    r |= << pc', (x,a1)::r', RRet r' :: k, CR t >>, pc ==> a, pcfinal ->
    r |= << pc', r', RLet x t :: k, CA a1 >>, pc ==> a, pcfinal
| evalCfgReturnA : forall r pc r' pc' r1 k a1 a pcfinal,
    r |= << pc', r1, k, CA a1 >>, pc ==> a, pcfinal ->
    r |= << pc', r', RRet r1 :: k, CA a1 >>, pc ==> a, pcfinal
| evalCfgBracketA : forall r pc r' pc' l' pc'' k b l'' a pcfinal,
    r |= << pc'', r', k, 
            CA (if flows_dec (l''\_/pc') (l'\_/pc'') then b else D eBracket,l') >>, pc ==> 
         a, pcfinal ->
    r |= << pc', r', RBrk l' pc'' :: k, CA (b,l'') >>, pc ==> a, pcfinal
(*
| evalCfgLabRA : forall r pc r' pc' t1 v1 l1 pc'' k l2 l2' a pcfinal,
    r' |- t1, pc' \_/ l2' ==> (v1 @ l1) , pc'' ->
    r |= << pc' \_/ l2', r', r_lab_l l2 l2' pc' :: k, CR t1 >>, pc ==> a, pcfinal ->
    r |= << pc', r', r_lab_r t1 :: k, CA (v_lab l2 @ l2') >>, pc ==> a, pcfinal
| evalCfgLabLA : forall r pc r' pc' v1 l1 k l2 l2' pc0 a pcfinal,
    l1 \_/ pc' <: l2 \_/ (pc0 \_/ l2') ->
    r |= << pc0 \_/ l2', r', k, CA (v1 @ l2) >>, pc ==> a, pcfinal ->
    r |= << pc', r', r_lab_l l2 l2' pc0 :: k, CA (v1 @ l1) >>, pc ==> a, pcfinal
| evalCfgCmpLA : forall r pc r' pc' k t2 a2 pc'' l1 l1' a pcfinal,
    r' |- t2, pc' ==> a2, pc'' ->
    r |= << pc', r', r_cmp_r l1 l1' :: k, CR t2 >>, pc ==> a, pcfinal ->
    r |= << pc', r', r_cmp_l t2 :: k, CA (v_lab l1 @ l1') >>, pc ==> a, pcfinal
| evalCfgCmpRA : forall r pc r' pc' k l1 l1' l2 l2' v a pcfinal,
    (  l1 <: l2  -> v = v_true) ->
    (~(l1 <: l2) -> v = v_false) ->
    r |= << pc', r', k, CA (v @ (l1' \_/ l2')) >>, pc ==> a, pcfinal ->
    r |= << pc', r', r_cmp_r l1 l1' :: k, CA (v_lab l2 @ l2') >>, pc ==> a, pcfinal
| evalCfgLabelOfA : forall r pc r' pc' k v l a pcfinal,
    r |= << pc', r', k, CA (v_lab l @ bot) >>, pc ==> a, pcfinal ->
    r |= << pc', r', r_lab_of :: k, CA (v @ l) >>, pc ==> a, pcfinal
| evalCfgJoinLA : forall r pc r' pc' k t2 a2 pc'' l1 l1' a pcfinal,
    r' |- t2, pc' ==> a2, pc'' ->
    r |= << pc', r', r_join_r l1 l1' :: k, CR t2 >>, pc ==> a, pcfinal ->
    r |= << pc', r', r_join_l t2 :: k, CA (v_lab l1 @ l1') >>, pc ==> a, pcfinal
| evalCfgJoinRA : forall r pc r' pc' k l1 l1' l2 l2' a pcfinal,
    r |= << pc', r', k, CA ((v_lab (l1 \_/ l2)) @ (l1' \_/ l2')) >>, pc ==> a, pcfinal ->
    r |= << pc', r', r_join_r l1 l1' :: k, CA (v_lab l2 @ l2') >>, pc ==> a, pcfinal *)
where "r |= cfg , pc1 ==> a , pc2" := (evalCfg r cfg pc1 a pc2).
Hint Constructors evalCfg.

(** [evalCfg] is preserved by stepping back. *)
Lemma evalCfg_anti_step : forall r pc pc' a conf conf',
  r |= conf', pc ==> a, pc' ->
  conf --> conf' ->
  r |= conf, pc ==> a, pc'.
Proof.
intros r pc pc' a conf conf' HevalCfg Hstep.
step_cases (invsc Hstep) Case; try solve [invs HevalCfg; eauto].
Case "step_let_start". invs HevalCfg. invs H8. invs H11. invs H10. eauto.
Case "step_app". invs HevalCfg. invs H10. eauto.
Case "step_app_error". eapply evalCfgT; eauto. auto using eval_app_no_abs.
Case "step_inx". eapply evalCfgT; eauto. auto using eval_inx.
Case "step_match". invs HevalCfg. invs H9. eauto.
Case "step_match_error". eapply evalCfgT; eauto. auto using eval_match_no_sum.
Case "step_tag". eapply evalCfgT; eauto. auto using eval_tag.
Case "step_bop". eapply evalCfgT; eauto. auto using eval_bop.
Case "step_bracket_start". invs HevalCfg. invs H9. eapply evalCfgT; eauto.
  auto using eval_bracket.
Case "step_bracket_start_error". eapply evalCfgT; eauto. auto using eval_bracket_no_lab.
Case "step_labelof". eapply evalCfgT; eauto. eauto using eval_label_of.
Case "step_mknav". eapply evalCfgT; eauto. auto using eval_mk_nav.
Case "step_tosum". eapply evalCfgT; eauto. auto using step_tosum.
Qed.

(** Generalization of the previous lemma to an arbitrary
    number of steps. *)
Lemma evalCfg_anti_step_star : forall r pc pc' a conf conf',
  r |= conf', pc ==> a, pc' ->
  conf -->* conf' ->
  r |= conf, pc ==> a, pc'.
Proof.
intros r pc pc' a conf conf' HevalCfg Hstep.
induction Hstep; eauto using evalCfg_anti_step.
Qed.

(** The second part of adequacy. *)
Lemma small_to_big : forall r pc r' pc' t a,
  << pc, r, nil, CR t >> -->* << pc', r', nil, CA a >> ->
  r |- t, pc ==> a, pc' /\ r' = r.
Proof.
intros r pc r' pc' t a Hstep.
assert (r' |= << pc, r, nil, CR t >>, pc ==> a, pc').
 eapply evalCfg_anti_step_star; eauto.
invs H. invs H9. auto.
Qed.

(** Finally, we prove adequacy. *)
Theorem adequacy: forall r pc pc' t a,
  r |- t, pc ==> a, pc' <-> << pc, r, nil, CR t >> -->* << pc', r, nil, CA a >>.
Proof.
intros r pc pc' t a. split; intro H.
auto using big_to_small.
apply small_to_big in H as [Heval _]. assumption.
Qed.
