Require Import Terms.
Require Import LNaVSyntax.
Require Import LNaVBigStep. (* reusing helpers *)

(** * Continuations and partial configurations *)

Inductive Frame : Type :=
| RLet : Var -> Tm -> Frame
| RRet : Env -> Frame
| RBrk : Lab -> Lab -> Frame. (* final label + original pc *)

Definition Cont := list Frame.

Definition PCfg := prod (prod Lab Env) Cont.

Inductive RCfg : Type :=
| CR : Tm -> RCfg    (* term to be reduced *)
| CA : Atom -> RCfg.  (* return atom *)

Definition Cfg := prod PCfg RCfg.

Notation "v @ L" := (v,L) (at level 5).

Notation "<< pc , r , k , X >>" := (((pc, r), k), X) (at level 5).

(** * Small-step semantics defined as a total(!) function *)

Definition step (c : Cfg) : Cfg :=
  match c with
  (* s_var *)
  | << pc, rho, k, CR (TVar x) >> =>
    match get rho x with
    | Some a =>
      << pc, rho, k, CA a >>
    | None =>
      << pc, rho, k, CA (D eUnbound)@bot >>
    end
  (* s_const *)
  | << pc, rho, k, CR (TConst c) >> =>
    << pc, rho, k, CA (V (VConst c))@bot>>
  (* s_let_start *)
  | << pc, rho, k, CR (TLet x t1 t2) >> =>
    << pc, rho, RLet x t2 :: k, CR t1 >>
  (* s_let_bind *)
  | << pc, rho, RLet x t :: k, CA a >> =>
    << pc, (x,a) :: rho, RRet rho :: k, CR t >>
  (* s_abs *)
  | << pc, rho, k, CR (TAbs x t) >> =>
    << pc, rho, k, CA (V (VClos rho x t))@bot >>
  (* s_app *)
  | << pc, rho, k, CR (TApp x1 x2) >> =>
    match get rho x1, get rho x2 with
    | Some ((V (VClos rho' x t))@L), Some a =>
      << pc\_/L, (x,a) :: rho', RRet rho :: k, CR t >>
    | Some (b,L),_ =>
      << pc\_/L, rho, k, CA (D (propagate_nav b))@bot >>
    | _, _ => 
      << pc, rho, k, CA (D eUnbound)@bot >>
    end
  (* s_return *)
  | << pc, rho, RRet rho' :: k, CA a >> =>
    << pc, rho', k, CA a >>
  (* s_inx *)
  | << pc, rho, k, CR (TInx d x) >> =>
    match get rho x with
    | Some a =>
      << pc, rho, k, CA (V (VInx d a))@bot >>
    | _ =>
      << pc, rho, k, CA (D eUnbound)@bot >>
    end
  (* s_match *)
  | << pc, rho, k, CR (TMatch x x' t1 t2) >> =>
    match get rho x with
    | Some (V (VInx DLeft a), l) =>
      << pc\_/l, (x',a) :: rho, RRet rho :: k, CR t1 >>
    | Some (V (VInx DRight a), l) =>
      << pc\_/l, (x',a) :: rho, RRet rho :: k, CR t2 >>
    | Some (V _, l) =>
      << pc\_/l, rho, k, CA (D eType)@bot >>
    | Some (D e, l) =>
      << pc\_/l, rho, k, CA (D e)@bot >>
    | _ =>
      << pc, rho, k, CA (D eUnbound)@bot >>
    end
  (* s_tag *)
  | << pc, rho, k, CR (TTag x) >> =>
    match get rho x with
    | Some (b,l) =>
      << pc, rho, k, CA (tag_box b)@l >>
    | _ =>
      << pc, rho, k, CA (D (eUnbound))@bot >>
    end
  (* s_bop *)
  | << pc, rho, k, CR (TBOp bo x' x'') >> =>
    match get rho x', get rho x'' with
    | Some (b', l0'), Some (b'', l0'') =>
      << pc, rho, k, CA (bop_box bo b' b'', l0' \_/ l0'') >>
    | _, _ =>
      << pc, rho, k, CA (D (eUnbound))@bot >>
    end
  (* s_bracket_start *)
  | << pc, rho, k, CR (TBracket x t) >> =>
    match get rho x with
    | Some ((V (VConst (CLab L)))@L') =>
      << pc\_/L', rho, RBrk L (pc\_/L') :: k, CR t >>
    | Some (b,L') => 
      << pc\_/L', rho, k, CA (D (propagate_nav b))@bot >>
    | None =>
      << pc, rho, k, CA (D (eUnbound))@bot >>
    end
  (* s_bracket_end *)
  | << pc, rho, RBrk L' pc' :: k, CA (b@L) >> =>
    if flows_dec (L \_/ pc) (L' \_/ pc') then
      << pc', rho, k, CA (b@L')>>
    else
      << pc', rho, k, CA ((D eBracket)@L')>>
  (* s_label_of *)
  | << pc, rho, k, CR (TLabelOf x) >> =>
    match get rho x with
    | Some (_,l) =>
      << pc, rho, k, CA (V (VConst (CLab l)))@bot >>
    | _ =>
      << pc, rho, k, CA (D (eUnbound))@bot >>
    end
  (* s_get_pc *)
  | << pc, rho, k, CR TGetPc >> =>
    << pc, rho, k, CA (V (VConst (CLab pc)))@bot >>
  (* s_mk_nav *)
  | << pc, rho, k, CR (TMkNav x) >> =>
    match get rho x with
    | Some (b,l) =>
      << pc, rho, k, CA (mk_nav_box b)@l >>
    | _ =>
      << pc, rho, k, CA (D (eUnbound))@bot >>
    end
  (* s_to_sum *)
  | << pc, rho, k, CR (TToSum x) >> =>
    match get rho x with
    | Some (b,l) =>
      << pc, rho, k, CA (to_sum_box b)@l >>
    | _ =>
      << pc, rho, k, CA (D (eUnbound))@bot >>
    end
  (* stack underflow (you're already done?) *)
  | << pc, rho, nil, CA _ >> =>
      << pc, rho, nil, CA (D (eStack))@bot >>
  (* terms not from this language *)
  | << pc, rho, k, CR (TThrow _) >> =>
      << pc, rho, k, CA (D (eLanguage))@bot >>
  | << pc, rho, k, CR (TCatch _ _ _) >> =>
      << pc, rho, k, CA (D (eLanguage))@bot >>
  end.

Definition final (c : Cfg) : bool :=
  match c with
  | << pc, rho, nil, CA _ >> => true
  | _ => false
  end.

Fixpoint nstep (n : nat) (cm : Cfg*nat) : Cfg*nat :=
  match n with
  | S n' =>
    match cm with
    | (c,m) => if final c then (c,m) else nstep n' (step c, m+1)
    end
  | O => cm
  end.

Definition mstep (n : nat) (t : Tm) : Cfg*nat :=
  nstep n (<< bot, nil, nil, CR t >>, 0).

Definition sstep (n : nat) (t : Tm) : option ((Atom*Lab)*nat) :=
  match mstep n t with
  | (<< pc, rho, nil, CA a >>, m) => Some ((a,pc),m)
  | _ => None (* looping or need more steps *)
  end.

Definition tstep_no := 1000.

Definition tstep (t : Tm) : option Atom :=
  match sstep tstep_no t with
  | Some ((a,_pc), m) => Some a
  | None => None (* looping or need more steps *)
  end.

(* Correspondence *)
Fixpoint multistep (n : nat) (c : Cfg) : Cfg :=
  match n with
  | S n' => multistep n' (step c)
  | O => c
  end.

Lemma multistep_trans_general : forall n1 n2 cfg1 cfg2 cfg3,
  multistep n1 cfg1 = cfg2 ->
  multistep n2 cfg2 = cfg3 ->
  exists n3, multistep n3 cfg1 = cfg3.
Proof.
  intros n1.
  induction n1; intros n2 cfg1 cfg2 cfg3 Hstep1 Hstep2.
  Case "n1 = 0".
    exists n2. simpl in Hstep1. subst. reflexivity.
  Case "S n1".
    simpl in Hstep1.
    remember (step cfg1) as cfg1'.
    specialize (IHn1 n2 cfg1' cfg2 cfg3 Hstep1 Hstep2).
    destruct IHn1 as [n Hstep1'].
    exists (S n). simpl. rewrite <- Heqcfg1'. assumption.
Qed.

Ltac solve_var H k f := exists 1; simpl; rewrite H; destruct k; try destruct f; eauto.
Ltac immediate k f := exists 1; simpl; destruct k; try destruct f; eauto.
  
Definition steps cfg1 cfg2 := exists n, multistep n cfg1 = cfg2.
Hint Unfold steps.

Lemma multistep_trans : forall cfg1 cfg2 cfg3,
  steps cfg1 cfg2 ->
  steps cfg2 cfg3 ->
  steps cfg1 cfg3.
Proof.
  intros cfg1 cfg2 cfg3 Hstep1 Hstep2.
  destruct Hstep1 as [n1 Hstep1]. destruct Hstep2 as [n2 Hstep2].
  eauto using multistep_trans_general.
Qed.

Lemma big_to_small : forall r t pc a pc' k,
  r |- t, pc ==> a, pc' ->
  steps <<pc, r, k, CR t>> <<pc', r, k, CA a>>.
Proof.
  intros r t pc a pc' k Heval. generalize dependent k.
  (eval_cases (induction Heval) Case); intro k.
  Case "eval_var". solve_var H k f.
  Case "eval_const". immediate k f.
  Case "eval_let".
    assert (steps << pc, r, k, CR (TLet x t t') >> << pc, r, RLet x t' :: k, CR t >>)
      by immediate k f.
    specialize (IHHeval1 (RLet x t' :: k)).
    assert (steps << pc', r, RLet x t' :: k, CA a >> << pc', (x,a) :: r, RRet r :: k, CR t' >>)
      by immediate k f.
    specialize (IHHeval2 (RRet r :: k)).
    assert (steps << pc'', x @ a :: r, RRet r :: k, CA a' >> << pc'', r, k, CA a' >>)
      by immediate k f.
    eauto using multistep_trans.
  Case "eval_abs". immediate k f.
  Case "eval_app".
    assert (steps << pc, r, k, CR (TApp x' x'') >> << pc\_/l, x@a::r', RRet r::k, CR t >>).
      exists 1; simpl; unfold Atom; rewrite H, H0; destruct k; try destruct f; eauto.
    specialize (IHHeval (RRet r :: k)).
    assert (steps <<pc', x@a::r', RRet r :: k, CA a'>> << pc', r, k, CA a'>>)
      by immediate k f.
    eauto using multistep_trans.
  Case "eval_app_no_abs".
    exists 1. simpl. unfold Atom. rewrite H. destruct b; try destruct v; destruct k; try destruct f; 
      try solve [simpl in H0; exfalso; auto]; auto.
  Case "eval_inx".
    solve_var H k f.
  Case "eval_match".
    assert (steps << pc, r, k, CR (TMatch x x' t' t'') >> 
                  << pc\_/l, x'@a::r, RRet r::k, CR (d_choose d t' t'') >>).
      fold Atom in H. destruct d; solve_var H k f.
    specialize (IHHeval (RRet r::k)).
    assert (steps << pc', x'@a::r, RRet r::k, CA a' >> << pc', r, k, CA a' >>).
      immediate k f.
    eauto using multistep_trans. 
  Case "eval_match_no_sum".
    exists 1. simpl. unfold Atom. rewrite H. destruct b; try destruct v; destruct k; try destruct f; 
      try solve [simpl in H0; exfalso; auto]; auto.
  Case "eval_tag".
    fold Atom in H. solve_var H k f.
  Case "eval_bop".
    fold Atom in H, H0. 
    exists 1; simpl; rewrite H, H0; destruct k; try destruct f; eauto.
  Case "eval_bracket".
    remember (flows_dec (l'' \_/ pc') (l \_/ (pc \_/ l'))) as flow.
    assert (steps << pc, r, k, CR (TBracket x t) >> << pc\_/l',r,RBrk l (pc\_/l')::k,CR t>>).
      fold Atom in H. solve_var H k f.
    specialize (IHHeval (RBrk l (pc\_/l') ::k)).
    assert (steps << pc', r, RBrk l (pc \_/ l') :: k, CA b @ l'' >>
                  << pc \_/ l', r, k, CA (if flow then b else D eBracket) @l >>).
      destruct flow; immediate k f; rewrite <- Heqflow; eauto.
    eauto using multistep_trans.
  Case "eval_bracket_no_lab".
    exists 1. simpl. unfold Atom. rewrite H. destruct b; try destruct v; try destruct c; 
      destruct k; try destruct f; try solve [simpl in H0; exfalso; auto]; auto.
  Case "eval_label_of".   
    fold Atom in H. solve_var H k f.
  Case "eval_get_pc".
    immediate k f.
  Case "eval_mk_nav".
    fold Atom in H. solve_var H k f.
  Case "eval_to_sum".
    fold Atom in H. solve_var H k f.
Qed.

(* MMG: to here.  Started running into some problems lining everything
   up, since this development is actually rather different from the
   old one.  I think this general approach will work, but we need to
   reconcile issues with unbound variables, get rid of stack
   underflows, and probably relation-ize the step function.  (At which
   point, we can either prove that the relation and function match, or
   just redo the previous proof for the relation...)
*)

(*
Reserved Notation "r |= cfg , pc1 ==> a , pc2" (at level 80).
Inductive evalCfg : Env -> Cfg -> Lab -> Atom -> Lab -> Prop :=
| evalCfgT : forall r pc r' pc' k (t:Tm) a a' pc'' pc''',
    r' |- t, pc' ==> a, pc'' ->
    r |= << pc'', r', k, CA a >>, pc ==> a', pc''' ->
    r |= << pc', r', k, CR t >>, pc ==> a', pc'''

| evalCfgNilA : forall r pc pc' a,
    r |= << pc, r, nil, CA a >>, pc' ==> a, pc
(*
| evalCfgLet : forall r t pc a pc' x t' k a' pc'' pc''',
    r |- t,pc' ==> a,pc'' ->
    r |= << pc'', x@a::r, RRet r::k, CR t' >>,pc ==> a',pc''' ->
    r |= << pc', r, RLet x t'::k, CR t >>,pc ==> a',pc'''
| evalCfgRet : forall r pc a pc' r' k a1,
    r |= << pc', r', k, CA a1 >>, pc ==> a, pc' ->
    r |= << pc', r, RRet r' :: k, CA a1 >>, pc ==> a, pc'
*)
where "r |= cfg , pc1 ==> a , pc2" := (evalCfg r cfg pc1 a pc2).
Hint Constructors evalCfg.

(** [evalCfg] is preserved by stepping back. *)
Lemma evalCfg_anti_step : forall r pc pc' a conf conf',
  r |= conf', pc ==> a, pc' ->
  step conf = conf' ->
  r |= conf, pc ==> a, pc'.
Proof.
intros r pc pc' a conf conf' HevalCfg Hstep.
destruct conf as [[[pc'' r'] k] [t | a']].
Tm_cases (destruct t) Case.
Case "TVar".
  remember (get r' v) as av.
  destruct av.
  simpl in Hstep.
  rewrite <- Heqav in Hstep.
  destruct k; try destruct f; subst; 
    solve [eapply evalCfgT; try apply HevalCfg; 
           apply eval_var; unfold maps; rewrite <- Heqav; auto].
  simpl in Hstep.  
  destruct k; try destruct f; rewrite <- Heqav in Hstep.
  subst. invsc HevalCfg.
  eapply evalCfgT; try apply HevalCfg.

Case "s_app_l". invs HevalCfg.
SCase "evalCfgAppL". invs H8. invs H12. invs H13. invs H19. invs H15. eauto.
Case "s_app_r". invs HevalCfg.
SCase "evalCfgAppR". invs H8. eauto.
Case "s_classify_r". invs HevalCfg.
SCase "evalCfgLabR". invs H8. invs H11. invs H12. econstructor; eauto. eauto.
Case "s_classify_l". invs HevalCfg.
SCase "evalCfgLabl". invs H8. eauto.
Case "s_lab_of_push". invs HevalCfg.
SCase "evalCfgLabOf". invs H8. econstructor; eauto. eauto.
Case "s_cmp_l". invs HevalCfg.
SCase "evalCfgCmpL". invs H8. invs H11. invs H12. econstructor; eauto. eauto.
Case "s_join_l". invs HevalCfg.
SCase "evalCfgJoinL". invs H8. invs H11. invs H12. econstructor; eauto. eauto.
Qed.

*)