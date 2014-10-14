
Require Import Terms.

Definition tForce (tsum : Tm) : Tm :=
  let x := 0 in
  tMatch tsum
    x (TVar x)
      (TThrow x).

Definition tForceTag (b : BOp) (t : Tm) : Tm :=
  let x := fresh (fv_tm t) in
  TLet x (tForce t)
    (match b with
     | BEq =>
       tIf (tEq (TTag x) (tCTag TagFun))
         (tThrow (tCExcp eType))
         (tIf (tEq (TTag x) (tCTag TagSum))
           (tThrow (tCExcp eType))
           (TVar x))
     | _ =>
       tIf (tEq (TTag x) (tCTag TagLab))
         (TVar x)
         (tThrow (tCExcp eType))
    end).

Fixpoint encode (t : Tm) : Tm :=
  match t with
  | TVar x => TVar x
  | TConst k => tInl (TConst k)
  | TLet x t1 t2 => TLet x (encode t1) (encode t2)
  | TAbs x t => tInl (TAbs x (encode t))
  | TApp x y =>
      (* not sure if it's possible to do this without type tags
         - there are 2 more uses of tHasTag below though *)
      let x' := fresh [x, y] in
      tSBind (TVar x) x'
        (tHasTag TagFun (TVar x')
          (TApp x' y))
  | TInx d x => tInl (TInx d x)
  | TMatch x x1 t1 t2 =>
      let x' := fresh (x :: x1 :: fv_tm t1 ++ fv_tm t2) in
      tSBind (TVar x) x'
        (tHasTag TagSum (TVar x')
          (TMatch x' x1 (encode t1) (encode t2)))
  | TTag x =>
      tBracket (TLabelOf x) (tTag (tForce (TVar x)))
  | TBOp BJoin x y =>
      tBracket (tJoin (TLabelOf x) (TLabelOf y))
        (tBOp BJoin (tForceTag BJoin (TVar x))
                    (tForceTag BJoin (TVar y)))
  (* additional massaging for BEq and BCmp
     since they return booleans encoded as sums *)
  | TBOp b x y =>
      let z := 0 in
      tBracket (tJoin (TLabelOf x) (TLabelOf y))
        (* playing the same trick as for toSum *)
        (tMatch (tBOp b (tForceTag b (TVar x))
                        (tForceTag b (TVar y)))
          z (tInl (TInx DLeft z))
            (tInr (TInx DLeft z)))
  | TBracket x t =>
      let x' := fresh (x :: fv_tm t) in
      tSBind (TVar x) x'
        (tHasTag TagLab (TVar x')
          (TBracket x' (tForce (encode t))))
  | TLabelOf x => tInl (TLabelOf x)
  | TGetPc => tInl TGetPc
  | TMkNav x =>
      tBracket (TLabelOf x)
        (tThrow (tForce (TVar x)))
  | TToSum x =>
      let y := 0 in
      (tBracket (TLabelOf x)
        (TMatch x
          y (tInl (TInx DLeft y))
            (tInr (TInx DLeft y))))
  | TThrow _ => tCUnit (* not part of LambdaNav *)
  | TCatch _ _ _ => tCUnit (* not part of LambdaNav *)
  end.

Require LNaVSyntax.
Require LNaVBigStep.
Require LBracketSyntax.
Require LThrowBigStep.

(* TODO: extract this and use it for quickchecking *)
Fixpoint InLN (t : Tm) : Prop :=
  match t with
  | (TThrow _) => False
  | (TCatch _ _ _) => False
  | (TLet _ t1 t2) => InLN t1 /\ InLN t2
  | (TAbs _ t) => InLN t
  | (TMatch _ _ t1 t2) => InLN t1 /\ InLN t2
  | (TBracket _ t) => InLN t
  | _ => True
  end.

(* defining this as an inductive relation
   (there seems to be no easy way around that) *)
Inductive eq_varLB_mr : list (Var * Var) -> LBracketSyntax.Env ->
  LBracketSyntax.Env -> Var -> Var -> Prop :=
  | EqX1 : forall m r1 r2 x1 x2,
    get m x1 = Some x2 ->
    eq_varLB_mr m r1 r2 x1 x2
  | EqX2 : forall m r1 r2 x1 x2 a1 a2,
    get m x1 = None ->
    get r1 x1 = Some a1 ->
    get r2 x2 = Some a2 ->
    eq_atomLB_mr [] a1 a2 ->
    eq_varLB_mr m r1 r2 x1 x2
with eq_tmLB_mr : list (Var * Var) -> LBracketSyntax.Env ->
  LBracketSyntax.Env -> Tm -> Tm -> Prop :=
  | EqTVar : forall m r1 r2 x1 x2,
    eq_varLB_mr m r1 r2 x1 x2 ->
    eq_tmLB_mr m r1 r2 (TVar x1) (TVar x2)
  | EqTConst : forall m r1 r2 c,
    eq_tmLB_mr m r1 r2 (TConst c) (TConst c)
  | EqTLet : forall m r1 r2 x1 t1' t1'' x2 t2' t2'',
    eq_tmLB_mr m r1 r2 t1' t2' ->
    eq_tmLB_mr ((x1,x2)::m) r1 r2 t1'' t2'' ->
    eq_tmLB_mr m r1 r2 (TLet x1 t1' t1'') (TLet x2 t2' t2'')
  | EqTAbs : forall m r1 r2 x1 t1' x2 t2',
    eq_tmLB_mr ((x1,x2)::m) r1 r2 t1' t2' ->
    eq_tmLB_mr m r1 r2 (TAbs x1 t1') (TAbs x2 t2')
  | EqTApp : forall m r1 r2 x1 x1' x2 x2',
    eq_varLB_mr m r1 r2 x1 x2 ->
    eq_varLB_mr m r1 r2 x1' x2' ->
    eq_tmLB_mr m r1 r2 (TApp x1 x1') (TApp x2 x2')
  | EqTInx : forall m r1 r2 d x1 x2,
    eq_varLB_mr m r1 r2 x1 x2 ->
    eq_tmLB_mr m r1 r2 (TInx d x1) (TInx d x2)
  | EqTMatch : forall m r1 r2 x1 x1' t1' t1'' x2 x2' t2' t2'',
    eq_varLB_mr m r1 r2 x1 x2 ->
    eq_tmLB_mr ((x1',x2')::m) r1 r2 t1' t2' ->
    eq_tmLB_mr ((x1',x2')::m) r1 r2 t1'' t2'' ->
    eq_tmLB_mr m r1 r2 (TMatch x1 x1' t1' t1'') (TMatch x2 x2' t2' t2'')
  | EqTTag : forall m r1 r2 x1 x2,
    eq_varLB_mr m r1 r2 x1 x2 ->
    eq_tmLB_mr m r1 r2 (TTag x1) (TTag x2)
  | EqTBOp : forall m r1 r2 bo x1 x1' x2 x2',
    eq_varLB_mr m r1 r2 x1 x2 ->
    eq_varLB_mr m r1 r2 x1' x2' ->
    eq_tmLB_mr m r1 r2 (TBOp bo x1 x1') (TBOp bo x2 x2')
  | EqTBracket : forall m r1 r2 x1 t1' x2 t2',
    eq_varLB_mr m r1 r2 x1 x2 ->
    eq_tmLB_mr m r1 r2 t1' t2' ->
    eq_tmLB_mr m r1 r2 (TBracket x1 t1') (TBracket x2 t2')
  | EqTLabelOf : forall m r1 r2 x1 x2,
    eq_varLB_mr m r1 r2 x1 x2 ->
    eq_tmLB_mr m r1 r2 (TLabelOf x1) (TLabelOf x2)
  | EqTGetPc : forall m r1 r2,
    eq_tmLB_mr m r1 r2 TGetPc TGetPc
  | EqTMkNav : forall m r1 r2 x1 x2,
    eq_varLB_mr m r1 r2 x1 x2 ->
    eq_tmLB_mr m r1 r2 (TMkNav x1) (TMkNav x2)
  | EqTToSum : forall m r1 r2 x1 x2,
    eq_varLB_mr m r1 r2 x1 x2 ->
    eq_tmLB_mr m r1 r2 (TToSum x1) (TToSum x2)
  | EqTThrow : forall m r1 r2 x1  x2,
    eq_varLB_mr m r1 r2 x1 x2 ->
    eq_tmLB_mr m r1 r2 (TThrow x1) (TThrow x2)
  | EqTCatch : forall m r1 r2 t1' x1 t1'' t2' x2 t2'',
    eq_tmLB_mr m r1 r2 t1' t2' ->
    eq_tmLB_mr ((x1,x2)::m) r1 r2 t1'' t2'' ->
    eq_tmLB_mr m r1 r2 (TCatch t1' x1 t1'') (TCatch t2' x2 t2'')
with eq_atomLB_mr : list (Var * Var) ->
    LBracketSyntax.Atom -> LBracketSyntax.Atom -> Prop :=
  | EqAtom : forall m l v1 v2,
    eq_valLB_mr m v1 v2 ->
    eq_atomLB_mr m (v1,l) (v2,l)
with eq_valLB_mr  : list (Var * Var) -> 
    LBracketSyntax.Val -> LBracketSyntax.Val -> Prop :=
  | EqVConst : forall m c,
    eq_valLB_mr m (LBracketSyntax.VConst c) (LBracketSyntax.VConst c)
  | EqVInx : forall m d a1 a2,
    eq_atomLB_mr m a1 a2 ->
    eq_valLB_mr m (LBracketSyntax.VInx d a1) (LBracketSyntax.VInx d a2)
  | EqVClos : forall m r1 x1 t1 r2 x2 t2,
    eq_tmLB_mr ((x1, x2)::m) r1 r2 t1 t2 ->
    eq_valLB_mr m (LBracketSyntax.VClos r1 x1 t1)
                  (LBracketSyntax.VClos r2 x2 t2).

Hint Constructors eq_valLB_mr eq_atomLB_mr eq_tmLB_mr.

Inductive eqEnvLB : list (Var * Var) -> LBracketSyntax.Env -> LBracketSyntax.Env -> Prop :=
  | EqNil : forall m,
    eqEnvLB m [] []
  | EqCons : forall m x1 a1 r1 x2 a2 r2,
    eq_atomLB_mr m a1 a2 ->
    eqEnvLB m r1 r2 ->
    eqEnvLB m ((x1,a1) :: r1) ((x2,a2) :: r2).

(* TODO: extract this and make sure it works *)
Definition Pval' (v : LNaVSyntax.Val) := LBracketSyntax.Val.
Definition Pbox' (b : LNaVSyntax.Box) := LBracketSyntax.Val.
Definition Patom' (a : LNaVSyntax.Atom) := LBracketSyntax.Atom.
Definition Penv' (r : LNaVSyntax.Env) := LBracketSyntax.Env.
Definition H_v_const' (c : Const) : LBracketSyntax.Val :=
  LBracketSyntax.vInl (LBracketSyntax.VConst c, bot).
Definition H_v_inx (d : Dir) (_aLN : LNaVSyntax.Atom)
    (HaLN : LBracketSyntax.Atom) : LBracketSyntax.Val :=
  LBracketSyntax.vInl (LBracketSyntax.VInx d HaLN, bot).
Definition H_v_clos (_r : LNaVSyntax.Env) (x : Var) (t : Tm)
    (Hr : LBracketSyntax.Env) : LBracketSyntax.Val :=
  LBracketSyntax.vInl (LBracketSyntax.VClos Hr x (encode t) , bot).
Definition H_b_val (v : LNaVSyntax.Val)
    (Hv : LBracketSyntax.Val) : LBracketSyntax.Val := Hv.
Definition H_b_nav (e : Excp) : LBracketSyntax.Val :=
  LBracketSyntax.vInr (LBracketSyntax.vExcp e, bot).
Definition H_atom (b : LNaVSyntax.Box) (l : Lab)
    (Hb : LBracketSyntax.Val) : LBracketSyntax.Atom := (Hb, l).
Definition H_nil : LBracketSyntax.Env := [].
Definition H_cons (x : Var) (_a : LNaVSyntax.Atom) (_r : LNaVSyntax.Env)
    (Ha : LBracketSyntax.Atom) (Hr : LBracketSyntax.Env)
    : LBracketSyntax.Env := (x,Ha) :: Hr.

Definition atomEN2T : LNaVSyntax.Atom -> LBracketSyntax.Atom :=
  LNaVSyntax.atom_rect Pval' Pbox' Patom' Penv'
    H_v_const' H_v_inx H_v_clos H_b_val H_b_nav H_atom H_nil H_cons.

Definition valEN2T : LNaVSyntax.Val -> LBracketSyntax.Val :=
  LNaVSyntax.val_rect Pval' Pbox' Patom' Penv'
    H_v_const' H_v_inx H_v_clos H_b_val H_b_nav H_atom H_nil H_cons.

Definition envEN2T : LNaVSyntax.Env -> LBracketSyntax.Env :=
  LNaVSyntax.env_rect Pval' Pbox' Patom' Penv'
    H_v_const' H_v_inx H_v_clos H_b_val H_b_nav H_atom H_nil H_cons.

Lemma maps_envEN2T : forall rLN v aLN rLT,
  maps rLN v aLN ->
  eqEnvLB [] (envEN2T rLN) rLT ->
  exists aLT, maps rLT v aLT /\ 
    eq_atomLB_mr [] (atomEN2T aLN) aLT.
Admitted. (* TODO: prove this *)

Lemma eq_tmLB_mr_refl : forall m r1 r2 t,
  eq_tmLB_mr m r1 r2 t t.
Admitted. (* TODO: prove this *)

Lemma maps_eqEnvLB : forall rLN rLT a x,
  eqEnvLB [] (envEN2T rLN) rLT ->
  maps rLN x a ->
  maps rLT x (atomEN2T a).
Admitted. (* TODO: prove this *)

Lemma maps_cons : forall X (x : Var) (a : X) r,
  maps ((x, a) :: r) x a.
Proof. intros. unfold maps. simpl. rewrite <- beq_nat_refl. reflexivity. Qed.

(* Because we are using the big-step semantics this only talks about
   successful runs (non-termination ignored) *)
Theorem prop_EN2T_correct : forall tLN rLN pc aLN pc' rLT,
  InLN tLN ->
  LNaVBigStep.eval rLN tLN pc aLN pc' ->
  eqEnvLB [] (envEN2T rLN) rLT ->
  exists aLT,
  LThrowBigStep.eval rLT (encode tLN) pc (LThrowBigStep.Suc aLT) pc'
  /\ eq_atomLB_mr [] (atomEN2T aLN) aLT.
Proof.
  intro tLN.
  (Tm_cases (induction tLN) Case);
    intros rLN pc aLN pc' rLT HInLN Heval Henv.
  Case "TVar". simpl. invsc Heval. eapply maps_envEN2T in H1.
    destruct H1 as [aLT [G1 G2]]. eauto. trivial.
  Case "TConst". simpl.
    exists (LBracketSyntax.vInl (LBracketSyntax.VConst c, bot), bot).
    invsc Heval. split.
    SCase "Left conjunct".
      unfold tInl. eapply LThrowBigStep.eval_let. eauto.
      apply LThrowBigStep.eval_inx. unfold maps. simpl. reflexivity.
    SCase "Right conjunct". 
     repeat constructor.
  Case "TLet". invsc Heval. simpl in HInLN.
    eapply IHtLN1 in H6; [| intuition | eauto].
      destruct H6 as [aLT [IH11 IH12]].
    eapply IHtLN2 in H7; [| intuition | ].
      destruct H7 as [aLT' [IH21 IH22]]. clear IHtLN1 IHtLN2.
    exists aLT'. split.
    SCase "Left conjunct". simpl.
      eapply LThrowBigStep.eval_let; eassumption.
    SCase "Right conjunct". assumption.
    SCase "leftover".
      assert(envEN2T ((v, a) :: rLN) = (v, atomEN2T a) :: envEN2T rLN) as G
        by reflexivity. rewrite G.
      apply EqCons. assumption. assumption.
  Case "TAbs". invsc Heval. clear IHtLN.
    exists (LBracketSyntax.vInl
      (LBracketSyntax.VClos rLT v (encode tLN), bot), bot).
    split. simpl. repeat econstructor.
    unfold LBracketSyntax.vInl.
    assert (atomEN2T (LNaVSyntax.V (LNaVSyntax.VClos rLN v tLN), bot) =
      (valEN2T (LNaVSyntax.VClos rLN v tLN), bot)) as G by reflexivity.
    rewrite G. constructor.
    assert (valEN2T (LNaVSyntax.VClos rLN v tLN) =
      (LBracketSyntax.vInl (LBracketSyntax.VClos
        (envEN2T rLN) v (encode tLN), bot))) as G' by admit. (* XXX *)
    rewrite G'. constructor. constructor. constructor.
    apply eq_tmLB_mr_refl.
  Case "TApp". invsc Heval.
    SCase "eval_app". admit.
    (*eexists. split.
      SSCase "Left conjunct". simpl. unfold tSBind. unfold tMatch.
        apply LThrowBigStep.eval_let with
          (a := atomEN2T (LNaVSyntax.V (LNaVSyntax.VClos r' x t), l))
          (pc' := pc).
        constructor. eapply maps_eqEnvLB; eassumption.
        econstructor. apply maps_cons. simpl. unfold tHasTag.
        econstructor. econstructor. repeat econstructor.
      SSCase "Right conjunct".
*)
    SCase "eval_app_no_abs". admit.
  Case "TInx". admit.
  Case "TMatch". admit.
  Case "TTag". admit.
  Case "TBOp". admit.
  Case "TBracket". admit.
  Case "TLabelOf". admit.
  Case "TGetPc". invsc Heval. eexists. split.
    SCase "Left conjunct". simpl. econstructor. eauto.
      econstructor. unfold maps. simpl. reflexivity.
    SCase "Right conjunct". repeat constructor.
  Case "TMkNav". admit.
  Case "TToSum". admit.
  Case "TThrow". inversion HInLN.
  Case "TCatch". inversion HInLN.
Admitted.
