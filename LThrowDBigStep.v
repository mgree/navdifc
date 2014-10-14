
Require Import Terms.
Require Import LNaVSyntax.

(** * Big-Step Semantics for LambdaThrowPlusD *)

Inductive Result : Type :=
| Suc : Atom -> Result
| Throw : Excp -> Result.

(** Helper functions that help us reduce the number of rules in the
    big-step semantics. This is important since the number of subcases
    in our non-interference proof is quadratic in the number of
    overlapping rules (i.e. not fully syntax-directed). *)

Definition propagate_d (b : Box) : Excp :=
  match b with
  | V _ => eType
  | D e => e
  end.

Definition bop_lb_res f (b' b'' : Box) : Result :=
  match b', b'' with
  | (V (VConst (CLab l'))), (V (VConst (CLab l''))) => Suc (f l' l'', bot)
  | V (VConst (CLab l')), V _ => Throw eType
  | V (VConst (CLab l')), D e => Throw e
  | V _, _ => Throw eType
  | D e, _ => Throw e
  end.

Definition eq_res (b' b'' : Box) : Result :=
  match b', b'' with
  | (V (VConst c')), (V (VConst c'')) =>
    if beq_const c' c'' then Suc (V vTrue, bot) else Suc (V vFalse, bot)
  | V (VConst v'), V _ => Throw eType
  | V (VConst v'), D e => Throw e
  | V _, _ => Throw eType
  | D e, _ => Throw e
  end.

Definition bop_res (bo : BOp) : Box -> Box -> Result :=
  match bo with
  | BEq => eq_res
  | BCmp => bop_lb_res (fun l' l'' =>
      if flows_dec l' l'' then V vTrue else V vFalse)
  | BJoin => bop_lb_res (fun l' l'' =>
      V (VConst (CLab (join l' l''))))
  end.

Definition mk_nav_box (b : Box) : Box :=
  match b with
  | V (VConst (CExcp e)) => D e
  | V _ => D eType
  | D e => D e
  end.

Definition to_sum_box (b : Box) : Box :=
  match b with
  | V v => V (vInl (V v, bot))
  | D e => V (vInr (V (VConst (CExcp e)), bot))
  end.

Definition tag_res (b : Box) : Result :=
  match b with
  | V v => Suc (V (VConst (CTag (tag_of v))), bot)
  | D e => Throw e
  end.

Definition bracket_box (res : Result) (pc_end lright : Lab) : Box :=
  match res with
  | Suc (b,l'') =>
    if flows_dec (l'' \_/ pc_end) lright then
      b (* old eval_bracket = success case *)
    else
      D eBracket (* eval_bracket_fail *)
  | Throw ex =>
    if flows_dec pc_end lright then
      D ex (* eval_bracket_low_pCExcp *)
    else
      D eBracket (* eval_bracket_high_pc_exp *)
  end.

Definition throw_excp (b : Box) : Excp :=
  match b with
  | D e => e
  | V (VConst (CExcp e)) => e
  | V _ => eType
  end.

(** The evaluation judgment. *)

Reserved Notation "r |- t , pc1 ==> res , pc2" (at level 80).
Inductive eval : Env -> Tm -> Lab -> Result -> Lab -> Prop :=
  | eval_var : forall r x a pc,
      maps r x a ->
      r |- (TVar x), pc ==> Suc a, pc
  | eval_const : forall r c pc,
      r |- (TConst c), pc ==> Suc (V (VConst c), bot), pc
  | eval_let : forall r x t t' pc a pc' res pc'',
      r |- t, pc ==> Suc a, pc' ->
      ((x,a)::r) |- t', pc' ==> res, pc'' ->
      r |- (TLet x t t'), pc ==> res, pc''
  | eval_let_fail : forall r x t t' pc pc' ex,
      r |- t, pc ==> Throw ex, pc' ->
      r |- (TLet x t t'), pc ==> Throw ex, pc'
  | eval_abs : forall r x t pc,
      r |- (TAbs x t), pc ==> Suc (V (VClos r x t), bot), pc
  | eval_app : forall r x' x'' pc res pc' x t a l r',
      maps r x' (V (VClos r' x t), l) ->
      maps r x'' a ->
      (x,a)::r' |- t, (pc \_/ l) ==> res, pc' ->
      r |- TApp x' x'', pc ==> res, pc'
  (* optimized version (mixes 2 rules in 1) *)
  | eval_app_no_abs : forall r x' x'' pc b l,
      maps r x' (b, l) ->
      ~(is_box is_abs b) ->
      r |- TApp x' x'', pc ==> Throw (propagate_d b), (pc \_/ l)
  | eval_inx : forall r d x pc a,
      maps r x a ->
      r |- TInx d x, pc ==> Suc (V (VInx d a),bot), pc
  | eval_match : forall r x x' t' t'' res pc pc' a l d,
      maps r x (V (VInx d a),l) ->
      (x',a)::r |- d_choose d t' t'', pc\_/l ==> res, pc' ->
      r |- TMatch x x' t' t'', pc ==> res, pc'
  | eval_match_no_sum : forall r x x' t' t'' pc l b,
      maps r x (b,l) ->
      ~(is_box is_sum b) ->
      r |- TMatch x x' t' t'', pc ==> Throw (propagate_d b), (pc\_/l)
  (* optimized version (mixes 2 rules in 1) *)
  (* Note: pc raises more! even compared to LThrow *)
  | eval_tag : forall r x pc b l,
      maps r x (b, l) ->
      r |- TTag x, pc ==> tag_res b, pc \_/ l
  (* optimized version (mixes 3 x 5 rules in 1) *)
  | eval_bop : forall r bo x' x'' pc b' b'' l' l'',
      maps r x' (b', l') ->
      maps r x'' (b'', l'') ->
      r |- (TBOp bo x' x''), pc ==> bop_res bo b' b'', pc \_/ l' \_/ l''
  (* optimized version (mixes 4 rules in 1) *)
  | eval_bracket : forall r x t pc pc' l l' res,
      maps r x (V (VConst (CLab l)), l') ->
      r |- t, (pc \_/ l') ==> res, pc' ->
      r |- (TBracket x t), pc ==> Suc (bracket_box res pc' (l \_/ (pc \_/ l')), l), (pc \_/ l')
  (* optimized version (mixes 2 rules in 1) *)
  | eval_bracket_no_lab : forall r x t pc b l',
      maps r x (b, l') ->
      ~(is_box is_lab b) ->
      r |- TBracket x t, pc ==> Throw (propagate_d b), (pc\_/l')
  | eval_label_of : forall r x b l pc,
      maps r x (b, l) ->
      r |- (TLabelOf x), pc ==> Suc (V (VConst (CLab l)), bot), pc
  | eval_get_pc : forall r pc,
      r |- TGetPc, pc ==> Suc (V (VConst (CLab pc)), bot), pc
(* Note: no rule for TMkNav, can use Throw + Bracket to encode it *)
  (* optimized version (mixes 2 rules in 1) *)
  | eval_to_sum : forall r x pc b l,
      maps r x (b,l) ->
      r |- TToSum x, pc ==> Suc (to_sum_box b, l), pc
  (* optimized version (mixes 2 rules in 1) *)
  | eval_throw : forall r x b l pc,
      maps r x (b, l) ->
      r |- (TThrow x), pc ==> Throw (throw_excp b), (pc \_/ l)
  | eval_catch_no_excp : forall r t x t' pc a pc',
      r |- t, pc ==> Suc a, pc' ->
      r |- (TCatch t x t'), pc ==> Suc a, pc'
  | eval_catch_excp : forall r t x t' pc ex pc' res pc'',
      r |- t, pc ==> Throw ex, pc' ->
      ((x,(V (VConst (CExcp ex)),bot)) :: r) |- t', pc' ==> res, pc'' ->
      r |- (TCatch t x t'), pc ==> res, pc''
where "r |- t , pc1 ==> a , pc2" := (eval r t pc1 a pc2).

Hint Constructors eval.

Tactic Notation "eval_cases" tactic(first) ident(c) :=
  first; [
  (* perl -ne 'print "    Case_aux c \"$1\" |\n" if /\| (eval_\w+)\s/' < LThrowPlusDBigStep.v *)
    Case_aux c "eval_var" |
    Case_aux c "eval_const" |
    Case_aux c "eval_let" |
    Case_aux c "eval_let_fail" |
    Case_aux c "eval_abs" |
    Case_aux c "eval_app" |
    Case_aux c "eval_app_no_abs" |
    Case_aux c "eval_inx" |
    Case_aux c "eval_match" |
    Case_aux c "eval_match_no_sum" |
    Case_aux c "eval_tag" |
    Case_aux c "eval_bop" |
    Case_aux c "eval_bracket" |
    Case_aux c "eval_bracket_no_lab" |
    Case_aux c "eval_label_of" |
    Case_aux c "eval_get_pc" |
    Case_aux c "eval_to_sum" |
    Case_aux c "eval_throw" |
    Case_aux c "eval_catch_no_excp" |
    Case_aux c "eval_catch_excp"
  ].
