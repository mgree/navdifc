
Require Import Terms.
Require Import LNaVSyntax.

(** * Big-Step Semantics for LambdaNaV *)

(** Helper functions that help us reduce the number of rules in the
    big-step semantics. This is important since the number of subcases
    in our non-interference proof is quadratic in the number of
    overlapping rules (i.e. not fully syntax-directed). *)

Definition propagate_nav (b : Box) : Excp :=
  match b with
  | V _ => eType
  | D e => e
  end.

Definition bop_lb_box f (b' b'' : Box) : Box :=
  match b', b'' with
  | (V (VConst (CLab l'))), (V (VConst (CLab l''))) => f l' l''
  | V (VConst (CLab l')), V _ => D eType
  | V (VConst (CLab l')), D e => D e
  | V _, _ => D eType
  | D e, _ => D e
  end.

Definition eq_box (b' b'' : Box) : Box :=
  match b', b'' with
  | (V (VConst c')), (V (VConst c'')) =>
    if beq_const c' c'' then V vTrue else V vFalse
  | V (VConst v'), V _ => D eType
  | V (VConst v'), D e => D e
  | V _, _ => D eType
  | D e, _ => D e
  end.

Definition bop_box bo :=
  match bo with
  | BEq => eq_box
  | BCmp => bop_lb_box (fun l' l'' => if flows_dec l' l'' then V vTrue else V vFalse)
  | BJoin => bop_lb_box (fun l' l'' => V (VConst (CLab (join l' l''))))
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

Definition tag_box (b : Box) : Box :=
  match b with
  | V v => V (VConst (CTag (tag_of v)))
  | D e => D e
  end.

(** The evaluation judgment. *)

Reserved Notation "r |- t , pc1 ==> a , pc2" (at level 80).
Inductive eval : Env -> Tm -> Lab -> Atom -> Lab -> Prop :=
  | eval_var : forall r x a pc,
      maps r x a ->
      r |- (TVar x), pc ==> a, pc
  | eval_const : forall r c pc,
      r |- (TConst c), pc ==> (V (VConst c), bot), pc
  | eval_let : forall r x t t' pc pc' pc'' a a',
      r |- t, pc ==> a, pc' ->
      (x,a)::r |- t', pc' ==> a', pc'' ->
      r |- TLet x t t', pc ==> a', pc''
  | eval_abs : forall r x t pc,
      r |- (TAbs x t), pc ==> (V (VClos r x t), bot), pc
  | eval_app : forall r x' x'' pc a' pc' x t a l r',
      maps r x' (V (VClos r' x t), l) ->
      maps r x'' a ->
      (x,a)::r' |- t, (pc \_/ l) ==> a', pc' ->
      r |- TApp x' x'', pc ==> a', pc'
  (* optimized version (mixes 2 rules in 1) *)
  | eval_app_no_abs : forall r x' x'' pc b l,
      maps r x' (b, l) ->
      ~(is_box is_abs b) ->
      r |- TApp x' x'', pc ==> (D (propagate_nav b), bot), (pc \_/ l)
  | eval_inx : forall r d x pc a,
      maps r x a ->
      r |- TInx d x, pc ==> (V (VInx d a),bot), pc
  | eval_match : forall r x x' t' t'' a' pc pc' a l d,
      maps r x (V (VInx d a),l) ->
      (x',a)::r |- d_choose d t' t'', pc\_/l ==> a', pc' ->
      r |- TMatch x x' t' t'', pc ==> a', pc'
  | eval_match_no_sum : forall r x x' t' t'' pc l b,
      maps r x (b,l) ->
      ~(is_box is_sum b) ->
      r |- TMatch x x' t' t'', pc ==> (D (propagate_nav b), bot), (pc\_/l)
  | eval_tag : forall r x pc b l,
      maps r x (b, l) ->
      r |- TTag x, pc ==> (tag_box b, l), pc
  (* optimized version (mixes 3 x 5 rules in 1) *)
  | eval_bop : forall r bo x' x'' pc b' b'' l' l'',
      maps r x' (b', l') ->
      maps r x'' (b'', l'') ->
      r |- (TBOp bo x' x''), pc ==> (bop_box bo b' b'', l' \_/ l''), pc
  (* optimized version (mixes 2 rules in 1) *)
  | eval_bracket : forall r x t pc pc' b l l' l'',
      maps r x (V (VConst (CLab l)), l') ->
      r |- t, (pc\_/l') ==> (b, l''), pc' ->
      r |- TBracket x t, pc ==> (if flows_dec (l'' \_/ pc') (l \_/ (pc\_/l')) then b else D eBracket, l), (pc\_/l')
  (* optimized version (mixes 2 rules in 1) *)
  | eval_bracket_no_lab : forall r x t pc b l',
      maps r x (b, l') ->
      ~(is_box is_lab b) ->
      r |- TBracket x t, pc ==> (D (propagate_nav b),bot), (pc\_/l')
  | eval_label_of : forall r x b l pc,
      maps r x (b, l) ->
      r |- (TLabelOf x), pc ==> (V (VConst (CLab l)), bot), pc
  | eval_get_pc : forall r pc,
      r |- TGetPc, pc ==> (V (VConst (CLab pc)), bot), pc
  (* optimized version (mixes 3 rules in 1) *)
  | eval_mk_nav : forall r x pc b l,
      maps r x (b, l) ->
      r |- TMkNav x, pc ==> (mk_nav_box b, l), pc
  (* optimized version (mixes 2 rules in 1) *)
  | eval_to_sum : forall r x pc b l,
      maps r x (b,l) ->
      r |- TToSum x, pc ==> (to_sum_box b, l), pc
where "r |- t , pc1 ==> a , pc2" := (eval r t pc1 a pc2).

Hint Constructors eval.

Tactic Notation "eval_cases" tactic(first) ident(c) :=
  first; [
  (* perl -ne 'print "    Case_aux c \"$1\" |\n" if /\| (eval_\w+)\s/' < LNaVBigStep.v *)
    Case_aux c "eval_var" |
    Case_aux c "eval_const" |
    Case_aux c "eval_let" |
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
    Case_aux c "eval_mk_nav" |
    Case_aux c "eval_to_sum"
  ].
