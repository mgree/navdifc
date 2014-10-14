Require Import Terms.
Require Import LBracketSyntax.

(** * Big-Step Semantics for LambdaBracket *)

Definition do_bop b v' v'' :=
  match b, v', v'' with
  | BEq, VConst c', VConst c'' =>
    if beq_const c' c'' then vTrue else vFalse
  | BCmp, VConst (CLab l'), VConst (CLab l'') =>
    if flows_dec l' l'' then vTrue else vFalse
  | BJoin, VConst (CLab l'), VConst (CLab l'') =>
    VConst (CLab (join l' l''))
  | _, _, _ => vUnit (* shouldn't happen *)
  end.

(** The evaluation judgment. *)
Reserved Notation "r |- t , pc1 ==> a , pc2" (at level 80).
Inductive eval : Env -> Tm -> Lab -> Atom -> Lab -> Prop :=
  | eval_var : forall r x a pc,
      maps r x a ->
      r |- (TVar x), pc ==> a, pc
  | eval_const : forall r c pc,
      r |- (TConst c), pc ==> (VConst c, bot), pc
  | eval_let : forall r x t t' pc pc' pc'' a a',
      r |- t, pc ==> a, pc' ->
      (x,a)::r |- t', pc' ==> a', pc'' ->
      r |- TLet x t t', pc ==> a', pc''
  | eval_abs : forall r x t pc,
      r |- (TAbs x t), pc ==> (VClos r x t, bot), pc
  | eval_app : forall r x' x'' pc a' pc' x t a l r',
      maps r x' (VClos r' x t, l) ->
      maps r x'' a ->
      (x,a)::r' |- t, (pc \_/ l) ==> a', pc' ->
      r |- TApp x' x'', pc ==> a', pc'
  | eval_inx : forall r d x pc a,
      maps r x a ->
      r |- TInx d x, pc ==> (VInx d a,bot), pc
  | eval_match : forall r x x' t' t'' a' pc pc' a l d,
      maps r x (VInx d a,l) ->
      (x',a)::r |- d_choose d t' t'', pc\_/l ==> a', pc' ->
      r |- TMatch x x' t' t'', pc ==> a', pc'
  | eval_tag : forall r x v l pc,
      maps r x (v, l) ->
      r |- (TTag x), pc ==> (VConst (CTag (tag_of v)), l), pc
  | eval_bop : forall r b x' x'' pc v' v'' l0' l0'',
      maps r x' (v', l0') ->
      maps r x''(v'', l0'') ->
      In (tag_of v') (tags_args b) ->
      In (tag_of v'') (tags_args b) ->
      r |- (TBOp b x' x''), pc ==> (do_bop b v' v'', l0' \_/ l0''), pc
  | eval_bracket : forall r x t pc pc' v l l' l'',
      maps r x (VConst (CLab l), l') ->
      r |- t, (pc\_/l') ==> (v, l''), pc' ->
      l'' \_/ pc' <: l \_/ (pc\_/l') ->
      r |- TBracket x t, pc ==> (v,l), (pc\_/l')
  | eval_label_of : forall r x v l pc,
      maps r x (v, l) ->
      r |- (TLabelOf x), pc ==> (VConst (CLab l), bot), pc
  | eval_get_pc : forall r pc,
      r |- TGetPc, pc ==> (VConst (CLab pc), bot), pc
where "r |- t , pc1 ==> a , pc2" := (eval r t pc1 a pc2).

Hint Constructors eval.

Tactic Notation "eval_cases" tactic(first) ident(c) :=
  first; [
  (* perl -ne 'print "    Case_aux c \"$1\" |\n" if /\| (eval_\w+)\s/' < LBracketBigStep.v *)
    Case_aux c "eval_var" |
    Case_aux c "eval_const" |
    Case_aux c "eval_let" |
    Case_aux c "eval_abs" |
    Case_aux c "eval_app" |
    Case_aux c "eval_inx" |
    Case_aux c "eval_match" |
    Case_aux c "eval_tag" |
    Case_aux c "eval_bop" |
    Case_aux c "eval_bracket" |
    Case_aux c "eval_label_of" |
    Case_aux c "eval_get_pc"
  ].
