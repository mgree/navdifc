Require Import Terms.
Require Import LBracketSyntax.

(** * Big-Step Semantics for LambdaThrow *)

Inductive Result : Type :=
| Suc : Atom -> Result
| Throw : Excp -> Result.

Definition bop_result (b : BOp) (v' v'' : Val) : Result :=
  match b, v', v'' with
  | BEq, VConst c', VConst c'' =>
    if beq_const c' c'' then Suc (vTrue, bot)
    else Suc (vFalse, bot)
  | BCmp, VConst (CLab l'), VConst (CLab l'') =>
    if flows_dec l' l'' then Suc (vTrue, bot)
    else Suc (vFalse, bot)
  | BJoin, VConst (CLab l'), VConst (CLab l'') =>
    Suc (VConst (CLab (join l' l'')), bot)
  | _, _, _ => Throw eType
  end.

Definition bracket_val (res : Result) (pc_end lright : Lab) : Val :=
  match res with
  | Suc (v,l'') =>
    if flows_dec (l'' \_/ pc_end) lright then
      vInl (v,bot) (* old eval_bracket = success case *)
    else
      vInr (VConst (CExcp eBracket), bot) (* eval_bracket_fail *)
  | Throw ex =>
    if flows_dec pc_end lright then
      vInr (VConst (CExcp ex), bot) (* eval_bracket_low_pCExcp *)
    else
      vInr (VConst (CExcp eBracket), bot) (* eval_bracket_high_pc_exp *)
  end.

Definition throw_excp (v : Val) : Excp :=
  match v with
  | VConst (CExcp e) => e
  | _ => eType
  end.

(** The evaluation judgment. *)

Reserved Notation "r |- t , pc ==> res , pc'" (at level 80, no associativity).

Inductive eval : Env -> Tm -> Lab -> Result -> Lab -> Prop :=
  | eval_var : forall r x a pc,
      maps r x a ->
      r |- (TVar x), pc ==> Suc a, pc
  | eval_const : forall r c pc,
      r |- (TConst c), pc ==> Suc (VConst c, bot), pc
  | eval_let : forall r x t t' pc a pc' res pc'',
      r |- t, pc ==> Suc a, pc' ->
      ((x,a)::r) |- t', pc' ==> res, pc'' ->
      r |- (TLet x t t'), pc ==> res, pc''
  | eval_let_fail : forall r x t t' pc pc' ex,
      r |- t, pc ==> Throw ex, pc' ->
      r |- (TLet x t t'), pc ==> Throw ex, pc'
  | eval_abs : forall r x t pc,
      r |- (TAbs x t), pc ==> Suc (VClos r x t, bot), pc
  | eval_app : forall r r' x' x'' pc pc' x t l a res,
      maps r x' (VClos r' x t, l) ->
      maps r x'' a ->
      ((x,a)::r') |- t, (pc \_/ l) ==> res, pc' ->
      r |- (TApp x' x''), pc ==> res, pc'
  | eval_app_etype : forall r x' x'' pc v' l,
      maps r x' (v', l) ->
      ~(tag_of v' = TagFun) ->
      r |- (TApp x' x''), pc ==> Throw eType, (pc \_/ l)
  | eval_inx : forall r d x pc a,
      maps r x a ->
      r |- TInx d x, pc ==> Suc (VInx d a,bot), pc
  | eval_match : forall r x x' t' t'' res pc pc' a l d,
      maps r x (VInx d a,l) ->
      (x',a)::r |- d_choose d t' t'', pc\_/l ==> res, pc' ->
      r |- TMatch x x' t' t'', pc ==> res, pc'
  | eval_match_etype : forall r x x' t' t'' pc l v,
      maps r x (v,l) ->
      ~(tag_of v = TagSum) ->
      r |- TMatch x x' t' t'', pc ==> Throw eType, (pc\_/l)
  | eval_tag : forall r x v l pc,
      maps r x (v, l) ->
      r |- (TTag x), pc ==> Suc (VConst (CTag (tag_of v)), l), pc
  (* optimized version (mixes 2 rules in 1) *)
  | eval_bop : forall r b x' x'' pc v' v'' l0' l0'',
      maps r x' (v', l0') ->
      maps r x'' (v'', l0'') ->
      r |- (TBOp b x' x''), pc ==> bop_result b v' v'', (pc \_/ l0' \_/ l0'')
  (* optimized version (mixes 4 rules in 1) *)
  | eval_bracket : forall r x t pc pc' l l' res,
      maps r x (VConst (CLab l), l') ->
      r |- t, (pc \_/ l') ==> res, pc' ->
      r |- (TBracket x t), pc ==> Suc (bracket_val res pc' (l \_/ (pc \_/ l')), l), (pc \_/ l')
  | eval_bracket_etype : forall r x t pc v l,
      maps r x (v,l) ->
      ~(tag_of v = TagLab) ->
      r |- (TBracket x t), pc ==> Throw eType, (pc \_/ l)
  | eval_label_of : forall r x v l pc,
      maps r x (v, l) ->
      r |- (TLabelOf x), pc ==> Suc (VConst (CLab l), bot), pc
  | eval_get_pc : forall r pc,
      r |- TGetPc, pc ==> Suc (VConst (CLab pc), bot), pc
  (* optimized version (mixes 2 rules in 1) *)
  | eval_throw : forall r x v l pc,
      maps r x (v, l) ->
      r |- (TThrow x), pc ==> Throw (throw_excp v), (pc \_/ l)
  | eval_catch_no_excp : forall r t x t' pc a pc',
      r |- t, pc ==> Suc a, pc' ->
      r |- (TCatch t x t'), pc ==> Suc a, pc'
  | eval_catch_excp : forall r t x t' pc ex pc' res pc'',
      r |- t, pc ==> Throw ex, pc' ->
      ((x,((VConst (CExcp ex)),bot)) :: r) |- t', pc' ==> res, pc'' ->
      r |- (TCatch t x t'), pc ==> res, pc''
where "r |- t , pc ==> res , pc'" := (eval r t pc res pc').

Hint Constructors eval.

Tactic Notation "eval_cases" tactic(first) ident(c) :=
  first; [
  (* perl -ne 'print "    Case_aux c \"$1\" |\n" if /\| (eval_\w+)\s/' < LThrowBigStep.v *)
    Case_aux c "eval_var" |
    Case_aux c "eval_const" |
    Case_aux c "eval_let" |
    Case_aux c "eval_let_fail" |
    Case_aux c "eval_abs" |
    Case_aux c "eval_app" |
    Case_aux c "eval_app_etype" |
    Case_aux c "eval_inx" |
    Case_aux c "eval_match" |
    Case_aux c "eval_match_etype" |
    Case_aux c "eval_tag" |
    Case_aux c "eval_bop" |
    Case_aux c "eval_bracket" |
    Case_aux c "eval_bracket_etype" |
    Case_aux c "eval_label_of" |
    Case_aux c "eval_get_pc" |
    Case_aux c "eval_throw" |
    Case_aux c "eval_catch_no_excp" |
    Case_aux c "eval_catch_excp"
  ].
