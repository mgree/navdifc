Require Export Basic.
Require Export Labels.

(** * Joined syntax of terms for the 3 calculi we consider *)

(** ** Variables *)

Definition Var := nat.

Lemma eq_var_dec : forall (x1 x2 : Var), {x1=x2} + {x1<>x2}.
Proof.
  intros x1 x2. destruct (eq_nat_decide x1 x2) as [H | H].
    apply eq_nat_eq in H. left. apply H.
    right. intros Hc. apply eq_eq_nat in Hc. apply H. apply Hc.
Qed.

(** ** Exception names *)

Definition Excp := nat.

Definition eBracket : Excp := 0.
Definition eType : Excp := 1.

(** Some silly errors in the small-step semantics that should never
    happen if all invariants are respected (e.g. closed programs) *)
Definition eUnbound : Excp := 2.
Definition eStack : Excp := 3.
Definition eLanguage : Excp := 4.

(** ** Dynamic type tags *)

Inductive Tag :=
  TagFun | TagUnit | TagSum | TagLab | TagTag | TagExcp.

Definition beq_tag (T1 T2 : Tag) : bool :=
  match T1, T2 with
  | TagFun, TagFun => true
  | TagUnit, TagUnit => true
  | TagSum, TagSum => true
  | TagLab, TagLab => true
  | TagTag, TagTag => true
  | TagExcp, TagExcp => true
  | _, _ => false
  end.

Lemma eq_tag_dec : forall (T1 T2: Tag), {T1 = T2} + {T1 <> T2}.
Proof. decide equality. Qed.

(** ** Constants *)

(** Note: exception constants are only used in LambdaThrow and LambdaNaV. *)
Inductive Const : Type :=
  | CUnit : Const
  | CLab : Lab -> Const
  | CTag : Tag -> Const
  | CExcp : Excp -> Const.

Definition tag_of_const (c : Const) : Tag :=
  match c with
  | CUnit => TagUnit
  | CLab _ => TagLab
  | CTag _ => TagTag
  | CExcp _ => TagExcp
  end.

Definition beq_const (c1 c2 : Const) : bool :=
  match c1, c2 with
  | CUnit, CUnit => true
  | CLab l1, CLab l2 =>
    if flows_dec l1 l2 then
      if flows_dec l2 l1 then true
      else false
    else false
  | CTag T1, CTag T2 => beq_tag T1 T2
  | CExcp e1, CExcp e2 => beq_nat e1 e2
  | _, _ => false
  end.

(** ** Binary operations *)

Inductive BOp :=
  BEq | BCmp | BJoin.

Definition tags_args (b : BOp) : list Tag :=
  match b with
  | BEq => [TagUnit, TagLab, TagTag, TagExcp]
  | BCmp => [TagLab]
  | BJoin => [TagLab]
  end.

(** ** Direction (for Inl/Inr) *)

Inductive Dir :=
  DLeft | DRight.

Definition d_choose {A:Type} (d : Dir) (t' t'' : A) : A :=
  match d with
  | DLeft => t'
  | DRight => t''
  end.

(** ** Terms *)

(** Not sure if it's such a good idea to share the term syntax. The
    only(?) advantage is that this way we don't have to duplicate the
    derived forms below?
    - Also generating random terms in Haskell is now shared.
*)

Inductive Tm : Type :=
| TVar : Var -> Tm
| TConst : Const -> Tm
| TLet : Var -> Tm -> Tm -> Tm
| TAbs : Var -> Tm -> Tm
| TApp : Var -> Var -> Tm
| TInx : Dir -> Var -> Tm
| TMatch : Var -> Var -> Tm -> Tm -> Tm
| TTag : Var -> Tm
| TBOp : BOp -> Var -> Var -> Tm
| TBracket : Var -> Tm -> Tm
| TLabelOf : Var -> Tm
| TGetPc : Tm
(** LambdaNaV-specific *)
| TMkNav : Var -> Tm
| TToSum : Var -> Tm
(** LambdaThrow-specific *)
| TThrow : Var -> Tm
| TCatch : Tm -> Var -> Tm -> Tm.

Tactic Notation "Tm_cases" tactic(first) ident(c) :=
  first; [
  (* perl -ne 'print "    Case_aux c \"$1\" |\n" if /\| (T\w+)\s/' < Terms.v *)
    Case_aux c "TVar" |
    Case_aux c "TConst" |
    Case_aux c "TLet" |
    Case_aux c "TAbs" |
    Case_aux c "TApp" |
    Case_aux c "TInx" |
    Case_aux c "TMatch" |
    Case_aux c "TTag" |
    Case_aux c "TBOp" |
    Case_aux c "TBracket" |
    Case_aux c "TLabelOf" |
    Case_aux c "TGetPc" |
    Case_aux c "TMkNav" |
    Case_aux c "TToSum" |
    Case_aux c "TThrow" |
    Case_aux c "TCatch"
  ].

(* TODO: this produces lists with lots of duplicates;
   would it be hard to avoid creating duplicates? *)
Fixpoint fv_tm (t : Tm) : list Var :=
  match t with
  | TVar x => [x]
  | TConst c => []
  | TLet x t1 t2 => fv_tm t1 ++ (remove eq_var_dec x (fv_tm t2))
  | TAbs x t => remove eq_var_dec x (fv_tm t)
  | TApp x1 x2 => [x1,x2]
  | TInx _ x => [x]
  | TMatch x x' t1 t2 => x :: (remove eq_var_dec x' (fv_tm t1))
                           ++ (remove eq_var_dec x' (fv_tm t2))
  | TTag x => [x]
  | TBOp _ x1 x2 => [x1,x2]
  | TBracket x t => x :: fv_tm t
  | TLabelOf x => [x]
  | TGetPc => []
  | TMkNav x => [x]
  | TToSum x => [x]
  | TThrow x => [x]
  | TCatch t1 x t2 => fv_tm t1 ++ (remove eq_var_dec x (fv_tm t2))
  end.

Fixpoint size_tm (t : Tm) : nat :=
  match t with
  | TVar _ => 1
  | TConst c => 1
  | TLet _ t1 t2 => size_tm t1 + size_tm t2 + 1
  | TAbs _ t => size_tm t + 1
  | TApp _ _ => 1
  | TInx _ _ => 1
  | TMatch _ _ t1 t2 => size_tm t1 + size_tm t2 + 1
  | TTag _ => 1
  | TBOp _ _ _ => 1
  | TBracket _ t => size_tm t + 1
  | TLabelOf _ => 1
  | TGetPc => 1
  | TMkNav _ => 1
  | TToSum _ => 1
  | TThrow _ => 1
  | TCatch t1 x t2 => size_tm t1 + size_tm t2 + 1
  end.

(** * Convenient derived constructs *)

Definition fresh xs := proj1_sig (fresh_for_list xs).

(** ** Constant terms *)

Definition tCUnit := TConst CUnit.
Definition tCLab l := TConst (CLab l).
Definition tCTag T := TConst (CTag T).
Definition tCExcp e := TConst (CExcp e).

(** ** Non-ANF constructs *)

Definition tApp (t1 t2 : Tm) : Tm :=
  let x1 := fresh (fv_tm t1 ++ fv_tm t2) in
  let x2 := fresh (x1 :: fv_tm t1 ++ fv_tm t2) in
  TLet x1 t1 (TLet x2 t2 (TApp x1 x2)).

Definition tInl (t : Tm) : Tm :=
  TLet 0 t (TInx DLeft 0).
Definition tInr (t : Tm) : Tm :=
  TLet 0 t (TInx DRight 0).
Definition tMatch t x' t1 t2 : Tm :=
  let x := fresh (fv_tm t1 ++ fv_tm t2) in
  TLet x t (TMatch x x' t1 t2).

Definition tTag (t : Tm) : Tm :=
  let x := fresh (fv_tm t) in
  TLet x t (TTag x).

Definition tBOp b (t1 t2 : Tm) : Tm :=
  let x1 := fresh (fv_tm t1 ++ fv_tm t2) in
  let x2 := fresh (x1 :: fv_tm t1 ++ fv_tm t2) in
  TLet x1 t1 (TLet x2 t2 (TBOp b x1 x2)).

Definition tEq := tBOp BEq.
Definition tCmp := tBOp BCmp.
Definition tJoin := tBOp BJoin.

Definition tBracket (t1 t2 : Tm) : Tm :=
  let x1 := fresh (fv_tm t1 ++ fv_tm t2) in
  TLet x1 t1 (TBracket x1 t2).

Definition tLabelOf (t : Tm) : Tm :=
  let x := fresh (fv_tm t) in
  TLet x t (TLabelOf x).

Definition tThrow (t : Tm) : Tm :=
  let x := fresh (fv_tm t) in
  TLet x t (TThrow x).

Definition tMkNav (t : Tm) : Tm :=
  let x := fresh (fv_tm t) in
  TLet x t (TMkNav x).

Definition tToSum (t : Tm) : Tm :=
  let x := fresh (fv_tm t) in
  TLet x t (TToSum x).

(** ** More derived constructs *)

(** Identity and constant functions *)
Definition tId : Tm := (TAbs 0 (TVar 0)).
Definition tCst (t : Tm) : Tm := 
  let x := fresh (fv_tm t) in
  TAbs x t.

(** Booleans *)
Definition tTrue : Tm := tInl tCUnit.
Definition tFalse : Tm := tInr tCUnit.
Definition tIf (t : Tm) (t1 t2 : Tm) : Tm :=
  let x' := fresh ((fv_tm t1) ++ (fv_tm t2)) in
  tMatch t x' t1 t2.
Definition tNot (t : Tm) := tIf t tFalse tTrue.

(** ** Auxiliary commonly used by encodings *)

Definition tHasTag T (t tk : Tm) : Tm :=
  tIf (tEq (tTag t) (TConst (CTag T)))
    tk (tInr (TConst (CExcp eType))).

Definition tSBind tsum xk tk :=
  tMatch tsum xk tk (TInx DRight xk).
