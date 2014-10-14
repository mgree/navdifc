
Require Import Terms.

(** * Syntax with delayed exceptions in the value space *)

(** ** Values *)

(** We tell Coq not (to try) to generate induction principles for val.
   The generated induction principles are too weak to be useful anyway *)
Unset Elimination Schemes.

Inductive Val : Type :=
| VConst : Const -> Val
| VInx : Dir -> (Box * Lab) -> Val
| VClos : list (Var * (Box * Lab)) -> Var -> Tm -> Val
with Box : Type :=
| V : Val -> Box
| D : Excp -> Box.
(* The alternative to boxes is to use sums and some Notation *)

Set Elimination Schemes.

Fixpoint fv_val (v : Val) : list Var :=
  match v with
  | VConst c => []
  | VInx _ (b,_) => fv_box b
  | VClos rho x t => remove eq_var_dec x (fv_tm t)
  end
with fv_box (b : Box) : list Var :=
  match b with
  | V v => fv_val v
  | D e => []
  end.

Definition tag_of (v : Val) : Tag :=
  match v with
  | VConst c => tag_of_const c
  | VInx _ _ => TagSum
  | VClos _ _ _ => TagFun
  end.

(** ** Boxes, Atoms and Environments *)

Definition Atom := prod Box Lab.
Definition Env := list (Var * Atom).

Definition atom_lab: Atom -> Lab := @snd Box Lab.
Definition atom_box: Atom -> Box := @fst Box Lab.

Definition fv_atom (a : Atom) : list Var := fv_box (fst a).

Definition is_abs (v : Val) : Prop :=
  match v with
  | VClos _ _ _ => True
  | _ => False
  end.

Definition is_lab (v : Val) : Prop :=
  match v with
  | VConst (CLab _) => True
  | _ => False
  end.

Definition is_excp (v : Val) : Prop :=
  match v with
  | VConst (CExcp _) => True
  | _ => False
  end.

Definition is_sum (v : Val) : Prop :=
  match v with
  | VInx _ _ => True
  | _ => False
  end.

Definition is_box (is_val : Val -> Prop) (b : Box) : Prop :=
  match b with
  | V v => is_val v
  | D _ => False
  end.

(* We start with an induction principle in Type,
   but we later specialize it to Prop and Set *)
Section atom_box_val_env_rect.
  Variable Pval : Val -> Type.
  Variable Pbox : Box -> Type.
  Variable Patom : Atom -> Type.
  Variable Penv : Env -> Type.
  Hypothesis H_v_const : forall c, Pval (VConst c).
  Hypothesis H_v_inx : forall d a,
    Patom a -> Pval (VInx d a).
  Hypothesis H_v_clos : forall r x t,
    Penv r -> Pval (VClos r x t).
  Hypothesis H_b_val : forall v,
    Pval v -> Pbox (V v).
  Hypothesis H_b_nav : forall e,
    Pbox (D e).
  Hypothesis H_atom : forall b l,
    Pbox b -> Patom (b, l).
  Hypothesis H_nil : Penv nil.
  Hypothesis H_cons : forall x a r,
    Patom a -> Penv r -> Penv ((x,a) :: r).

  Fixpoint val_rect (v : Val) {struct v} : Pval v :=
    match v as v0 return Pval v0 with
      | VConst c => H_v_const c
      | VInx d (V v,l) => 
        H_v_inx d (V v,l) (H_atom (V v) l (H_b_val v (val_rect v)))
      | VInx d (D e,l) => 
        H_v_inx d (D e,l) (H_atom (D e) l (H_b_nav e))
      | VClos r x t => H_v_clos r x t
        ((fix env_rect' (r : Env) {struct r} : Penv r :=
          match r as r0 return Penv r0 with
            | nil => H_nil
            | (x,a)::r' => H_cons x a r'
              ((fix atom_rect' (a : Atom) {struct a} : Patom a :=
                match a as a0 return Patom a0 with
                  | (V v, l) => H_atom (V v) l (H_b_val v (val_rect v))
                  | (D e, l) => H_atom (D e) l (H_b_nav e)
                end
              ) a) (env_rect' r')
          end
        ) r)
    end.

(* once we have val_rect, we can easily obtain the three nested ones *)

  Definition box_rect (b : Box) : Pbox b :=
    match b with
      | V v => H_b_val v (val_rect v)
      | D e => H_b_nav e
    end.

  Definition atom_rect (a : Atom) : Patom a :=
    match a with
      | (v,l) => H_atom v l (box_rect v)
    end.

  Fixpoint env_rect (r : Env) {struct r} : Penv r :=
    match r as r0 return Penv r0 with
      | nil => H_nil
      | (x,a)::r' => H_cons x a r'
        (atom_rect a) (env_rect r')
    end.

End atom_box_val_env_rect.

Definition atom_rec
  (Pval: Val -> Set) (Pbox: Box->Set) 
  (Patom: Atom -> Set) (Penv: Env -> Set) := atom_rect Pval Pbox Patom Penv.

Definition val_ind
  (Pval: Val->Prop) (Pbox: Box->Prop) 
  (Patom: Atom->Prop) (Penv: Env->Prop) := val_rect Pval Pbox Patom Penv.

Definition box_ind
  (Pval: Val -> Prop) (Pbox: Box->Prop) 
  (Patom: Atom -> Prop) (Penv: Env -> Prop) := box_rect Pval Pbox Patom Penv.

Definition atom_ind
  (Pval: Val -> Prop) (Pbox: Box->Prop) 
  (Patom: Atom -> Prop) (Penv: Env -> Prop) := atom_rect Pval Pbox Patom Penv.

Definition env_ind
  (Pval: Val -> Prop) (Pbox: Box->Prop) 
  (Patom: Atom -> Prop) (Penv: Env -> Prop) := env_rect Pval Pbox Patom Penv.

Combined Scheme val_box_atom_env_mutind from 
  val_ind, box_ind, atom_ind, env_ind.

(** * Derived forms (values) *)

(** ** Constant values *)

Definition vUnit := VConst CUnit.
Definition vLab l := VConst (CLab l).
Definition vTag T := VConst (CTag T).
Definition vExcp e := VConst (CExcp e).

(** ** Sums *)

Definition vInl : Atom -> Val := VInx DLeft.
Definition vInr : Atom -> Val := VInx DRight.

(** ** Booleans *)

Definition vTrue : Val := vInl (V vUnit, bot).
Definition vFalse : Val := vInr (V vUnit, bot).

