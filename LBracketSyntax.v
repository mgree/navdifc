Require Import Terms.

(** * Syntax *)

(** This is shared by LambdaBracket and LambdaThrow *)

(** ** Values *)

(** We tell Coq not (to try) to generate induction principles for val.
   The generated induction principles are too weak to be useful anyway *)
Unset Elimination Schemes.

(** The type of values. *)
Inductive Val : Type :=
| VConst : Const -> Val
| VInx : Dir -> (Val * Lab) -> Val
| VClos : list (Var * (Val * Lab)) -> Var -> Tm -> Val.

Set Elimination Schemes.

Fixpoint fv_val (v : Val) : list Var :=
  match v with
  | VConst c => []
  | VInx _ (v,_) => fv_val v
  | VClos rho x t => remove eq_var_dec x (fv_tm t)
    (* TODO: Don't I also have to remove dom rho? *)
  end.

Definition tag_of (v : Val) : Tag :=
  match v with
  | VConst c => tag_of_const c
  | VInx _ _ => TagSum
  | VClos _ _ _ => TagFun
  end.

(** ** Atoms and Environments *)

Definition Atom := prod Val Lab.
Definition Env := list (Var * Atom).

Definition atom_lab: Atom -> Lab := @snd Val Lab.
Definition atom_val: Atom -> Val := @fst Val Lab.

Definition fv_atom (a : Atom) : list Var := fv_val (fst a).

(** We produce an induction principle, that Coq cannot define by itself. *)
(* We start with an induction principle in Type,
   but we later specialize it to Prop and Set *)
Section atom_val_env_rect.
  Variable Pval : Val -> Type.
  Variable Patom : Atom -> Type.
  Variable Penv : Env -> Type.
  Hypothesis H_v_const : forall c, Pval (VConst c).
  Hypothesis H_v_inx : forall d a,
    Patom a -> Pval (VInx d a).
  Hypothesis H_v_clos : forall r x t,
    Penv r -> Pval (VClos r x t).
  Hypothesis H_atom : forall u l,
    Pval u -> Patom (u, l).
  Hypothesis H_nil : Penv nil.
  Hypothesis H_cons : forall x a r,
    Patom a -> Penv r -> Penv ((x,a) :: r).

  Fixpoint val_rect (v : Val) {struct v} : Pval v :=
    match v as v0 return Pval v0 with
      | VConst c => H_v_const c
      | VInx d (v,l) => H_v_inx d (v,l) (H_atom v l (val_rect v))
      | VClos r x t => H_v_clos r x t
        ((fix env_rect' (r : Env) {struct r} : Penv r :=
          match r as r0 return Penv r0 with
            | nil => H_nil
            | (x,a)::r' => H_cons x a r'
              ((fix atom_rect' (a : Atom) {struct a} : Patom a :=
                match a as a0 return Patom a0 with
                  | (v, l) => H_atom v l (val_rect v)
                end
              ) a) (env_rect' r')
          end
        ) r)
    end.

(* once we have val_rect, we can easily obtain the two nested ones *)

  Definition atom_rect (a : Atom) : Patom a :=
    match a with
      | (v,l) => H_atom v l (val_rect v)
    end.

  Fixpoint env_rect (r : Env) {struct r} : Penv r :=
    match r as r0 return Penv r0 with
      | nil => H_nil
      | (x,a)::r' => H_cons x a r'
        (atom_rect a) (env_rect r')
    end.

End atom_val_env_rect.

Definition val_ind
         (Pval: Val->Prop) (Patom: Atom->Prop) (Penv: Env->Prop) :=
  val_rect Pval Patom Penv.

Definition atom_ind
         (Pval: Val->Prop) (Patom: Atom->Prop) (Penv: Env->Prop) :=
  atom_rect Pval Patom Penv.

Definition env_ind
          (Pval: Val->Prop) (Patom: Atom->Prop) (Penv: Env->Prop) :=
  env_rect Pval Patom Penv.

Combined Scheme val_atom_env_mutind from val_ind, atom_ind, env_ind.

Tactic Notation "val_atom_env_mutind_cases" tactic(first) ident(c) :=
  first; [
    Case_aux c "lab" |
    Case_aux c "clos" |
    Case_aux c "val" |
    Case_aux c "nil" |
    Case_aux c "cons"
  ].
(** End of the (uninteresting) definition of the induction principle. *)

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

Definition vTrue : Val := vInl (vUnit, bot).
Definition vFalse : Val := vInr (vUnit, bot).

