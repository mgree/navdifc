Require Export Datatypes. Open Scope bool_scope.
Require Export String. Open Scope string_scope.
Require Export List. Open Scope list_scope.
Require Export TheoryList.
Require Export EqNat.
Require Export Coq.Arith.MinMax.
Require Import Omega.

Tactic Notation "invs" hyp(H):= inversion H; subst.
Tactic Notation "invsc" hyp(H):= invs H; clear H.

Ltac split3 := split; [| split].
Ltac split4 := split; [| split3].
Ltac split5 := split; [| split4].

(* "Stolen" from the metatheory library *)

(** [get] looks up a key in an association list. *)

Fixpoint get {A} (E : list (nat * A)) (x : nat) : option A :=
  match E with
    | nil => None
    | (y, c) :: F => if beq_nat x y then Some c else get F x
  end.

(** [maps] is a ternary predicate that holds when the first binding in
    the list for the given key is to the given value. *)

Definition maps {A} (E : list (nat * A)) (x : nat) (a : A) : Prop :=
  get E x = Some a.

Lemma maps_inj : forall A s (v1 v2 : A) r,
  maps r s v1 ->
  maps r s v2 ->
  v1 = v2.
Proof. intros. unfold maps in *. rewrite H in H0. invs H0. trivial. Qed.

Lemma maps_dec : forall {A} (r: list (nat * A)) s,
  { exists v, maps r s v } + { forall v, ~ maps r s v }.
Proof.
intros A r s. unfold maps; induction r; simpl.
right. intro; congruence.
destruct a as [y c].
destruct IHr as [H | H].
left. destruct (beq_nat s y). subst. eauto. assumption.
destruct (beq_nat s y); [left|right].
subst. eauto.
assumption.
Qed.

(* "Stolen" from SfLib: Software Foundations Library *)

Ltac move_to_top x :=
  match reverse goal with
  | H : _ |- _ => try move x after H
  end.

Tactic Notation "assert_eq" ident(x) constr(v) :=
  let H := fresh in
  assert (x = v) as H by reflexivity;
  clear H.

Tactic Notation "Case_aux" ident(x) constr(name) :=
  first [
    set (x := name); move_to_top x
  | assert_eq x name; move_to_top x
  | fail 1 "because we are working on a different case" ].

Tactic Notation "Case" constr(name) := Case_aux Case name.
Tactic Notation "SCase" constr(name) := Case_aux SCase name.
Tactic Notation "SSCase" constr(name) := Case_aux SSCase name.
Tactic Notation "SSSCase" constr(name) := Case_aux SSSCase name.
Tactic Notation "SSSSCase" constr(name) := Case_aux SSSSCase name.
Tactic Notation "SSSSSCase" constr(name) := Case_aux SSSSSCase name.
Tactic Notation "SSSSSSCase" constr(name) := Case_aux SSSSSSCase name.
Tactic Notation "SSSSSSSCase" constr(name) := Case_aux SSSSSSSCase name.

Notation "[ ]" := nil.
Notation "[ x ]" := (cons x []).
Notation "[ x , .. , y ]" := (cons x .. (cons y []) ..).

(* fresh taken from http://www.cis.upenn.edu/~plclub/metalib/current/html/MetatheoryAtom.html#atom_fresh *)
Lemma max_lt_r : forall x y z,
  x <= z -> x <= max y z.
Proof.
  induction x. auto with arith.
  induction y. auto with arith.
    simpl. induction z. omega. auto with arith.
Qed.

Lemma nat_list_max : forall (xs : list nat),
  { n : nat | forall x, List.In x xs -> x <= n }.
Proof.
  induction xs as [ | x xs [y H] ].
  (* case: nil *)
  exists 0. inversion 1.
  (* case: cons x xs *)
  exists (max x y). intros z J. simpl in J. destruct J as [K | K].
    subst. auto with arith.
    auto using max_lt_r.
Qed.

Lemma fresh_for_list :
  forall (xs : list nat), { n : nat | ~ List.In n xs }.
Proof.
  intros xs. destruct (nat_list_max xs) as [x H].
  exists (S x). intros J. lapply (H (S x)). omega. trivial.
Qed.
