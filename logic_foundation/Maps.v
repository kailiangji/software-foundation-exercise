From Coq Require Import Arith.Arith.
From Coq Require Import Bool.Bool.
Require Export Coq.Strings.String.
From Coq Require Import Logic.FunctionalExtensionality.
From Coq Require Import Lists.List.
Import ListNotations.

Definition eqb_string (x y : string) : bool :=
  if string_dec x y then true else false.

Theorem eqb_string_refl : forall s : string, true = eqb_string s s.
Proof.
  intro s. unfold eqb_string. destruct (string_dec s s) as [|Hs].
  - reflexivity.
  - exfalso. unfold not in Hs. apply Hs. reflexivity.
Qed.

Theorem eqb_string_true_iff : forall x y : string,
    eqb_string x y = true <-> x = y.
Proof.
  intros x y. split.
  - intro H. unfold eqb_string in H. destruct (string_dec x y).
    + apply e.
    + discriminate H.
  - intro H. rewrite H. rewrite <- eqb_string_refl. reflexivity.
Qed.

Theorem eqb_string_false_iff : forall x y : string,
    eqb_string x y = false <-> x <> y.
Proof.
  intros x y. split.
  - intro H. unfold eqb_string in H. destruct (string_dec x y).
    + discriminate H.
    + apply n.
  - intro H. unfold eqb_string. destruct (string_dec x y).
    + contradiction.
    + reflexivity.
Qed.

Theorem false_eqb_string : forall x y : string,
    x <> y -> eqb_string x y = false.
Proof. apply eqb_string_false_iff. Qed.

Definition total_map (A : Type) := string -> A.

Definition t_empty {A : Type} (v : A) : total_map A :=
  (fun _ => v).

Definition t_update {A : Type} (m : total_map A) (k : string) (v : A) :=
  fun k' => if eqb_string k k' then v else m k'.

Definition examplemap :=
  t_update (t_update (t_empty false) "foo" true) "bar" true.

Notation "'_' '!->' v" := (t_empty v) (at level 100, right associativity).

Example example_empty := (_ !-> false).

Notation "x '!->' v ';' m" := (t_update m x v)
                                (at level 100, v at next level, right associativity).

Definition examplemap' := "bar" !-> true; "foo" !-> true; _ !-> false.

Lemma t_apply_empty : forall (A : Type) (x : string) (v : A),
    (_ !-> v) x = v.
Proof. reflexivity. Qed.

Lemma t_update_eq : forall (A : Type) (m : total_map A) x v,
    (x !-> v; m) x = v.
Proof.
  intros A m x v. unfold t_update.
  rewrite <- eqb_string_refl. reflexivity.
Qed.

Lemma t_update_neq : forall (A : Type) (m : total_map A) x1 x2 v,
    x1 <> x2 -> (x1 !-> v; m) x2 = m x2.
Proof.
  intros A m x1 x2 v H. unfold t_update.
  rewrite <- eqb_string_false_iff in H.
  rewrite H. reflexivity.
Qed.

Lemma t_update_shadow : forall (A : Type) (m : total_map A) x v1 v2,
    (x !-> v2; x !-> v1; m) = (x !-> v2; m).
Proof.
  intros A m x v1 v2.
  apply functional_extensionality.
  intro x0. destruct (string_dec x x0).
  - rewrite e. rewrite t_update_eq. rewrite t_update_eq. reflexivity.
  - assert (Heq : (x !-> v2; x !-> v1; m) x0 = (x !-> v1; m) x0).
    { apply t_update_neq. apply n. }
    rewrite Heq.
    assert (Heq1 : forall v, (x !-> v; m) x0 = m x0).
    { intro v. apply t_update_neq. apply n. }
    rewrite Heq1. rewrite Heq1. reflexivity.
Qed.

Lemma eqb_stringP : forall x y : string,
    reflect (x = y) (eqb_string x y).
Proof.
  intros x y. apply iff_reflect.
  rewrite eqb_string_true_iff. reflexivity.
Qed.

Theorem t_update_same : forall (A : Type) (m : total_map A) x,
    (x !-> m x; m) = m.
Proof.
  intros A m x.
  apply functional_extensionality.
  intro x0. unfold t_update.
  assert (Heq: reflect (x = x0) (eqb_string x x0)).
  { apply eqb_stringP. }
  destruct (eqb_string x x0).
  - inversion Heq. rewrite H. reflexivity.
  - reflexivity.
Qed.

Theorem t_update_permute :
  forall (A : Type) (m : total_map A) v1 v2 x1 x2,
    x2 <> x1 ->
    ( x1 !-> v1; x2 !-> v2; m) = (x2 !-> v2; x1 !-> v1; m).
Proof.
  intros A m v1 v2 x1 x2 H.
  apply functional_extensionality.
  intro x. unfold t_update.
  assert (Heq1 : reflect (x1 = x) (eqb_string x1 x)).
  { apply eqb_stringP. }
  assert (Heq2 : reflect (x2 = x) (eqb_string x2 x)).
  { apply eqb_stringP. }
  destruct (eqb_string x1 x) eqn:E1.
  - destruct (eqb_string x2 x) eqn:E2.
    + inversion Heq1. inversion Heq2. rewrite H0 in H. rewrite H1 in H.
      exfalso. apply H. reflexivity.
    + reflexivity.
  - reflexivity.
Qed.

(** Partial maps *)
Definition partial_map (A : Type) := total_map (option A).

Definition empty {A : Type} : partial_map A := t_empty None.

Definition update {A : Type} (m : partial_map A) (x : string) (v : A) :=
  (x !-> Some v; m).

Notation "x '|->' v ';' m" := (update m x v)
  (at level 100, v at next level, right associativity).

Notation "x '|->' v" := (update empty x v) (at level 100).

Example examplepmap := ("Church" |-> true; "Turing" |-> false).

Lemma apply_empty : forall (A : Type) (x : string),
    @empty A x = None.
Proof. intros A x. reflexivity. Qed.

Lemma update_eq : forall (A : Type) (m : partial_map A) x v,
    (x |-> v; m) x = Some v.
Proof. intros A m x v. unfold update. apply t_update_eq. Qed.

Theorem update_neq : forall (A : Type) (m : partial_map A) x1 x2 v,
    x2 <> x1 -> (x2 |-> v; m) x1 = m x1.
Proof.
  intros A m x1 x2 v H. unfold update. apply t_update_neq. apply H.
Qed.

Lemma update_shadow : forall (A : Type) (m : partial_map A) x v1 v2,
    (x |-> v2; x |-> v1; m) = (x |-> v2; m).
Proof.
  intros A m x v1 v2. unfold update. apply t_update_shadow.
Qed.

Theorem update_same : forall (A : Type) (m : partial_map A) x v,
    m x = Some v -> (x |-> v; m) = m.
Proof.
  intros V m x v H. unfold update. rewrite <- H. apply t_update_same.
Qed.

Theorem update_permute : forall (A : Type) (m : partial_map A) x1 x2 v1 v2,
    x2 <> x1 ->
    ( x1 |-> v1; x2 |-> v2; m) = (x2 |-> v2; x1 |-> v1; m).
Proof.
  intros A m x1 x2 v1 v2. unfold update. apply t_update_permute.
Qed.

