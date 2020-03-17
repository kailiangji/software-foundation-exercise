Set Warnings "-notation-overridden,-parsing".
From LF Require Export Logic.
Require Coq.omega.Omega.

Inductive even : nat -> Prop :=
| ev_O : even 0
| ev_SS (n : nat) ( H : even n) : even (S (S n)).

Theorem ev_double : forall n, even (double n).
Proof.
  intro n. induction n as [| n' IHn'].
  - constructor.
  - simpl. apply (ev_SS (double n') IHn').
Qed.

Theorem ev_inversion : forall (n : nat),
    even n ->
    (n = 0) \/ (exists n', n = S (S n') /\ even n').
Proof.
  intros n H.
  destruct H as [ | n' H'].
  - left. reflexivity.
  - right. exists n'. split. reflexivity. apply H'.
Qed.

Theorem SSSSev__even : forall n,
    even (S (S (S (S n)))) -> even n.
Proof.
  intros n H.
  apply ev_inversion in H.
  destruct H.
  - discriminate H.
  - destruct H. destruct H.
    apply ev_inversion in H0.
    destruct H0.
    + rewrite H0 in H. discriminate H.
    + destruct H0. destruct H0. rewrite H0 in H.
      apply eq_add_S in H. apply eq_add_S in H.
      apply eq_add_S in H. apply eq_add_S in H.
      rewrite <- H in H1. apply H1.
Qed.

Theorem even5_nonsense : even 5 -> 2 + 2 = 9.
Proof.
  intro H. inversion H. inversion H1. inversion H3.
Qed.

Lemma ev_even : forall n,
    even n -> exists k, n = double k.
Proof.
  intros n H.
  induction H as [| n' H' IH].
  - exists 0. reflexivity.
  - destruct IH as [k IH].
    exists (S k). simpl. rewrite IH. reflexivity.
Qed.

Theorem ev_even_iff : forall n,
    even n <-> exists k, n = double k.
Proof.
  intro n. split.
  - apply ev_even.
  - intros [k Hk]. rewrite Hk. apply ev_double.
Qed.

Theorem ev_sum : forall n m, even n -> even m -> even (n + m).
Proof.
  intros n m Hn Hm.
  induction Hn as [|n' Hn' IH].
  - simpl. apply Hm.
  - simpl. apply ev_SS. apply IH.
Qed.

Inductive even' : nat -> Prop :=
| even'_O : even' 0
| even'_2 : even' 2
| even'_sum n m (Hn : even' n) (Hm : even' m) : even' (n + m).

Theorem even'_ev : forall n, even' n <-> even n.
Proof.
  intro n. split.
  - intro H. induction H.
    + constructor.
    + constructor. constructor.
    + apply ev_sum. apply IHeven'1. apply IHeven'2.
  - intro H. induction H.
    + constructor.
    + assert (H' : S (S n) = 2 + n).
      { simpl. reflexivity. }
      rewrite H'. apply even'_sum. constructor. apply IHeven.
Qed.

Theorem ev_ev__ev : forall n m,
    even (n + m) -> even n -> even m.
Proof.
  intros n m H1 H2. induction H2 as [| n' H2' IH].
  - simpl in H1. apply H1.
  - apply IH. simpl in H1. inversion H1. apply H0.
Qed.

Theorem ev_plus_plus : forall n m p,
    even (n + m) -> even (n + p) -> even (m + p).
Proof.
  intros n m p H1 H2.
  apply (ev_ev__ev (n+p) (m+p)).
  assert (H: n + p + (m + p) = (n + m) + (p + p)).
  { assert (H' : m + p = p + m).
    { apply plus_comm. }
    rewrite H'. rewrite plus_assoc. rewrite plus_comm.
    assert (H'': n + p + p = n + (p + p)).
    rewrite plus_assoc. reflexivity. rewrite H''.
    rewrite plus_assoc. rewrite (plus_comm n m).
    reflexivity. }
  rewrite H. apply ev_sum. apply H1. Search double.
  rewrite <- double_plus. apply ev_double.
  apply H2.
Qed.

Module Playground.
  Inductive le : nat -> nat -> Prop :=
  | le_n n : le n n
  | le_S n m (H : le n m) : le n (S m).

  Notation "m <= n" := (le m n).

  Example test_le1 : 3 <= 3.
  Proof. apply (le_n 3). Qed.

  Example test_le2 : 3 <= 6.
  Proof.
    apply (le_S 3 5). apply (le_S 3 4). apply (le_S 3 3).
    apply (le_n 3).
  Qed.

  Example test_le3 : (2 <= 1) -> 2 + 2 = 5.
  Proof.
    intro H. inversion H. inversion H2.
  Qed.

End Playground.

Definition lt (n m : nat) := le (S n) m.

Inductive square_of : nat -> nat -> Prop :=
| sq n : square_of n (n * n).

Inductive next_nat : nat -> nat -> Prop :=
| nn n : next_nat n (S n).

Inductive next_even : nat -> nat -> Prop :=
| ne_1 n : even (S n) -> next_even n (S n)
| ne_2 n (H : even (S (S n))) : next_even n (S (S n)).
