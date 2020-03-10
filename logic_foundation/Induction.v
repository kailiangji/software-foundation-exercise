From LF Require Export Basics.

Theorem plus_n_O : forall n : nat, n = n + 0.
Proof.
  intro n. induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite <- IHn'. reflexivity.
Qed.

Theorem minus_diag : forall n, minus n n = 0.
Proof.
  intro n. induction n as [| n' IHn'].
  - reflexivity.
  - simpl. apply IHn'.
Qed.

Theorem mult_O_r : forall n : nat, n * 0 = 0.
Proof.
  intro n. induction n as [| n' IHn'].
  - reflexivity.
  - simpl. apply IHn'.
Qed.

Theorem plus_n_Sm : forall n m : nat, S (n + m) = n + (S m).
Proof.
  intros n m.
  induction n as [|n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite IHn'. reflexivity.
Qed.

Theorem plus_comm : forall n m : nat, n + m = m + n.
Proof.
  intros n m.
  induction n as [|n' IHn'].
  - simpl. apply plus_n_O.
  - simpl. rewrite IHn'. apply plus_n_Sm.
Qed.

Theorem plus_assoc : forall n m p : nat,
    n + (m + p) = (n + m) + p.
Proof.
  intros n m p. induction n as [| n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite IHn'. reflexivity.
Qed.

Fixpoint double (n : nat) : nat :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

Lemma double_plus : forall n, double n = n + n.
Proof.
  intro n; induction n as [|n' IHn'].
  - reflexivity.
  - simpl. rewrite <- plus_n_Sm. rewrite IHn'. reflexivity.
Qed.

Theorem evenb_S : forall n : nat,
    evenb (S n) = negb (evenb n).
Proof.
  intro n. induction n as [|n' IHn'].
  - reflexivity.
  - rewrite IHn'. simpl. rewrite negb_involutive.
    reflexivity.
Qed.

Theorem plus_rearrange : forall n m p q : nat,
    (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros.
  assert (H: n + m = m + n). { apply plus_comm. }
  rewrite H. reflexivity.
Qed.