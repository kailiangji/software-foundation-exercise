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

