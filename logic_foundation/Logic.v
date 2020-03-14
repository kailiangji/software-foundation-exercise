Set Warnings "-notation-overridden, -parsing".
From LF Require Export Tactics.

Definition injective {A B} (f : A -> B) :=
  forall x y : A, f x = f y -> x = y.

Lemma succ_inj : injective S.
Proof.
  unfold injective. intros x y H.
  injection H as H. apply H.
Qed.

Example and_example : 3 + 4 = 7 /\ 2 * 2 = 4.
Proof. split; reflexivity. Qed.

Lemma and_intro : forall A B : Prop, A -> B -> A /\ B.
Proof. intros A B HA HB; split; assumption. Qed.

Example and_exercise :
  forall n m : nat, n + m = 0 -> n = 0 /\ m = 0.
Proof.
  intros n m H. apply and_intro.
  - induction n as [| n' IHn'].
    + reflexivity.
    + simpl in H. discriminate H.
  - destruct m as [| m'].
    + reflexivity.
    + rewrite plus_comm in H. simpl in H. discriminate H.
Qed.

Lemma and_example2 :
  forall n m : nat, n = 0 /\ m = 0 -> n + m = 0.
Proof.
  intros n m [H1 H2]. rewrite H1, H2. reflexivity.
Qed.

Lemma and_example3 :
  forall n m : nat, n + m = 0 -> n * m = 0.
Proof.
  intros n m H.
  assert (H' : n = 0).
  { apply and_exercise in H. destruct H as [Hn Hm]. assumption. }
  rewrite H'. simpl. reflexivity.
Qed.

Lemma proj1 : forall P Q : Prop, P /\ Q -> P.
Proof. intros P Q [HP HQ]; assumption. Qed.

Lemma proj2 : forall P Q : Prop, P /\ Q -> Q.
Proof. intros P Q [HP HQ]; assumption. Qed.

Theorem and_commut : forall P Q : Prop, P /\ Q -> Q /\ P.
Proof. intros P Q [HP HQ]; split; assumption. Qed.

Theorem and_assoc : forall P Q R : Prop,
    P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
  intros P Q R [HP [HQ HR]]. split.
  - split; assumption.
  - assumption.
Qed.

Lemma or_example :
  forall n m : nat, n = 0 \/ m = 0 -> n * m = 0.
Proof.
  intros n m [Hn | Hm].
  - rewrite Hn. simpl. reflexivity.
  - rewrite Hm. rewrite mult_comm. simpl. reflexivity.
Qed.

Lemma or_intro_l : forall A B : Prop, A -> A \/ B.
Proof. intros A B HA; left; assumption. Qed.

Lemma or_intro_r : forall A B : Prop, B -> A \/ B.
Proof. intros A B HB; right; assumption. Qed.

Lemma zero_or_succ :
  forall n : nat, n = 0 \/ n = S (pred n).
Proof.
  intro n. destruct n as [| n'] eqn:E.
  - left. reflexivity.
  - right. simpl. reflexivity.
Qed.

Module MyNot.
  Definition not (P : Prop) := P -> False.

  Notation "~ x" := (not x) : type_scope.
End MyNot.

Theorem ex_falso_quodlibet : forall P : Prop,
    False -> P.
Proof. intros P HF. destruct HF. Qed.

Fact not_implies_our_not : forall P : Prop,
    ~ P -> (forall Q : Prop, P -> Q).
Proof.
  unfold not. intros Pf H Q P.
  apply H in P. destruct P.
Qed.

Notation "x <> y" := (~(x = y)).

Theorem zero_not_one : 0 <> 1.
Proof. unfold not. intro H. discriminate H. Qed.

Theorem not_False : ~ False.
Proof. unfold not. intro H. assumption. Qed.

Theorem contradiction_implies_anything : forall P Q : Prop,
    ( P /\ ~P) -> Q.
Proof.
  intros P Q [H1 H2].
  unfold not in H2.
  apply H2 in H1. destruct H1.
Qed.

Theorem double_neg : forall P : Prop, P -> ~ ~ P.
Proof.
  intros P HP.
  unfold not. intro HPF. apply HPF in HP. assumption.
Qed.

Theorem contrapositive : forall P Q : Prop,
    (P -> Q) -> (~ Q -> ~ P).
Proof.
  intros P Q H.
  unfold not. intros HQF HP.
  apply H in HP. apply HQF in HP. assumption.
Qed.

Theorem not_both_true_and_false : forall P : Prop,
    ~(P /\ ~P).
Proof.
  unfold not. intros P [H1 H2]. apply H2 in H1. assumption.
Qed.

Theorem not_true_is_false : forall b : bool,
    b <> true -> b = false.
Proof.
  intros [] H.
  - unfold not in H. exfalso.
    apply H. reflexivity.
  - reflexivity.
Qed.

Lemma True_is_true : True.
Proof. apply I. Qed.

Module MyIff.
  Definition iff (P Q : Prop) := (P -> Q) /\ (Q -> P).

  Notation "P <-> Q" := (iff P Q)
                          (at level 95, no associativity) : type_scope.

End MyIff.

Theorem iff_sym : forall P Q : Prop, (P <-> Q) -> (Q <-> P).
Proof. intros P Q [HAB HBA]. split; assumption. Qed.

Lemma not_true_iff_false : forall b,
    b <> true <-> b = false.
Proof.
  intros b. split.
  - apply not_true_is_false.
  - intro H. rewrite H. unfold not. intro H'. discriminate H'.
Qed.

Theorem or_distributes_over_and : forall P Q R : Prop,
    P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
  intros P Q R. split.
  - intros [HP | [HQ HR]].
    + split; left; apply HP.
    + split; right; assumption.
  - intros [[HP | HQ] [HP' | HR]].
    + left; assumption.
    + left; assumption.
    + left; assumption.
    + right; split; assumption.
Qed.

From Coq Require Import Setoids.Setoid.

Lemma mult_O : forall n m, n * m = 0 <-> n = 0 \/ m = 0.
Proof.
  intros n m. split.
  - intro H. destruct n as [| n'].
    + left. reflexivity.
    + destruct m as [| m'].
      * right. reflexivity.
      * simpl in H. discriminate H.
  - intros [Hn | Hm].
    + rewrite Hn; simpl. reflexivity.
    + rewrite Hm; rewrite mult_comm; simpl. reflexivity.
Qed.

Lemma or_assoc :
  forall P Q R : Prop, P \/ (Q \/ R) <-> (P \/ Q) \/ R.
Proof.
  intros P Q R. split.
  - intros [HP | [HQ | HR]].
    + left; left; assumption.
    + left; right; assumption.
    + right; assumption.
  - intros [[HP | HQ] | HR].
    + left; assumption.
    + right; left; assumption.
    + right; right; assumption.
Qed.

Lemma mult_O_3 :
  forall n m p, n * m * p = 0 <-> n = 0 \/ m = 0 \/ p = 0.
Proof.
  intros n m p. rewrite mult_O. rewrite mult_O. rewrite or_assoc.
  reflexivity.
Qed.

Lemma apply_iff_example :
  forall n m : nat, n * m = 0 -> n = 0 \/ m = 0.
Proof. intros n m H. apply mult_O. apply H. Qed.

Lemma four_is_even : exists n : nat, 4 = n + n.
Proof. exists 2. reflexivity. Qed.

Theorem exists_example_2 : forall n,
    (exists m, n = 4 + m) -> (exists o, n = 2 + o).
Proof.
  intros n [m Hm]. exists (2 + m).
  simpl in *. apply Hm.
Qed.

Theorem dist_not_exists : forall (X : Type) (P : X -> Prop),
    (forall x, P x) -> ~ (exists x, ~ P x).
Proof.
  intros X P H. unfold not. intros [x H'].
  apply H'. apply H.
Qed.

Fixpoint In {A : Type} (x : A) (l : list A) : Prop :=
  match l with
  | [] => False
  | x' :: l' => x = x' \/ In x l'
  end.

