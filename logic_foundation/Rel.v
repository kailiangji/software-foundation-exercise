Set Warnings "-notation-overridden,-parsing".
From LF Require Export IndProp.

Definition relation (X : Type) := X -> X -> Prop.

Check le : nat -> nat -> Prop.
Check le : relation nat.

Definition partial_function {X : Type} (R : relation X) :=
  forall x y1 y2 : X, R x y1 -> R x y2 -> y1 = y2.

Print next_nat.

Check next_nat : relation nat.

Theorem next_nat_partial_function : partial_function next_nat.
Proof.
  unfold partial_function. intros x y1 y2 H1 H2.
  inversion H1. inversion H2. reflexivity.
Qed.

Print total_relation.

Theorem le_not_a_partial_function : ~ (partial_function le).
Proof.
  unfold partial_function. intro H.
  assert (Nonsense: 0 = 1).
  { apply H with (x := 0).
    - apply le_n.
    - apply le_S. apply le_n.
  }
  discriminate Nonsense.
Qed.

Theorem total_relation_not_partial :
  ~(partial_function total_relation).
Proof.
  unfold partial_function. intro H.
  Print total_relation.
  assert (Nonsense : 0 = 1).
  { apply H with (x := 0).
    - apply re_n.
    - apply arti_sym. apply re_n.
  }
  discriminate Nonsense.
Qed.

Print empty_relation.

Theorem empty_relation_pairtial:
  partial_function empty_relation.
Proof.
  unfold partial_function.
  intros x y1 y2 H1 H2.
  inversion H1. inversion H.
Qed.

Definition reflexive {X : Type} (R : relation X) :=
  forall a : X, R a a.

Theorem le_reflexive : reflexive le.
Proof. unfold reflexive. apply le_n. Qed.

Definition transitive {X : Type} (R : relation X) :=
  forall a b c : X, (R a b) -> (R b c) -> (R a c).

Theorem le_trans : transitive le.
Proof.
  unfold transitive. intros a b c Hab Hbc.
  induction Hbc.
  - apply Hab.
  - apply le_S. apply IHHbc.
Qed.

Theorem le_trans' : transitive le.
Proof.
  unfold transitive. intros a b c Hab.
  apply le_ind.
  - apply Hab.
  - intros m H1 H2. apply le_S. apply H2.
Qed.


Theorem lt_trans : transitive lt.
Proof.
  unfold transitive. unfold lt.
  intros a b c H. apply le_trans.
  apply le_S. apply H.
Qed.

Theorem lt_trans' : transitive lt.
Proof.
  unfold transitive. unfold lt.
  intros a b c H1. apply le_ind.
  - apply le_S. apply H1.
  - intros m H2 H3. apply le_S. apply H3.
Qed.

Theorem lt_trans'' : transitive lt.
Proof.
  unfold lt. unfold transitive.
  intros n m o Hnm Hmo.
  induction o as [| o'].
  - inversion Hmo.
  - inversion Hmo.
    + apply le_S. rewrite H0 in Hnm. apply Hnm.
    + apply le_S. apply IHo'. apply H0.
Qed.

Theorem lt_trans''': transitive lt.
Proof.
  unfold transitive. intros a b c.
  generalize dependent b.
  generalize dependent a.
  induction c as [|c' IH].
  - intros. inversion H0.
  - intros. unfold lt in *.
    apply le_n_S. apply le_S_n in H0.
    destruct a as [| a'] eqn:Ea.
    + apply O_le_n.
    + destruct b as [| b'] eqn:Eb.
      * inversion H.
      * apply IH with (a := a') (b := b').
        { apply le_S_n. apply H. }
        { apply H0. }
Qed.

Theorem le_Sn_le : forall n m, S n <= m -> n <= m.
Proof.
  intros n m.
  apply (le_trans n (S n) m).
  apply le_S. apply le_reflexive.
Qed.

Theorem le_S_n : forall n m, S n <= S m -> n <= m.
Proof.
  intros n m H. inversion H.
  - apply le_reflexive.
  - apply (le_trans n (S n) m).
    + apply le_S. apply le_reflexive.
    + apply H1.
Qed.

Theorem le_Sn_n : forall n, ~(S n <= n).
Proof.
  apply nat_ind.
  - intro H. inversion H.
  - intros n H. unfold not in *. intro H1. apply H.
    apply le_S_n. apply H1.
Qed.

Definition symmetric {X : Type} (R : relation X) :=
  forall a b : X, (R a b) -> (R b a).

Theorem le_not_symmetric : ~ (symmetric le).
Proof.
  unfold symmetric. intro H.
  assert (Hf : 0 <= 1 -> False).
  { intro H'. apply H in H'. inversion H'. }
  apply Hf. apply le_S. apply le_reflexive.
Qed.

Definition antisymmetric {X : Type} (R : relation X) :=
  forall a b : X, (R a b) -> (R b a) -> a = b.

Theorem le_antisymmetric : antisymmetric le.
Proof.
  unfold antisymmetric.
  intros a b H1 H2.
  induction H2.
  - reflexivity.
  - apply (le_trans (S m) b m) in H1.
    Search le. apply le_Sn_n in H1.
    + contradiction.
    + apply H2.
Qed.

Theorem le_step : forall n m p,
    n < m -> m <= S p -> n <= p.
Proof.
  unfold lt. intros n m p H1 H2.
  apply le_S_n. apply (le_trans _ m _).
  - apply H1.
  - apply H2.
Qed.

Definition equivalence {X : Type} (R : relation X) :=
  (reflexive R) /\ (symmetric R) /\ (transitive R).

Definition order {X : Type} (R : relation X) :=
  (reflexive R) /\ (antisymmetric R) /\ (transitive R).

Definition preorder {X : Type} (R : relation X) :=
  (reflexive R) /\ (transitive R).

Theorem le_order : order le.
Proof.
  unfold order.
  split.
  - apply le_reflexive.
  - split.
    + apply le_antisymmetric.
    + apply le_trans.
Qed.

Inductive clos_refl_trans {A : Type} (R : relation A) : relation A :=
| rt_step x y (H : R x y) : clos_refl_trans R x y
| rt_refl x : clos_refl_trans R x x
| rt_trans x y z
           (Hxy : clos_refl_trans R x y)
           (Hyz : clos_refl_trans R y z) :
    clos_refl_trans R x z.

Theorem next_nat_closure_is_le : forall n m,
    (n <= m) <-> ((clos_refl_trans next_nat) n m).
Proof.
  intros n m. split.
  - intro H. induction H.
    + apply rt_refl.
    + apply (rt_trans _ n m (S m)).
      * apply IHle.
      * apply rt_step. apply nn.
  - intro H. induction H.
    + inversion H. apply le_S. apply le_reflexive.
    + apply le_reflexive.
    + apply (le_trans x y z); assumption.
Qed.

Inductive clos_refl_trans_ln {A : Type} (R : relation A) (x : A)
  : A -> Prop :=
| rtln_refl : clos_refl_trans_ln R x x
| rtln_trans (y z : A) (Hxy : R x y) (Hrest : clos_refl_trans_ln R y z) :
    clos_refl_trans_ln R x z.

Lemma rsc_R : forall (X : Type) (R : relation X) (x y : X),
    R x y -> clos_refl_trans_ln R x y.
Proof.
  intros X R x y H. apply (rtln_trans R x y y).
  - apply H.
  - apply rtln_refl.
Qed.

Lemma rsc_trans : forall (X : Type) (R : relation X) (x y z : X),
    clos_refl_trans_ln R x y ->
    clos_refl_trans_ln R y z ->
    clos_refl_trans_ln R x z.
Proof.
  intros X R x y z H1 H2.
  induction H1.
  - apply H2.
  - apply (rtln_trans R x y z).
    + apply Hxy.
    + apply IHclos_refl_trans_ln. apply H2.
Qed.

Theorem rtc_rsc_coincide :
  forall (X : Type) (R : relation X) (x y : X),
    clos_refl_trans R x y <-> clos_refl_trans_ln R x y.
Proof.
  intros X R x y. split.
  - intro H. induction H.
    + apply (rtln_trans R x y y).
      * apply H.
      * apply rtln_refl.
    + apply rtln_refl.
    + apply (rsc_trans X R x y z); assumption.
  - intro H. induction H.
    + apply rt_refl.
    + apply (rt_trans R x y z).
      * apply rt_step. apply Hxy.
      * apply IHclos_refl_trans_ln.
Qed.