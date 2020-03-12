Set Warnings "-notation-overridden,-parsing".
From LF Require Export Poly.

Theorem rev_exercise1 : forall (l l' : list nat),
    l = rev l' -> l' = rev l.
Proof.
  intros. rewrite H. rewrite rev_involutive. reflexivity.
Qed.

Theorem trans_eq : forall (X : Type) (n m o : X),
    n = m -> m = o -> n = o.
Proof.
  intros X n m o eq1 eq2. rewrite eq1, <- eq2. reflexivity.
Qed.

Example trans_eq_example : forall (a b c d e f : nat),
    [a;b] = [c;d] -> [c;d] = [e;f] -> [a;b] = [e;f].
Proof.
  intros a b c d e f. apply trans_eq. Qed.

Example trans_eq_exercise : forall (n m o p : nat),
    m = (minustwo o) ->
    (n + p) = m ->
    (n + p) = (minustwo o).
Proof.
  intros. apply trans_eq with (m := m).
  - assumption.
  - assumption.
Qed.

Theorem S_injective : forall n m : nat,
    S n = S m -> n = m.
Proof.
  intros n m H. injection H. intros Hnm. apply Hnm.
Qed.

Theorem injection_ex1 : forall (n m o : nat),
    [n; m] = [o; o] -> [n] = [m].
Proof.
  intros. injection H. intros. rewrite H0, H1. reflexivity.
Qed.

Theorem injection_ex2 : forall (n m : nat),
    [n] = [m] -> n = m.
Proof.
  intros n m H. injection H as Hnm. rewrite Hnm.
  reflexivity.
Qed.

Example injection_ex3 : forall (X : Type) (x y z : X) (l j : list X),
    x :: y :: l = z :: j ->
    y :: l = x :: j ->
    x = y.
Proof.
  intros. injection H0 as Hyx. symmetry. apply Hyx.
Qed.

Theorem eqb_O_l : forall n, 0 =? n = true -> n = 0.
Proof.
  intros. simpl in H. destruct n as [| n'] eqn:E.
  - reflexivity.
  - discriminate H.
Qed.

Theorem discriminate_ex1 : forall n : nat,
    S n = O -> 2 + 2 = 5.
Proof.
  intros n H. discriminate H.
Qed.

Theorem discrimiante_ex2: forall (n m : nat),
    false = true -> [n] = [m].
Proof. intros. discriminate H. Qed.

Example discrimiate_ex3 :
  forall (X : Type) (x y z : X) (l j : list X),
    x :: y :: l = [] -> x = z.
Proof. intros. discriminate H. Qed.

Theorem f_equal : forall (A B : Type) (f : A -> B) (x y : A),
    x = y -> f x = f y.
Proof. intros. rewrite H. reflexivity. Qed.

Theorem S_inj : forall (n m : nat) (b : bool),
    (S n) =? (S m) = b -> n =? m = b.
Proof. intros. simpl in H. apply H. Qed.

Theorem plus_n_n_injective : forall n m,
    n + n = m + m -> n = m.
Proof.
  intro n. induction n as [| n' IHn'].
  - intros m H. simpl in H.
    induction m as [| m' IHm'].
    + reflexivity.
    + simpl in *. discriminate H.
  - intros m H. simpl in H.
    induction m as [| m' IHm'].
    + simpl in H. discriminate H.
    + simpl in *. injection H as H'.
      Search plus. rewrite <- plus_n_Sm in H'.
      rewrite <- plus_n_Sm in H'.
      injection H' as H''. apply IHn' in H''.
      rewrite H''. reflexivity.
Qed.

Theorem double_injective : forall n m,
    double n = double m -> n = m.
Proof.
  intros n m. rewrite double_plus, double_plus.
  apply plus_n_n_injective.
Qed.

Theorem eqb_true : forall n m, n =? m = true -> n = m.
Proof.
  intro n. induction n.
  - intros m H. destruct m as [| m'] eqn:E.
    + reflexivity.
    + discriminate H.
  - intros m H. destruct m as [| m'] eqn:E.
    + discriminate H.
    + simpl in H. apply IHn in H. rewrite H.
      reflexivity.
Qed.

Theorem double_injective_take2 : forall n m,
    double n = double m -> n = m.
Proof.
  intros n m.
  (* n and m are both in the context *)
  generalize dependent n.
  (* Now n is back in the goal and we can do induction on
     m and get a sufficiently general IH. *)
  induction m as [| m'].
  - simpl. intros n eq. destruct n as [| n' ] eqn:E.
    + reflexivity.
    + discriminate eq.
  - simpl. intros n eq. destruct n as [| n' ] eqn:E.
    + discriminate eq.
    + simpl in eq. injection eq as eq. apply IHm' in eq.
      rewrite eq. reflexivity.
Qed.

Theorem eqb_id_true : forall x y,
    eqb_id x y = true -> x = y.
Proof.
  intros [m] [n]. simpl. intro H.
  apply eqb_true in H.
  rewrite H. reflexivity.
Qed.

Theorem nth_error_after_last : forall (n : nat) (X : Type) (l : list X),
    length l = n -> nth_error l n = None.
Proof.
  intros n X l. generalize n. induction l.
  - reflexivity.
  - intros n0 H. induction n0.
    + discriminate H.
    + simpl in H. injection H as H. apply IHl in H.
      simpl. apply H.
Qed.

Definition square n := n * n.

Lemma plus_mult_l : forall a b c, (a + b) * c = a * c + b * c.
Proof.
  intros a b c. induction a.
  - simpl. reflexivity.
  - simpl. rewrite IHa. rewrite plus_assoc. reflexivity.
Qed.

Lemma mult_assoc : forall a b c, a * b * c = a * (b * c).
Proof.
  intros a b c. induction a.
  - simpl. reflexivity.
  - simpl. rewrite <- IHa. rewrite plus_mult_l. reflexivity.
Qed.

Lemma mult_comm : forall n m, n * m = m * n.
Proof.
  intros n m. induction n.
  - simpl. rewrite <- mult_n_O. reflexivity.
  - simpl. rewrite IHn. rewrite plus_comm. rewrite mult_n_Sm.
    reflexivity.
Qed.

Lemma square_mult : forall n m, square (n * m) = square n * square m.
Proof.
  intros n m. unfold square. rewrite <- mult_assoc.
  rewrite <- mult_assoc.
  assert (H: n * m * n = n * n * m).
  { rewrite mult_comm. rewrite mult_assoc. reflexivity. }
  rewrite H. reflexivity.
Qed.

Definition foo (x : nat) := 5.

Fact silly_fact_1 : forall m, foo m + 1 = foo (m + 1) + 1.
Proof. intro m. simpl. reflexivity. Qed.

Definition bar x :=
  match x with
  | O => 5
  | S _ => 5
  end.

Fact silly_fact_2 : forall m, bar m + 1 = bar (m + 1) + 1.
Proof.
  intro m. destruct m as [| m'] eqn:E.
  - reflexivity.
  - simpl. reflexivity.
Qed.

Definition sillyfun (n : nat) : bool :=
  if n =? 3 then false
  else if n =? 5 then false
  else false.

Theorem sillyfun_false : forall n : nat,
    sillyfun n = false.
Proof.
  intro n. unfold sillyfun.
  destruct (n =? 3) eqn:E1.
  - reflexivity.
  - destruct (n =? 5) eqn:E2.
    + reflexivity.
    + reflexivity.
Qed.

Theorem combine_split : forall X Y (l : list (X * Y)) l1 l2,
    split l = (l1, l2) -> combine l1 l2 = l.
Proof.
  intros X Y l. induction l as [| h t IHt].
  - intros l1 l2 H. inversion H. reflexivity.
  - intros l1 l2 H. destruct h as [a b] eqn:E in H. simpl in H.
    destruct (split t) as [l1' l2'] eqn:Et in H. inversion H.
    simpl. inversion E.
    assert (Heq : forall (X : Type) (x : X) (l1 l2 : list X),
               l1 = l2 -> x :: l1 = x::l2).
    { intros. rewrite H3. reflexivity. }
    apply Heq. apply IHt. apply Et.
Qed.

Definition sillyfun1 (n : nat) : bool :=
  if n =? 3 then true
  else if n =? 5 then true
       else false.

Theorem sillyfun1_odd : forall (n : nat),
    sillyfun1 n = true -> oddb n = true.
Proof.
  intros n H.
  unfold sillyfun1 in H.
  destruct (n =? 3) eqn:E3 in H.
  - apply eqb_true in E3. rewrite E3. reflexivity.
  - destruct (n =? 5) eqn:E5 in H.
    + apply eqb_true in E5. rewrite E5. reflexivity.
    + discriminate H.
Qed.

Theorem bool_fn_applied_thrice :
  forall (f : bool -> bool) (b : bool), f (f (f b)) = f b.
Proof.
  intros f b. destruct (f b) eqn:E.
Admitted.

Theorem eqb_sym : forall n m : nat, (n =? m) = (m =? n).
Proof.
  intro n. induction n as [| n' IHn'].
  - intro m. simpl. destruct m as [| m'] eqn:Em.
    + reflexivity.
    + simpl. reflexivity.
  - intro m. destruct m as [| m'] eqn:Em.
    + simpl. reflexivity.
    + simpl. apply IHn'.
Qed.

Theorem eqb_trans : forall n m p,
    n =? m = true ->
    m =? p = true ->
    n =? p = true.
Proof.
  intro n. induction n as [| n' IHn'].
  - intro m. induction m as [| m' IHm'].
    + intro p. intro H1. destruct p as [| p'] eqn:Ep.
      * reflexivity.
      * simpl. intro H2. apply H2.
    + intro p. intro H1. simpl in H1. discriminate H1.
  - intro m. induction m as [| m' IHm'].
    + intro p. intro H1. simpl in H1. discriminate H1.
    + intro p. intro H1. simpl in H1. destruct p as [| p'] eqn:Ep.
      * intro H2. simpl in H2. discriminate H2.
      * intro H2. simpl in H2. simpl. apply IHn' with m'.
        apply H1. apply H2.
Qed.

Definition split_combine_statement : Prop :=
  forall X Y (l1 : list X) (l2 : list Y),
    length l1 = length l2 -> split (combine l1 l2) = (l1, l2).

Theorem split_combine : split_combine_statement.
Proof.
  unfold split_combine_statement.
  intros X Y l1. induction l1 as [| h1 l1' IHl1'].
  - intros l2 H. destruct l2 as [| h2 l2'] eqn:El2.
    + reflexivity.
    + simpl in H. discriminate H.
  - intros l2 H. destruct l2 as [| h2 l2'] eqn:El2.
    + simpl in H. discriminate H.
    + simpl in H. injection H as H. apply IHl1' in H.
      simpl. rewrite H. reflexivity.
Qed.

Theorem filter_exercise :
  forall (X : Type) (test : X -> bool) (x : X) (l lf : list X),
    filter test l = x :: lf -> test x = true.
Proof.
  intros X test x l. induction l as [| h l' IHl'].
  - intros lf H. simpl in H. discriminate H.
  - intros lf H. simpl in H. destruct (test h) eqn:E in H.
    + inversion H. rewrite H1 in E. apply E.
    + apply IHl' with lf. apply H.
Qed.

Fixpoint forallb {X : Type} (test : X -> bool) (l : list X) : bool :=
  match l with
  | [] => true
  | h :: t => if test h then forallb test t else false
  end.

Example test_forallb_1 : forallb oddb [1;3;5;7;9] = true.
Proof. reflexivity. Qed.
Example test_forallb_2 : forallb negb [false;false] = true.
Proof. reflexivity. Qed.
Example test_forallb_3 : forallb evenb [0;2;4;5] = false.
Proof. reflexivity. Qed.
Example test_forallb_4 : forallb (eqb 5) [] = true.
Proof. reflexivity. Qed.

Fixpoint existsb {X : Type} (test : X -> bool) (l : list X) : bool :=
  match l with
  | [] => false
  | h :: t => if test h then true else existsb test t
  end.

Example test_existsb_1 : existsb (eqb 5) [0;2;3;6] = false.
Proof. reflexivity. Qed.
Example test_existsb_2 : existsb (andb true) [true;true;false] = true.
Proof. reflexivity. Qed.
Example test_existsb_3 : existsb oddb [1;0;0;0;0;3] = true.
Proof. reflexivity. Qed.
Example test_existsb_4 : existsb evenb [] = false.
Proof. reflexivity. Qed.

Definition existsb' {X : Type} (test : X -> bool) (l : list X) : bool :=
  negb (forallb (fun x => negb (test x)) l).

Theorem existsb_existsb' :
  forall (X : Type) (test : X -> bool) (l : list X),
    existsb test l = existsb' test l.
Proof.
  intros. induction l as [| h t IHt].
  - reflexivity.
  - simpl. destruct (test h) eqn:E.
    + unfold existsb'. simpl. rewrite E.
      simpl. reflexivity.
    + unfold existsb'. simpl. rewrite E.
      simpl. fold (existsb' test t). apply IHt.
Qed.