(** Basics.v *)

Inductive day : Type :=
| monday
| tuesday
| wednesday
| thursday
| friday
| saturday
| sonday.

Definition next_weekday (d : day) : day :=
  match d with
  | monday => tuesday
  | tuesday => wednesday
  | wednesday => thursday
  | thursday => friday
  | friday => saturday
  | saturday => sonday
  | sonday => monday
  end.

Example test_next_weekday:
  (next_weekday (next_weekday saturday)) = monday.
Proof. simpl. reflexivity. Qed.

Inductive bool : Type := true | false.

Definition negb (b : bool) : bool :=
  match b with
  | true => false
  | false => true
  end.

Definition andb (b1 : bool) (b2 : bool) : bool :=
  match b1 with
  | true => b2
  | false => false
  end.

Definition orb (b1 : bool) (b2 : bool) : bool :=
  match b1 with
  | false => b2
  | true  => true
  end.

Example test_orb1: (orb true false) = true.
Proof. reflexivity. Qed.

Example test_orb2: (orb false false) = false.
Proof. reflexivity. Qed.

Example test_orb3: (orb false true) = true.
Proof. reflexivity. Qed.

Example test_orb4: (orb true true) = true.
Proof. reflexivity. Qed.

Notation "x && y" := (andb x y).
Notation "x || y" := (orb x y).

Definition nandb (b1 : bool) (b2 : bool) : bool :=
  negb (andb b1 b2).

Example test_nandb1: (nandb true false) = true.
Proof. reflexivity. Qed.
Example test_nandb2: (nandb false false) = true.
Proof. reflexivity. Qed.
Example test_nandb3: (nandb false true) = true.
Proof. reflexivity. Qed.
Example test_nandb4: (nandb true true) = false.
Proof. reflexivity. Qed.

Definition andb3 (b1 : bool) (b2 : bool) (b3 : bool) : bool :=
  andb (andb b1 b2) b3.

Example test_andb31: (andb3 true true true) = true.
Proof. reflexivity. Qed.
Example test_andb32: (andb3 false true true) = false.
Proof. reflexivity. Qed.
Example test_andb33: (andb3 true false true) = false.
Proof. reflexivity. Qed.
Example test_andb34: (andb3 true true false) = false.
Proof. reflexivity. Qed.

Inductive rgb : Type := red | green | blue.

Inductive color : Type :=
| black | white | primary (p : rgb).

Definition monochrome (c : color) : bool :=
  match c with
  | black | white => true
  | primary q => false
  end.

Definition isred (c : color) : bool :=
  match c with
  | primary red => true
  | _ => false
  end.

Inductive bit : Type := B0 | B1.

Inductive nybble : Type :=
| bits ( b0 b1 b2 b3 : bit).

Definition all_zero (nb : nybble) : bool :=
  match nb with
  | (bits B0 B0 B0 B0) => true
  | _ => false
  end.

Module NatPlayground.
  Inductive nat : Type :=
  | O
  | S (n : nat).

  Definition pred (n : nat) : nat :=
    match n with
    | O => O
    | S n' => n'
    end.
End NatPlayground.

Fixpoint evenb (n : nat) : bool :=
  match n with
  | O => true
  | S O => false
  | S (S n') => evenb n'
  end.

Definition oddb (n : nat) : bool :=
  negb (evenb n).

Example test_oddb1: oddb 1 = true.
Proof. simpl. reflexivity. Qed.

Example test_oddb2: oddb 4 = false.
Proof. simpl. reflexivity. Qed.

Module NatPlayground2.
  Fixpoint plus (n m : nat) : nat :=
    match n with
    | O => m
    | S n' => plus n' (S m)
    end.

  Fixpoint mult (n m : nat) : nat :=
    match n with
    | O => O
    | S n' => plus m (mult n' m)
    end.

  Fixpoint minus (n m : nat) : nat :=
    match n, m with
    | O, _ => O
    | S n', O => n
    | S n', S m' => minus n' m'
    end.
End NatPlayground2.

Fixpoint exp (base power : nat) : nat :=
  match power with
  | O => S O
  | S p => mult base (exp base p)
  end.

Fixpoint factorial (n : nat) : nat :=
  match n with
  | 0 => 1
  | S n' => mult n (factorial n')
  end.

Example test_factorial1: (factorial 3) = 6.
Proof. reflexivity. Qed.

Notation "x + y" := (plus x y)
                      (at level 50, left associativity) : nat_scope.
Notation "x - y" := (minus x y)
                      (at level 50, left associativity) : nat_scope.
Notation "x * y" := (mult x y)
                      (at level 40, left associativity) : nat_scope.

Fixpoint eqb (n m : nat) : bool :=
  match n, m with
  | O, O => true
  | S n', S m' => eqb n' m'
  | _, _ => false
  end.

Fixpoint leb (n m : nat) : bool :=
  match n, m with
  | O, _ => true
  | _, O => false
  | S n', S m' => leb n' m'
  end.

Example test_leb1: (leb 2 2) = true.
Proof. simpl. reflexivity. Qed.

Example test_leb2: (leb 2 4) = true.
Proof. simpl. reflexivity. Qed.

Example test_leb3: (leb 4 2) = false.
Proof. simpl. reflexivity. Qed.

Definition ltb (n m : nat) : bool := negb (leb m n).

Example test_ltb1: (ltb 2 2) = false.
Proof. reflexivity. Qed.
Example test_ltb2: (ltb 2 4) = true.
Proof. reflexivity. Qed.
Example test_ltb3: (ltb 4 2) = false.
Proof. reflexivity. Qed.

Notation "x =? y" := (eqb x y) (at level 70) : nat_scope.
Notation "x <=? y" := (leb x y) (at level 70) : nat_scope.
Notation "x <? y" := (ltb x y) (at level 70) : nat_scope.

Theorem plus_O_n : forall n : nat, O + n = n.
Proof. reflexivity. Qed.

Theorem plus_1_l : forall n : nat, 1 + n = S n.
Proof. reflexivity. Qed.

Theorem mult_O_l : forall n : nat, O * n = O.
Proof. reflexivity. Qed.

Theorem plus_id_example : forall n m : nat,
    n = m -> n + n = m + m.
Proof. intros n m H. rewrite H. reflexivity. Qed.

Theorem plus_id_exercise : forall n m o : nat,
    n = m -> m = o -> n + m = m + o.
Proof.
  intros n m o H1 H2. rewrite H1, <- H2.
  reflexivity.
Qed.

Theorem mult_O_plus : forall n m : nat,
    (O + n) * m = n * m.
Proof. intros n m. simpl. reflexivity. Qed.

Theorem mult_S_1 : forall n m : nat,
    m = S n -> m * (1 + n) = m * m.
Proof.
  intros n m H. simpl. rewrite <- H.
  reflexivity.
Qed.

Theorem plus_1_neq_O : forall n : nat,
    (n + 1) =? 0 = false.
Proof.
  intro n. destruct n as [|n'] eqn:E.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Theorem negb_involutive : forall b : bool,
    negb (negb b) = b.
Proof.
  intro b. destruct b eqn:E.
  - reflexivity.
  - reflexivity.
Qed.

Theorem andb_commutative : forall b c, andb b c = andb c b.
Proof.
  intros b c. destruct b eqn:Eb.
  - destruct c eqn:Ec.
    + reflexivity.
    + reflexivity.
  - destruct c eqn:Ec.
    + reflexivity.
    + reflexivity.
Qed.

Theorem andb_true_elim2 : forall b c : bool,
    andb b c = true -> c = true.
Proof.
  intros b c H.
  destruct c.
  - trivial.
  - destruct b.
    + simpl in H. apply H.
    + simpl in H. apply H.
Qed.

Theorem zero_nbeq_plus_1 : forall n : nat,
    0 =? (n + 1) = false.
Proof.
  intro n. destruct n as [| n'] eqn:E.
  - reflexivity.
  - reflexivity.
Qed.

Theorem identity_fn_applied_twice :
  forall (f : bool -> bool),
    (forall (x : bool), f x = x) ->
    forall (b : bool), f (f b) = b.
Proof.
  intros f H b. specialize H with b.
  rewrite H. apply H.
Qed.

Theorem andb_eq_orb :
  forall (b c : bool), (andb b c = orb b c) -> b = c.
Proof.
  intros b c H.
  destruct b eqn:Eb.
  - simpl in H. rewrite H. reflexivity.
  - simpl in H. apply H.
Qed.

Inductive bin : Type :=
| Z | A (n : bin) | B (n : bin).

Fixpoint incr (m : bin) : bin :=
  match m with
  | Z => B Z
  | B m' => A m
  | A m' => B m'
  end.

Fixpoint bin_to_nat (m : bin) : nat :=
  match m with
  | Z => 0
  | B m' => 1 + (bin_to_nat m') * 2
  | A m' => (bin_to_nat m') * 2
  end.