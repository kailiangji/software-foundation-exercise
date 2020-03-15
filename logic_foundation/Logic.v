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

Example In_example_1 : In 4 [1; 2; 3; 4; 5].
Proof. simpl. right; right; right; left; reflexivity. Qed.

Example In_example_2 :
  forall n, In n [2; 4] -> exists n', n = 2 * n'.
Proof.
  intros n H. simpl in H. destruct H.
  - rewrite H. exists 1. reflexivity.
  - destruct H.
    + rewrite H. exists 2. reflexivity.
    + destruct H.
Qed.

Lemma In_map :
  forall (A B : Type) (f : A -> B) (l : list A) (x : A),
    In x l -> In (f x) (map f l).
Proof.
  intros. induction l as [| h t IHt].
  - simpl in H. destruct H.
  - simpl in H. simpl. destruct H.
    + rewrite H. left. reflexivity.
    + apply IHt in H. right. assumption.
Qed.

Lemma In_map_iff :
  forall (A B : Type) (f : A -> B) (l : list A) (y : B),
    In y (map f l) -> exists x, f x = y /\ In x l.
Proof.
  intros. induction l as [| h t IHt].
  - simpl in H. destruct H.
  - simpl in H. destruct H.
    + exists h. split.
      * symmetry. apply H.
      * simpl. left. reflexivity.
    + apply IHt in H. destruct H. exists x.
      destruct H. split.
      * apply H.
      * simpl; right; assumption.
Qed.

Fixpoint All {T : Type} (P : T -> Prop) (l : list T) : Prop :=
  match l with
  | [] => True
  | h :: t => P h /\ All P t
  end.

Lemma All_In : forall T (P : T -> Prop) (l : list T),
    (forall x, In x l -> P x) <-> All P l.
Proof.
  intros. split.
  - intro H. induction l as [| h t IHt].
    + reflexivity.
    + simpl. split.
      * apply H. simpl. left. reflexivity.
      * apply IHt. intros x H'. apply H. simpl; right. assumption.
  - intros H x H'. induction l as [| h t IHt].
    + simpl in H'. destruct H'.
    + simpl in H. simpl in H'. destruct H. destruct H'.
      * rewrite H1. apply H.
      * apply IHt. apply H0. apply H1.
Qed.

Definition combine_odd_even (Podd Peven : nat -> Prop)
  : nat -> Prop :=
  fun n => if oddb n then Podd n else Peven n.

Theorem combine_odd_even_intro :
  forall (Podd Peven : nat -> Prop) (n : nat),
    (oddb n = true -> Podd n) ->
    (oddb n = false -> Peven n) ->
    combine_odd_even Podd Peven n.
Proof.
  intros Podd Peven n H1 H2.
  unfold combine_odd_even.
  destruct (oddb n) eqn:E.
  - apply H1. reflexivity.
  - apply H2. reflexivity.
Qed.

Theorem combine_odd_even_elim_odd :
  forall (Podd Peven : nat -> Prop) (n : nat),
    combine_odd_even Podd Peven n ->
    oddb n = true -> Podd n.
Proof.
  intros. unfold combine_odd_even in H.
  rewrite H0 in H. apply H.
Qed.

Theorem combine_odd_even_elim_even :
  forall (Podd Peven : nat -> Prop) (n : nat),
    combine_odd_even Podd Peven n ->
    oddb n = false ->
    Peven n.
Proof.
  intros. unfold combine_odd_even in H.
  rewrite H0 in H. assumption.
Qed.

Lemma plus_comm3 :
  forall x y z, x + (y + z) = (z + y) + x.
Proof.
  intros x y z.
  rewrite plus_comm.
  rewrite (plus_comm y z).
  reflexivity.
Qed.

Lemma in_not_nil :
  forall A (x : A) (l : list A), In x l -> l <> [].
Proof.
  intros. unfold not. intro H'. destruct l.
  - simpl in H. assumption.
  - discriminate H'.
Qed.

Lemma in_not_nil_42 :
  forall l : list nat, In 42 l -> l <> [].
Proof.
  apply (in_not_nil nat 42).
Qed.

Example lemma_application_ex :
  forall {n : nat} {ns : list nat},
    In n (map (fun m => m * 0) ns) -> n = 0.
Proof.
  intros n ns H.
  induction ns.
  - simpl in H. destruct H.
  - simpl in H. destruct H.
    + rewrite mult_comm in H. simpl in H. apply H.
    + apply IHns. apply H.
Qed.

Example function_equality_ex1 :
  (fun x => 3 + x) = (fun x => (pred 4) + x).
Proof. simpl. reflexivity. Qed.

Axiom functional_extensionality :
  forall {X Y : Type} {f g : X -> Y},
    (forall (x : X), f x = g x) -> f = g.

Example function_equality_ex2 :
  (fun x => plus x 1) = (fun y => plus 1 y).
Proof.
  apply functional_extensionality. intro x.
  apply plus_comm.
Qed.

Print Assumptions function_equality_ex2.

Fixpoint rev_append {X} (l1 l2 : list X) : list X :=
  match l1 with
  | [] => l2
  | x :: l1' => rev_append l1' (x :: l2)
  end.

Definition tr_rev {X} (l : list X) : list X :=
  rev_append l [].

Lemma tr_rev_correct : forall X, @tr_rev X = @rev X.
  intro X. apply functional_extensionality.
  intro x. induction x as [| h t IHt].
  - reflexivity.
  - simpl. unfold tr_rev.
    simpl. unfold tr_rev in IHt. rewrite <- IHt.
    assert (H : forall (X : Type) (l1 l2 : list X),
               rev_append l1 l2 = rev_append l1 [] ++ l2).
    { intros X0 l1.  induction l1.
      - simpl. reflexivity.
      - simpl. intro l2. rewrite (IHl1 [x]).
        rewrite <- app_assoc. simpl. apply IHl1.
    }
    rewrite <- H. reflexivity.
Qed.

Example even_42_bool : evenb 42 = true.
Proof. reflexivity. Qed.

Example even_42_prop : exists k, 42 = double k.
Proof. exists 21. reflexivity. Qed.

Theorem evenb_double : forall k, evenb (double k) = true.
Proof.
  intro k. induction k as [|k' IHk'].
  - reflexivity.
  - simpl. apply IHk'.
Qed.

Theorem evenb_double_conv : forall n,
    exists k, n = if evenb n then double k else S (double k).
Proof.
  intro n. induction n as [| n' IHn'].
  - exists 0. reflexivity.
  - destruct IHn'. destruct (evenb n') eqn:E.
    + exists x. rewrite evenb_S. rewrite E.
      simpl. rewrite H. reflexivity.
    + exists (S x). rewrite evenb_S. rewrite E.
      simpl. rewrite H. reflexivity.
Qed.

Theorem even_bool_prop : forall n,
    evenb n = true <-> exists k, n = double k.
Proof.
  intro n. split.
  - intro H. assert (H' : exists k, n = if evenb n then double k
                                        else S (double k)).
    { apply evenb_double_conv. }
    rewrite H in H'. assumption.
  - intro H. destruct H. rewrite H. apply evenb_double.
Qed.

Theorem eqb_eq : forall n1 n2 : nat,
    n1 =? n2 = true <-> n1 = n2.
Proof.
  intros n1 n2. split.
  - apply eqb_true. 
  - intro H. rewrite H. apply eqb_refl.
Qed.

Example even_1000 : exists k, 1000 = double k.
Proof. apply even_bool_prop. reflexivity. Qed.

Lemma plus_eqb_example : forall n m p : nat,
    n =? m = true -> n + p =? m + p = true.
Proof.
  intros. rewrite eqb_eq in H. rewrite H.
  apply eqb_refl.
Qed.

Lemma andb_true_iff : forall b1 b2 : bool,
    b1 && b2 = true <-> b1 = true /\ b2 = true.
Proof.
  intros b1 b2. split.
  - intro H. split.
    + apply (andb_true_elim2 b2).
      rewrite andb_commutative. assumption.
    + apply (andb_true_elim2 b1). assumption.
  - intros [H1 H2]. rewrite H1, H2. reflexivity.
Qed.

Lemma orb_true_iff : forall b1 b2,
    b1 || b2 = true <-> b1 = true \/ b2 = true.
Proof.
  intros b1 b2. split.
  - intro H. destruct b1 eqn:Eb1.
    + left. reflexivity.
    + simpl in H. right. apply H.
  - intros [H1 | H2].
    + rewrite H1. simpl. reflexivity.
    + rewrite H2. destruct b1; reflexivity.
Qed.

Theorem eqb_neq : forall x y : nat,
    x =? y = false <-> x <> y.
Proof.
  intros x y. split.
  - intro H. unfold not. rewrite <- eqb_eq.
    intro H'. rewrite H in H'. discriminate H'.
  - intro H. destruct (x =? y) eqn:E.
    + rewrite eqb_eq in E. rewrite E in H. unfold not in H.
      exfalso. apply H. reflexivity.
    + reflexivity.
Qed.

Fixpoint eqb_list {A : Type} (eqb : A -> A -> bool) (l1 l2 : list A)
  : bool :=
  match l1, l2 with
  | [], [] => true
  | [], _ => false
  | _ , [] => false
  | h1 :: t1, h2 :: t2 => if eqb h1 h2 then eqb_list eqb t1 t2 else false
  end.

Lemma eqb_list_true_iff :
  forall A (eqb : A -> A -> bool),
    (forall a1 a2, eqb a1 a2 = true <-> a1 = a2) ->
    forall l1 l2, eqb_list eqb l1 l2 = true <-> l1 = l2.
Proof.
  intros A eqb H l1. induction l1 as [| h1 t1 IHt1].
  - intro l2. split.
    + intro H'. destruct l2 eqn:E.
      * reflexivity.
      * simpl in H'. discriminate H'.
    + intro H'. rewrite <- H'. reflexivity.
  - intro l2. split.
    + intro H'. destruct l2 as [| h2 t2] eqn:E.
      * simpl in H'. discriminate H'.
      * simpl in H'. destruct (eqb h1 h2) eqn:E'.
        rewrite H in E'. rewrite IHt1 in H'.
        rewrite E'. rewrite H'. reflexivity.
        discriminate H'.
    + intro H'. destruct l2 as [| h2 t2] eqn:E.
      * discriminate H'.
      * simpl. injection H'. intros. rewrite <- H in H1.
        rewrite H1. apply IHt1. apply H0.
Qed.

Check @forallb.

Theorem forallb_true_iff : forall X test (l : list X),
    forallb test l = true <-> All (fun x => test x = true) l.
Proof.
  intros. induction l as [| h t IHt].
  - split.
    + intro H. reflexivity.
    + intro H. reflexivity.
  - split.
    + intro H. simpl in H. destruct (test h) eqn:E.
      * simpl. split. apply E. apply IHt. apply H.
      * discriminate H.
    + intro H. simpl in H. destruct H. simpl. 
      rewrite H. apply IHt. apply H0.
Qed.

(** Classical vs. Constructive Logic *)

Definition excluded_middle := forall P : Prop, P \/ ~ P.

Theorem restricted_excluded_middle : forall P b,
    (P <-> b = true) -> P \/ ~ P.
Proof.
  intros P [] H.
  - left. rewrite H. reflexivity.
  - right. rewrite H. intros constra. discriminate constra.
Qed.

Theorem restricted_excluded_middle_eq : forall n m : nat,
    n = m \/ n <> m.
Proof.
  intros n m.
  apply (restricted_excluded_middle (n = m) (n =? m)).
  rewrite eqb_eq. reflexivity.
Qed.

Theorem excluded_middle_irrefutable : forall P : Prop,
    ~~(P \/ ~P).
Proof.
  intro P. unfold not. intro H. apply H. right.
  intro H'. apply H. left. apply H'.
Qed.

Theorem not_exists_dist :
  excluded_middle ->
  forall (X : Type) (P : X -> Prop),
    ~(exists x, ~ P x) -> (forall x, P x).
Proof.
  intros. unfold excluded_middle in H.
  unfold not in H0. destruct H with (P x).
  - apply H1.
  - unfold not in H1. exfalso. apply H0. exists x. apply H1.
Qed.

Definition peirce := forall P Q : Prop, ((P -> Q) -> P) -> P.

Definition double_negation_elimination := forall P : Prop, ~~ P -> P.

Definition de_morgan_not_and_not := forall P Q : Prop,
    ~(~P /\ ~Q) -> P \/ Q.

Definition implies_to_or := forall P Q : Prop,
    (P -> Q) -> (~P \/ Q).

Theorem excluded_middle_iff_peirce : excluded_middle <-> peirce.
Proof.
  unfold excluded_middle. unfold peirce. split.
  - intros H P Q. intro H1. destruct H with P.
    + assumption.
    + apply H1. destruct H with Q.
      * intro H3. assumption.
      * intro H3. apply H0 in H3. destruct H3.
  - intros H P. apply (H (P \/ ~P) False).
    intro H1. apply excluded_middle_irrefutable in H1.
    destruct H1.
Qed.

Theorem double_negation_elimination_valid :
  excluded_middle <-> double_negation_elimination.
Proof.
  split. 
  - (* -> *) intros E P.
    destruct (E P) as [H' | H'].
    + intro HP. apply H'.
    + intro HNP.
      unfold not in H'.
      unfold not in HNP.
      apply HNP in H'.
      inversion H'.
  - (* <- *) intros DNE EXM.
    apply DNE. apply excluded_middle_irrefutable.
Qed.

Theorem de_morgan_not_and_not_valid :
  excluded_middle <-> de_morgan_not_and_not.
Proof.
  split.
  - (* -> *) intros E P Q.
    destruct (E P) as [HP | HP].   
    + intro H. left. apply HP.
    + destruct (E Q) as [HQ | HQ].
      * intro H. right. apply HQ.
      * intro H. exfalso. apply H. split.
        { apply HP. }
        { apply HQ. }
  - (* <- *) intros D E.
    apply D.
    unfold not.
    intros [H1 H2].
    apply H2. apply H1.
Qed.

Theorem implies_to_or_valid :
  excluded_middle <-> implies_to_or.
Proof.
  split.
  - (* -> *) intros E P Q.
    destruct (E P) as [HP | HP].
    + intro H. right. apply H. apply HP.
    + intro H. left. apply HP.
  - (* <- *) intros IO E.
    rewrite -> or_comm. apply IO. intro HE. apply HE.
Qed.