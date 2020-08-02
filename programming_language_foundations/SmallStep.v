Set Warnings "-notation-overridden,-parsing".
Add LoadPath "/Users/jikl/demos/coq/software-foundation-exercise/logic_foundation" as LF.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Nat.
From Coq Require Import omega.Omega.
From Coq Require Import Lists.List.
Import ListNotations.
From LF Require Import Maps.
From LF Require Import Imp.

Inductive tm : Type :=
| C : nat -> tm
| P : tm -> tm -> tm.

Fixpoint evalF (t : tm) : nat :=
  match t with
  | C n => n
  | P a1 a2 => evalF a1 + evalF a2
  end.

Reserved Notation " t '==>' n " (at level 50, left associativity).

Inductive eval : tm -> nat -> Prop :=
| E_Const : forall n,
    C n ==> n
| E_Plus : forall t1 t2 n1 n2,
    t1 ==> n1 ->
    t2 ==> n2 ->
    P t1 t2 ==> (n1 + n2)
where "t '==>' n " := (eval t n).

Module SimpleArith1.

  Reserved Notation "t '-->' t' " (at level 40).

  Inductive step : tm -> tm -> Prop :=
  | ST_PlusConstConst : forall n1 n2,
      P (C n1) (C n2) --> C (n1 + n2)
  | ST_Plus1 : forall t1 t1' t2,
      t1 --> t1' ->
      P t1 t2 --> P t1' t2
  | ST_Plus2 : forall n1 t2 t2',
      t2 --> t2' ->
      P (C n1) t2 --> P (C n1) t2'
  where " t '-->' t' " := (step t t').

  Example test_step_1 :
    P (P (C 0) (C 3)) (P (C 2) (C 4))
      -->
      P (C (0 + 3)) (P (C 2) (C 4)).
  Proof. apply ST_Plus1. apply ST_PlusConstConst. Qed.

  Example test_step_2 :
      P
        (C 0)
        (P
          (C 2)
          (P (C 0) (C 3)))
      -->
      P
        (C 0)
        (P
          (C 2)
          (C (0 + 3))).
  Proof.
    apply ST_Plus2. apply ST_Plus2. apply ST_PlusConstConst.
  Qed.

End SimpleArith1.

Definition relation (X : Type) := X -> X -> Prop.

Definition deterministic {X : Type} (R : relation X) :=
  forall x y1 y2 : X, R x y1 -> R x y2 -> y1 = y2.

Module SimpleArith2.
  Import SimpleArith1.

  Theorem step_deterministic :
    deterministic step.
  Proof.
    unfold deterministic.
    intros x. induction x.
    - intros y1 y2 H1 H2. inversion H1.
    - intros y1 y2 H1 H2.
      inversion H1.
      + inversion H2.
        * rewrite <- H0 in H5. inversion H5.
          rewrite <- H3 in H6. inversion H6.
          reflexivity.
        * rewrite <- H0 in H7. inversion H7.
        * rewrite <- H3 in H7. inversion H7.
      + inversion H2.
        * rewrite <- H6 in H4. inversion H4.
        * assert (Heq : t1' = t1'0).
          { apply IHx1.
            { apply H4. }
            { apply H8. }
          }
          rewrite Heq. reflexivity.
        * rewrite <- H5 in H4. inversion H4.
      + inversion H2.
        * rewrite <- H7 in H4. inversion H4.
        * rewrite <- H in H8. inversion H8.
        * rewrite <- H in H5. rewrite H5.
          assert (Heq : t2' = t2'0).
          { apply IHx2.
            { apply H4. }
            { apply H8. }
          }
          rewrite Heq. reflexivity.
  Qed.

End SimpleArith2.

Ltac solve_by_inverts n :=
  match goal with
  | H : ?T |- _ =>
    match type of T with Prop =>
      solve [
        inversion H;
        match n with S (S (?n')) => subst; solve_by_inverts (S n')
        end ]
    end end.

Ltac solve_by_invert :=
  solve_by_inverts 1.

Module SimpleArith3.
  Import SimpleArith1.

  Theorem step_deterministic_alt: deterministic step.
  Proof.
    intros x y1 y2 Hy1 Hy2.
    generalize dependent y2.
    induction Hy1; intros y2 Hy2;
      inversion Hy2; subst; try solve_by_invert.
    - reflexivity.
    - apply IHHy1 in H2. rewrite H2. reflexivity.
    - apply IHHy1 in H2. rewrite H2. reflexivity.
  Qed.

End SimpleArith3.

Inductive value : tm -> Prop :=
| v_const : forall n, value (C n).

Reserved Notation " t '-->' t' " (at level 40).

Inductive step : tm -> tm -> Prop :=
| ST_PlusConstConst : forall n1 n2,
    P (C n1) (C n2)
      --> C (n1 + n2)
| ST_Plus1 : forall t1 t1' t2,
    t1 --> t1' ->
    P t1 t2 --> P t1' t2
| ST_Plus2 : forall v1 t2 t2',
    value v1 ->
    t2 --> t2' ->
    P v1 t2 --> P v1 t2'
where " t '-->' t' " := (step t t').

Theorem step_deterministic :
  deterministic step.
Proof.
  unfold deterministic.
  intros x y1 y2 Hy1 Hy2.
  generalize dependent y2.
  induction Hy1; intros y2 Hy2; inversion Hy2;
    subst; try solve_by_invert.
  - reflexivity.
  - apply IHHy1 in H2; rewrite H2. reflexivity.
  - inversion H1. rewrite <- H in Hy1. inversion Hy1.
  - inversion H. rewrite <- H0 in H3. inversion H3.
  - apply IHHy1 in H4. rewrite H4. reflexivity.
Qed.

Theorem strong_progress : forall t,
    value t \/ (exists t', t --> t').
Proof.
  intro t. induction t.
  - left. constructor.
  - destruct IHt1.
    + destruct IHt2.
      * right. inversion H. inversion H0. eexists. constructor.
      * right. destruct H0. apply (ST_Plus2 t1 t2 x H) in H0.
        exists (P t1 x). apply H0.
    + destruct H as [t3 H].
      right. exists (P t3 t2). apply ST_Plus1. apply H.
Qed.

Definition normal_form {X : Type} (R : relation X) (t : X) : Prop :=
  ~ exists t', R t t'.

Lemma value_is_nf : forall v,
    value v -> normal_form step v.
Proof.
  intros v H. inversion H. unfold normal_form.
  unfold not. intro H1. destruct H1. inversion H1.
Qed.

Lemma nf_is_value : forall t,
    normal_form step t -> value t.
Proof.
  unfold normal_form, not.
  intros t H. destruct (strong_progress t).
  - apply H0.
  - congruence.
Qed.

Corollary nf_same_as_value : forall t,
    normal_form step t <-> value t.
Proof.
  split.
  - apply nf_is_value.
  - apply value_is_nf.
Qed.

Module Temp1.

  Inductive value : tm -> Prop :=
  | v_const : forall n, value (C n)
  | v_funny : forall t1 n2, value (P t1 (C n2)).

  Reserved Notation " t '--> t' " (at level 40).

  Inductive step : tm -> tm -> Prop :=
  | ST_PlusConstConst : forall n1 n2,
      P (C n1) (C n2) --> C (n1 + n2)
  | ST_Plus1 : forall t1 t1' t2,
      t1 --> t1' ->
      P t1 t2 --> P t1' t2
  | ST_Plus2 : forall v1 t2 t2',
      value v1 ->
      t2 --> t2' ->
      P v1 t2 --> P v1 t2'
  where " t '-->' t' " := (step t t').

  Lemma value_not_same_as_normal_form :
    exists v, value v /\ ~ normal_form step v.
  Proof.
    exists (P (C 0) (C 0)).
    split.
    - apply v_funny.
    - unfold not. intro. unfold normal_form in H.
      unfold not in H. apply H.
      exists (C (0 + 0)). constructor.
  Qed.

End Temp1.

Module Temp2.
  Inductive value : tm -> Prop :=
  | v_const : forall n, value (C n). (* Original definition *)

  Reserved Notation " t '-->' t' " (at level 40).
  Inductive step : tm -> tm -> Prop :=
  | ST_Funny : forall n, 
      C n --> P (C n) (C 0) (* <--- NEW *)
  | ST_PlusConstConst : forall n1 n2,
      P (C n1) (C n2) --> C (n1 + n2)
  | ST_Plus1 : forall t1 t1' t2,
      t1 --> t1' ->
      P t1 t2 --> P t1' t2
  | ST_Plus2 : forall v1 t2 t2',
      value v1 ->
      t2 --> t2' ->
      P v1 t2 --> P v1 t2'

  where " t '-->' t' " := (step t t').
  
  Lemma value_not_same_as_normal_form :
    exists v, value v /\ ~ normal_form step v.
  Proof.
    exists (C 0).
    split.
    - constructor.
    - unfold normal_form. unfold not.
      intro. apply H.
      exists (P (C 0) (C 0)).
      apply ST_Funny.
  Qed.

End Temp2.

Module Temp3.

  Inductive value : tm -> Prop :=
  | v_const : forall n, value (C n).

  Reserved Notation " t '-->' t' " (at level 40).

  Inductive step : tm -> tm -> Prop :=
  | ST_PlusConstConst : forall n1 n2,
      P (C n1) (C n2) --> C (n1 + n2)
  | ST_Plus1 : forall t1 t1' t2,
      t1 --> t1' ->
      P t1 t2 --> P t1' t2
  where " t '-->' t' " := (step t t').
  
(* Note that ST_Plus2 is missing. *)
Lemma value_not_same_as_normal_form :
  exists t, ~ value t /\ normal_form step t.
Proof.
  exists (P (C 0) (P (C 0) (C 0))).
  - split.
    + unfold not. intro H. inversion H.
    + unfold normal_form. intro H.
      destruct H. inversion H. inversion H3.
Qed.      

End Temp3.

Module Temp4.

  Inductive tm : Type :=
  | tru : tm
  | fls : tm
  | test : tm -> tm -> tm -> tm.

  Inductive value : tm -> Prop :=
  | v_tru : value tru
  | v_fls : value fls.

  Reserved Notation " t '-->' t' " (at level 40).

  Inductive step : tm -> tm -> Prop :=
  | ST_IfTrue : forall t1 t2,
      test tru t1 t2 --> t1
  | ST_IfFalse : forall t1 t2,
      test fls t1 t2 --> t2
  | ST_If : forall t1 t1' t2 t3,
      t1 --> t1' ->
      test t1 t2 t3 --> test t1' t2 t3
  where " t '-->' t' " := (step t t').

  Theorem strong_progress : forall t,
      value t \/ (exists t', t --> t').
  Proof.
    induction t.
    - left. constructor.
    - left. constructor.
    - destruct IHt1. inversion H.
      + right. exists t2. apply ST_IfTrue.
      + right. exists t3. apply ST_IfFalse.
      + destruct H. right. exists (test x t2 t3).
        apply ST_If. apply H.
  Qed.

  Theorem step_deterministic :
    deterministic step.
  Proof.
    unfold deterministic.
    intros x y1 y2 Hy1 Hy2.
    generalize dependent y2.
    induction Hy1; intros y2 Hy2; inversion Hy2;
      subst; try solve_by_invert.
    - reflexivity.
    - reflexivity.
    - apply IHHy1 in H3. rewrite H3. reflexivity.
  Qed.

  Module Temp5.

    Reserved Notation " t '-->' t' " (at level 40).

    Inductive step : tm -> tm -> Prop :=
    | ST_IfTrue : forall t1 t2,
        test tru t1 t2 --> t1
    | ST_IfFalse : forall t1 t2,
        test fls t1 t2 --> t2
    | ST_If : forall t1 t1' t2 t3,
        t1 --> t1' ->
        test t1 t2 t3 --> test t1' t2 t3
    | ST_ShortCircuit : forall t1 t2,
        test t1 t2 t2 --> t2
    where " t '-->' t' " := (step t t').
    
    Definition bool_step_prop4 :=
      test
        (test tru tru tru)
        fls
        fls
        -->
        fls.

    Example bool_step_prop4_holds :
      bool_step_prop4.
    Proof.
      unfold bool_step_prop4.
      apply ST_ShortCircuit.
    Qed.

    Theorem step_deterministic :
    ~ (deterministic step).
    Proof.
      unfold deterministic, not.
      intro H.
      specialize H with (test (test tru tru tru) tru tru) (test tru tru tru) tru.
      assert (Hneq : test tru tru tru <> tru).
      { intro H'. inversion H'. }
      apply Hneq.
      apply H.
      - apply ST_If. apply ST_IfTrue.
      - apply ST_ShortCircuit.
    Qed.

    Theorem strong_progress : forall t,
      value t \/ (exists t', t --> t').
  Proof.
    induction t.
    - left. constructor.
    - left. constructor.
    - destruct IHt1. inversion H.
      + right. exists t2. apply ST_IfTrue.
      + right. exists t3. apply ST_IfFalse.
      + destruct H. right. exists (test x t2 t3).
        apply ST_If. apply H.
  Qed.

  End Temp5.
End Temp4.

Inductive multi {X : Type} (R : relation X) : relation X :=
| multi_refl : forall (x : X), multi R x x
| multi_step : forall (x y z : X),
    R x y ->
    multi R y z ->
    multi R x z.

Notation " t '-->*' t' " := (multi step t t') (at level 40).

Theorem multi_R : forall (X : Type) (R : relation X) (x y : X),
    R x y -> (multi R) x y.
Proof.
  intros X R x y H. apply (multi_step R _ y).
  - apply H.
  - apply (multi_refl R).
Qed.

Theorem multi_trans :
  forall (X : Type) (R : relation X) (x y z : X),
    multi R x y ->
    multi R y z ->
    multi R x z.
Proof.
  intros.
  induction H.
  - apply H0.
  - apply (multi_step R _ y).
    + apply H.
    + apply IHmulti. apply H0.
Qed.

Lemma test_multistep_1:
      P
        (P (C 0) (C 3))
        (P (C 2) (C 4))
   -->*
   C ((0 + 3) + (2 + 4)).
Proof.
  apply (multi_step step _ (P (C (0 + 3)) (P (C 2) (C 4)))).
  - apply ST_Plus1. apply ST_PlusConstConst.
  - apply (multi_step step _ (P (C (0 + 3)) (C (2 + 4)))).
    + apply ST_Plus2.
      * constructor.
      * apply ST_PlusConstConst.
    + apply (multi_step step _ (C (0 + 3 + (2 + 4)))).
      * apply ST_PlusConstConst.
      * apply (multi_refl step).
Qed.

Lemma test_multistep_1':
      P
        (P (C 0) (C 3))
        (P (C 2) (C 4))
  -->*
      C ((0 + 3) + (2 + 4)).
Proof.
  eapply multi_step. { apply ST_Plus1. apply ST_PlusConstConst. }
  eapply multi_step. { apply ST_Plus2. apply v_const.
                       apply ST_PlusConstConst. }
  eapply multi_step. { apply ST_PlusConstConst. }
  apply multi_refl.
Qed.

Lemma test_multistep_2:
  C 3 -->* C 3.
Proof. apply (multi_refl step). Qed.

Lemma test_multistep_3:
      P (C 0) (C 3)
   -->*
      P (C 0) (C 3).
Proof. apply (multi_refl step). Qed.

Lemma test_multistep_4:
      P
        (C 0)
        (P
          (C 2)
          (P (C 0) (C 3)))
  -->*
      P
        (C 0)
        (C (2 + (0 + 3))).
Proof.
  eapply (multi_step step).
  - apply ST_Plus2.
    + apply v_const.
    + apply ST_Plus2.
      * apply v_const.
      * apply ST_PlusConstConst.
  - eapply (multi_step step).
    + apply ST_Plus2.
      * apply v_const.
      * apply ST_PlusConstConst.
    + apply (multi_refl step).
Qed.

Definition step_normal_form := normal_form step.

Definition normal_form_of (t t' : tm) :=
  (t -->* t' /\ step_normal_form t').

Theorem normal_forms_unique:
  deterministic normal_form_of.
Proof.
  unfold deterministic, normal_form_of.
  unfold step_normal_form. unfold normal_form.
  intros x y1 y2 Hy1 Hy2.
  generalize dependent y2.
  destruct Hy1 as [H1 H2].
  induction H1; intros y2 [H3 H4]; subst; try solve_by_invert.
  - inversion H3.
    + reflexivity.
    + subst. unfold not in H2. exfalso. apply H2.
      exists y. apply H.
  - inversion H3.
    + subst. exfalso. apply H4. exists y. apply H.
    + subst.
      assert (Heq : y = y0 ).
      { apply (step_deterministic x). 
        { apply H. }
        { apply H0. }
      }
      subst.
      apply IHmulti.
      * apply H2.
      * split.
        { apply H5. }
        { apply H4. }
Qed.

Definition normalizing {X : Type} (R : relation X) :=
  forall t, exists t',
      (multi R) t t' /\ normal_form R t'.

Lemma multistep_congr_1 : forall t1 t1' t2,
     t1 -->* t1' ->
     P t1 t2 -->* P t1' t2.
Proof.
  intros t1 t1' t2 H1.
  generalize dependent t2.
  induction H1; intro t2.
  - apply (multi_refl step).
  - eapply (multi_step step).
    + apply ST_Plus1. apply H.
    + apply IHmulti.
Qed.

Lemma multistep_congr_2 : forall t1 t2 t2',
     value t1 ->
     t2 -->* t2' ->
     P t1 t2 -->* P t1 t2'.
Proof.
  intros t1 t2 t2' H1 H2.
  induction H2.
  - apply (multi_refl step).
  - eapply (multi_step step).
    + eapply ST_Plus2.
      * apply H1.
      * apply H.
    + apply IHmulti.
Qed.

Theorem step_normalizing : normalizing step.
Proof.
  unfold normalizing. unfold normal_form.
  intros t.
  induction t.
  - exists (C n). split.
    + apply (multi_refl step).
    + intro. destruct H. inversion H.
  - destruct IHt1. destruct IHt2.
    destruct H.    
    assert (Hv1 : value x).
    { destruct (strong_progress x).
      + apply H2.
      + congruence.
    }
    destruct H0.
    assert (Hv2 : value x0).
    { destruct (strong_progress x0).
      + apply H3.
      + congruence.
    }
    inversion Hv1. inversion Hv2.
    exists (C (n + n0)). subst.
    split.
    + eapply (multi_trans tm step _ (P (C n) (C n0))).
      * eapply (multi_trans tm step _ (P (C n) t2)).
        { apply multistep_congr_1. apply H. }
        { apply multistep_congr_2.
          { apply Hv1. }
          { apply H0. }
        }
      * eapply (multi_step step).
        { apply ST_PlusConstConst. }
        { apply (multi_refl step). }
    + intro H3. destruct H3. inversion H3.
Qed.

(* Equivalence of Big-Step and Small-Step *)

Theorem eval__multistep : forall t n,
    t ==> n -> t -->* C n.
Proof.
  intros t. induction t.
  - intros n0 H. inversion H. apply (multi_refl step).
  - intros n H. inversion H.
    eapply (multi_trans tm step _ (P (C n1) (C n2))).
    + eapply (multi_trans tm step _ (P (C n1) t2)).
      * apply multistep_congr_1. apply IHt1. apply H2.
      * apply multistep_congr_2.
        { apply v_const. }
        { apply IHt2. apply H4. }
    + eapply (multi_step step).
      * apply ST_PlusConstConst.
      * apply (multi_refl step).
Qed.

Lemma step__eval : forall t t' n,
    t --> t' ->
    t' ==> n ->
    t ==> n.
Proof.
  intros t t' n Hs. generalize dependent n.
  induction Hs.
  - intros n H. inversion H. apply E_Plus; apply E_Const.
  - intros n H. inversion H. subst. apply E_Plus.
    + apply IHHs. apply H2.
    + apply H4.
  - intros n H1. inversion H1. subst.
    apply E_Plus.
    + apply H3.
    + apply IHHs. apply H5.
Qed.

Theorem multistep__eval : forall t t',
    normal_form_of t t' -> exists n, t' = C n /\ t ==> n.
Proof.
  unfold normal_form_of. unfold step_normal_form.
  intros t t' [H1 H2].
  apply nf_is_value in H2.
  inversion H2.
  induction H1.
  - exists n. split.
    + reflexivity.
    + rewrite <- H. apply E_Const.
  - exists n. split.
    + reflexivity.
    + eapply step__eval.
      * apply H0.
      * apply IHmulti in H2.
        destruct H2.
        destruct H2.
        inversion H2. subst.
        { apply H3. }
        { apply H. }
Qed.

Theorem evalF_eval : forall t n,
    evalF t = n <-> t ==> n.
Proof.
  intro t. induction t.
  - split.
    + intro H. simpl in H. rewrite H. apply E_Const.
    + intro H. inversion H. reflexivity.
  - split.
    + intro H. simpl in H. rewrite <- H. apply E_Plus.
      * apply IHt1. reflexivity.
      * apply IHt2. reflexivity.
    + intro H. inversion H. subst. simpl.
      apply IHt1 in H2. apply IHt2 in H4.
      subst. reflexivity.
Qed.

Module Combined.

  Inductive tm : Type :=
  | C : nat -> tm
  | P : tm -> tm -> tm
  | tru : tm
  | fls : tm
  | test : tm -> tm -> tm -> tm.

  Inductive value : tm -> Prop :=
  | v_const : forall n, value (C n)
  | v_tru : value tru
  | v_fls : value fls.
  
  Reserved Notation " t '-->' t' " (at level 40).

  Inductive step : tm -> tm -> Prop :=
  | ST_PlusConstConst : forall n1 n2,
      P (C n1) (C n2) --> C (n1 + n2)
  | ST_Plus1 : forall t1 t1' t2,
      t1 --> t1' ->
      P t1 t2 --> P t1' t2
  | ST_Plus2 : forall v1 t2 t2',
      value v1 ->
      t2 --> t2' ->
      P v1 t2 --> P v1 t2'
  | ST_IfTrue : forall t1 t2,
      test tru t1 t2 --> t1
  | ST_IfFalse : forall t1 t2,
      test fls t1 t2 --> t2
  | ST_If : forall t1 t1' t2 t3,
      t1 --> t1' ->
      test t1 t2 t3 --> test t1' t2 t3
  where " t '-->' t' " := (step t t').

  Theorem step_deterministic :
    deterministic step.
  Proof.
    unfold deterministic.
    intros x y1 y2 Hy1 Hy2.
    generalize dependent y2.
    induction Hy1; intros y2 Hy2; inversion Hy2;
      subst; try solve_by_invert.
    - reflexivity.
    - apply IHHy1 in H2. rewrite H2. reflexivity.
    - inversion H1; rewrite <- H in Hy1; inversion Hy1.
    - inversion H; rewrite <- H0 in H3; inversion H3.
    - apply IHHy1 in H4. rewrite H4. reflexivity.
    - reflexivity.
    - reflexivity.
    - apply IHHy1 in H3. rewrite H3. reflexivity.
  Qed.

  Theorem non_strong_progress : ~ (forall t,
      value t \/ (exists t', t --> t')).
  Proof.
    intro H.
    specialize H with (P (C 1) (tru)).
    destruct H.
    - inversion H.
    - destruct H. inversion H.
      + inversion H3.
      + inversion H4.
  Qed.

End Combined.

(* Small-Step Imp *)