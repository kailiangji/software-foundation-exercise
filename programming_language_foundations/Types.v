Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Arith.Arith.
Add LoadPath "/Users/jikl/demos/coq/software-foundation-exercise/logic_foundation" as LF.
From LF Require Import Maps.
From LF Require Import Imp.
From PLF Require Import SmallStep.

Hint Constructors multi : db.

Inductive tm : Type :=
| tru : tm
| fls : tm
| test : tm -> tm -> tm -> tm
| zro : tm
| scc : tm -> tm
| prd : tm -> tm
| iszro : tm -> tm.

Inductive bvalue : tm -> Prop :=
| bv_tru : bvalue tru
| bv_fls : bvalue fls.

Inductive nvalue : tm -> Prop :=
| nv_zro : nvalue zro
| nv_scc : forall t, nvalue t -> nvalue (scc t).

Definition value (t : tm) := bvalue t \/ nvalue t.

Hint Constructors bvalue nvalue : db.

Hint Unfold value.
Hint Unfold update.

Reserved Notation "t1 '-->' t2" (at level 40).

Inductive step : tm -> tm -> Prop :=
| ST_TestTru : forall t1 t2, (test tru t1 t2) --> t1
| ST_TestFls : forall t1 t2, (test fls t1 t2) --> t2
| ST_Test : forall t1 t1' t2 t3,
    t1 --> t1' ->
    (test t1 t2 t3) --> (test t1' t2 t3)
| ST_Scc : forall t1 t1',
    t1 --> t1' ->
    (scc t1) --> (scc t1')
| ST_PrdZro : (prd zro) --> zro
| ST_PrdScc : forall t1,
    nvalue t1 ->
    (prd (scc t1)) --> t1
| ST_Prd : forall t1 t1',
    t1 --> t1' ->
    (prd t1) --> (prd t1')
| ST_IszroZro :
    (iszro zro) --> tru
| ST_IszroScc : forall t1,
    nvalue t1 ->
    (iszro (scc t1)) --> fls
| ST_Iszro : forall t1 t1',
    t1 --> t1' ->
    (iszro t1) --> (iszro t1')
               
where "t1 '-->' t2" := (step t1 t2).

Hint Constructors step.

Notation step_normal_form := (normal_form step).

Definition stuck (t : tm) : Prop :=
  step_normal_form t /\ ~ value t.

Hint Unfold stuck.

Example some_term_is_stuck :
  exists t, stuck t.
Proof.
  exists (test zro zro zro).
  unfold stuck. split.
  - unfold step_normal_form.
    intro H. destruct H.
    inversion H. inversion H4.
  - intro H. inversion H.
    + inversion H0.
    + inversion H0.
Qed.

Lemma value_is_nf : forall t,
    value t -> step_normal_form t.
Proof.
  intros t H. inversion H.
  - inversion H0.
    + unfold step_normal_form.
      intro H2. destruct H2. inversion H2.
    + unfold step_normal_form.
      intro H2. destruct H2. inversion H2.
  - induction H0.
    + unfold step_normal_form.
      intro H1. destruct H1. inversion H0.
    + unfold step_normal_form.
      intro H1. destruct H1.
      inversion H1. subst.
      assert (Hv : value t).
      { unfold value. right. apply H0. }
      apply IHnvalue in Hv. unfold step_normal_form in Hv.
      apply Hv. eapply ex_intro. apply H3.
Qed.

Theorem step_deterministic :
  deterministic step.
Proof with eauto.
  unfold deterministic.
  intros x y1 y2 Hy1 Hy2.
  generalize dependent y2.
  induction Hy1; intros y2 Hy2;
    inversion Hy2; subst; try reflexivity.
  - inversion H3.
  - inversion H3.
  - inversion Hy1.
  - inversion Hy1.
  - apply IHHy1 in H3. rewrite H3. reflexivity.
  - apply IHHy1 in H0. rewrite H0. reflexivity.
  - inversion H0.
  - inversion H1. subst.
    assert (Hnf: step_normal_form t1).
    { apply value_is_nf. unfold value. right. apply H. }
    unfold step_normal_form in Hnf. unfold not in Hnf.
    exfalso. apply Hnf. eapply ex_intro. apply H2.
  - inversion Hy1.
  - inversion Hy1; subst.
    assert (Hnf: step_normal_form y2).
    { apply value_is_nf. unfold value. right. apply H0. }
    unfold step_normal_form in Hnf. unfold not in Hnf.
    exfalso. apply Hnf. eapply ex_intro. apply H1.
  - apply IHHy1 in H0. rewrite H0. reflexivity.
  - inversion H0.
  - inversion H1; subst.
    assert (Hnf: step_normal_form t1).
    { apply value_is_nf. unfold value. right. apply H. }
    unfold step_normal_form in Hnf. unfold not in Hnf.
    exfalso. apply Hnf. eapply ex_intro. apply H2.
  - inversion Hy1.
  - inversion Hy1; subst.
    assert (Hnf: step_normal_form t0).
    { apply value_is_nf. unfold value. right. apply H0. }
    unfold step_normal_form in Hnf. unfold not in Hnf.
    exfalso. apply Hnf. eapply ex_intro. apply H1.
  - apply IHHy1 in H0. rewrite H0. reflexivity.
Qed.

