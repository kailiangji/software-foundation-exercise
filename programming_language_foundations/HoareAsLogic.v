Set Warnings "-notation-overridden,-parsing".
Add LoadPath "/Users/jikl/demos/coq/software-foundation-exercise/logic_foundation" as LF.
From LF Require Import Imp.
From PLF Require Import Hoare.

Inductive hoare_proof : Assertion -> com -> Assertion -> Type :=
| H_Skip : forall P, hoare_proof P (SKIP) P
| H_Asgn : forall Q V a,
    hoare_proof (Q[V |-> a]) (V ::= a) Q
| H_Seq : forall P c Q d R,
    hoare_proof P c Q -> hoare_proof Q d R -> hoare_proof P (c ;; d) R
| H_If : forall P Q b c1 c2,
    hoare_proof (fun st => P st /\ bassn b st) c1 Q ->
    hoare_proof (fun st => P st /\ ~(bassn b st)) c2 Q ->
    hoare_proof P (TEST b THEN c1 ELSE c2 FI) Q
| H_While : forall P b c,
    hoare_proof (fun st => P st /\ bassn b st) c P ->
    hoare_proof P (WHILE b DO c END) (fun st => P st /\ ~(bassn b st))
| H_Consequence : forall (P Q P' Q' : Assertion) c,
    hoare_proof P' c Q' ->
    (forall st, P st -> P' st) ->
    (forall st, Q' st -> Q st) ->
    hoare_proof P c Q.

Lemma H_Consequence_pre : forall (P Q P' : Assertion) c,
    hoare_proof P' c Q ->
    (forall st, P st -> P' st) ->
    hoare_proof P c Q.
Proof.
  intros P Q P' c H1 H2.
  eapply H_Consequence.
  - apply H1.
  - auto.
  - auto.
Qed.

Lemma H_Consequence_post : forall (P Q Q' : Assertion) c,
    hoare_proof P c Q' ->
    (forall st, Q' st -> Q st) ->
    hoare_proof P c Q.
Proof.
  intros.
  eapply H_Consequence.
  - apply X.
  - auto.
  - apply H.
Qed.

Example sample_proof :
  hoare_proof
    ((fun st:state => st X = 3) [X |-> X + 2] [X |-> X + 1])
    (X ::= X + 1;;X ::= X + 2)
    (fun st:state => st X = 3).
Proof.
  eapply H_Seq.
  - apply H_Asgn.
  - apply H_Asgn.
Qed.

(* Print sample_proof. *)

Theorem hoare_proof_sound : forall P c Q,
    hoare_proof P c Q -> {{P}} c {{Q}}.
Proof.
  intros P c Q H.
  induction H.
  - apply hoare_skip.
  - apply hoare_asgn.
  - eapply hoare_seq.
    + apply IHhoare_proof2.
    + apply IHhoare_proof1.
  - eapply hoare_if.
    + apply IHhoare_proof1.
    + apply IHhoare_proof2.
  - apply hoare_while. apply IHhoare_proof.
  - unfold hoare_triple.
    intros st st' Ht Hp.
    apply q.
    apply p in Hp.
    unfold hoare_triple in IHhoare_proof.
    eapply IHhoare_proof.
    apply Ht.
    apply Hp.
Qed.

Theorem H_Post_True_deriv :
  forall c P, hoare_proof P c (fun _ => True).
Proof.
  intro c.
  induction c; intro P.
  - eapply H_Consequence.
    + eapply H_Skip.
    + intros st H. apply H.
    + intros. apply I.
  - eapply H_Consequence_pre.
    + eapply H_Asgn.
    + intros st H. unfold assn_sub. apply I.
  - eapply H_Consequence_pre.
    + eapply H_Seq.
      * apply IHc1.
      * apply IHc2.
    + intros st H. apply H.
  - apply H_If. 
    + apply IHc1.
    + apply IHc2.
  - eapply H_Consequence.
    + apply H_While. apply IHc.
    + intros st H. apply I.
    + intros. apply I.
Qed.

Lemma False_and_P_imp : forall P Q,
    False /\ P -> Q.
Proof. intros P Q [H1 H2]. inversion H1. Qed.

Tactic Notation "pre_false_helper" constr(CONSTR) :=
  eapply H_Consequence_pre;
  [eapply CONSTR | intros ? CONSTRA; destruct CONSTRA].

Theorem H_Pre_False_deriv :
  forall c Q, hoare_proof (fun _ => False) c Q.
Proof.
  intros c.
  induction c; intro Q.
  - pre_false_helper H_Skip.
  - pre_false_helper H_Asgn.
  - pre_false_helper H_Seq. apply IHc1. apply IHc2.
  - apply H_If.
    + eapply H_Consequence_pre. apply IHc1. simpl.
      intro st. apply False_and_P_imp.
    + eapply H_Consequence_pre. apply IHc2. simpl.
      intro st. apply False_and_P_imp.
  - eapply H_Consequence_post.
    + apply H_While.
      eapply H_Consequence_pre.
      * apply IHc.
      * simpl. intro st. apply False_and_P_imp.
    + simpl. intro st. apply False_and_P_imp.
Qed.

Definition wp (c : com) (Q : Assertion) : Assertion :=
  fun s => forall s', s =[ c ]=> s' -> Q s'.

Lemma wp_is_precondition : forall c Q,
    {{wp c Q}} c {{Q}}.
Proof.
  intros c Q. unfold hoare_triple.
  unfold wp.
  intros. apply H0. apply H.
Qed.

Lemma wp_is_weakest : forall c Q P',
    {{P'}} c {{Q}} -> forall st, P' st -> wp c Q st.
Proof.
  intros. unfold hoare_triple in H.
  unfold wp.
  intros s' H1.
  apply H in H1. apply H1. apply H0.
Qed.

Lemma wp_invariant : forall b c Inv Q,
    Inv = wp (WHILE b DO c END) Q ->
    {{ fun st => Inv st /\ bassn b st }} c {{ Inv }}.
Proof.
  intros.
  rewrite H.
  unfold hoare_triple.
  intros st st' Ht [Hwp Hb].
  unfold wp in *.
  intros s' Hwhile.
  apply Hwp.
  eapply E_WhileTrue.
  - unfold bassn in Hb. apply Hb.
  - apply Ht.
  - apply Hwhile.
Qed.

Lemma bassn_eval_false : forall b st, ~ bassn b st -> beval st b = false.
Proof.
  intros b st H.
  unfold bassn in *.
  destruct (beval st b).
  - exfalso. apply H. reflexivity.
  - reflexivity.
Qed.

Theorem hoare_proof_complete : forall P c Q,
    {{P}} c {{Q}} -> hoare_proof P c Q.
Proof.
  intros P c.
  generalize dependent P.
  induction c; intros P Q HT.
  - eapply H_Consequence_pre.
    + apply H_Skip.
    + intros st HP.
      unfold hoare_triple in HT.
      eapply HT.
      * apply E_Skip.
      * apply HP.
  - eapply H_Consequence_pre.
    + apply H_Asgn.
    + unfold hoare_triple in HT.
      intros st HP.
      eapply HT.
      * apply E_Ass. reflexivity.
      * apply HP.
  - apply H_Seq with (wp c2 Q).
    + eapply IHc1. unfold hoare_triple.
      intros st st' E1 H. unfold wp.
      intros st'' E2.
      eapply HT.
      * eapply E_Seq. apply E1. apply E2.
      * apply H.
    + apply IHc2. apply wp_is_precondition.
  - apply H_If.
    + apply IHc1. unfold hoare_triple.
      intros st st' E1 [H1 H2].
      eapply HT.
      * apply E_IfTrue.
        { unfold bassn in H2. apply H2. }
        { apply E1. }
      * apply H1.
    + apply IHc2. unfold hoare_triple.
      intros st st' E2 [H1 H2].
      eapply HT.
      * apply E_IfFalse.
        { apply bassn_eval_false. apply H2. }
        { apply E2. }
      * apply H1.
  - remember (WHILE b DO c END)%imp as while eqn:Heqwhile.
    assert (Hwp : {{wp while Q}} while {{Q}}).
    { apply wp_is_precondition. }
    assert (Hwp' : forall st, P st -> wp while Q st).
    { apply wp_is_weakest. apply HT. }
    assert (Hinv :{{ fun st => (wp while Q) st /\ bassn b st }} c {{ wp while Q }}).
    { apply (wp_invariant _ _ _ Q). rewrite Heqwhile. reflexivity. }
    eapply (H_Consequence _ _ (wp while Q) (fun st => (wp while Q) st /\ ~ bassn b st)).
    + rewrite Heqwhile. apply H_While.
      apply IHc.
      rewrite Heqwhile in Hinv. apply Hinv.
    + apply Hwp'.
    + intros st [H1 H2].
      unfold wp in H1.
      apply H1.
      rewrite Heqwhile. apply E_WhileFalse.
      apply bassn_eval_false. apply H2.
Qed.