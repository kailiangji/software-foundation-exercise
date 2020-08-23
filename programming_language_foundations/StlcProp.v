Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Strings.String.
Add LoadPath "/Users/jikl/demos/coq/software-foundation-exercise/logic_foundation" as LF.
From LF Require Import Maps.
From PLF Require Import Types.
From PLF Require Import Stlc.
From PLF Require Import SmallStep.

Module STLCProp.

  Import STLC.

  Lemma canonical_forms_bool : forall t,
      empty |- t ? Bool ->
      value t ->
      (t = tru) \/ (t = fls).
  Proof.
    intros t H1 Hv.
    inversion H1; subst; inversion Hv.
    - left. reflexivity.
    - right. reflexivity.
  Qed.

  Lemma canonical_forms_fun : forall t T1 T2,
      empty |- t ? (Arrow T1 T2) ->
      value t ->
      exists x u, t = abs x T1 u.
  Proof.
    intros t T1 T2 H1 Hv.
    inversion H1; subst; inversion Hv.
    eexists. eexists. reflexivity.
  Qed.

  Theorem progress : forall t T,
      empty |- t ? T ->
      value t \/ exists t', t --> t'.
  Proof.
    intros t T H.
    remember (@empty ty) as Gamma.
    induction H.
    - subst. inversion H.
    - left. apply v_abs.
    - right. destruct IHhas_type1.
      + apply HeqGamma.
      + destruct IHhas_type2.
        * apply HeqGamma.
        * subst. apply (canonical_forms_fun t1 T11 T12 H) in H1.
          destruct H1. destruct H1. subst.
          eexists. apply ST_AppAbs. apply H2.
        * subst. destruct H2.  eexists. apply ST_App2. apply H1. 
          apply H2.
      + subst. destruct H1. eexists. apply ST_App1. apply H1.
    - subst. left. apply v_tru.
    - subst. left. apply v_fls.
    - subst.
      assert (Heq1 : value t1 \/ (exists t' : tm, t1 --> t')).
      { apply IHhas_type1. reflexivity. }
      assert (Heq2 : value t2 \/ (exists t' : tm, t2 --> t')).
      { apply IHhas_type2. auto. }
      assert (Heq3 : value t3 \/ (exists t' : tm, t3 --> t')).
      { auto. }
      destruct Heq1.
      + inversion H.
        * inversion H3.
        * subst. inversion H2.
        * subst. right. eexists. apply ST_TestTru.
        * subst. right. eexists. apply ST_TestFls.
        * subst. inversion H2.
      + destruct H2. right.
        eexists. apply ST_Test. apply H2.
  Qed.

  (* Show that progress can also be proved by induction on terms
  instead of induction on typing derivations. *)
  Theorem progress' : forall t T,
      empty |- t ? T ->
      value t \/ exists t', t --> t'.
  Proof.
    intro t. induction t; intros T H.
    - inversion H. inversion H2.
    - right. inversion H. subst. apply IHt1 in H3.
      destruct H3.
      + apply IHt2 in H5. destruct H5.
        * inversion H0.
          { eexists. apply ST_AppAbs. apply H1. }
          { subst. inversion H. subst. inversion H5. }
          { subst. inversion H. subst. inversion H5. }
        * destruct H1. eexists. apply ST_App2. apply H0. apply H1.
      + destruct H0. eexists. apply ST_App1. apply H0.
    - left. apply v_abs.
    - left. apply v_tru.
    - left. apply v_fls.
    - right. inversion H; subst. inversion H4; subst.
      + inversion H0.
      + apply IHt1 in H4. destruct H4.
        * inversion H2.
        * destruct H2. eexists. apply ST_Test. apply H2.
      + eexists. apply ST_TestTru.
      + eexists. apply ST_TestFls.
      + apply IHt1 in H4. destruct H4.
        * inversion H3.
        * destruct H3. eexists. apply ST_Test. apply H3.
  Qed.

  Inductive appears_free_in : string -> tm -> Prop :=
  | afi_var : forall x,
      appears_free_in x (var x)
  | afi_app1 : forall x t1 t2,
      appears_free_in x t1 ->
      appears_free_in x (app t1 t2)
  | afi_app2 : forall x t1 t2,
      appears_free_in x t2 ->
      appears_free_in x (app t1 t2)
  | afi_abs : forall x y T11 t12,
      y <> x ->
      appears_free_in x t12 ->
      appears_free_in x (abs y T11 t12)
  | afi_test1 : forall x t1 t2 t3 ,
      appears_free_in x t1 ->
      appears_free_in x (test t1 t2 t3)
  | afi_test2 : forall x t1 t2 t3,
      appears_free_in x t2 ->
      appears_free_in x (test t1 t2 t3)
  | afi_test3 : forall x t1 t2 t3,
      appears_free_in x t3 ->
      appears_free_in x (test t1 t2 t3).
  
  Hint Constructors appears_free_in : db.

  Definition closed (t : tm) :=
    forall x, ~ appears_free_in x t.

  Lemma free_in_context : forall x t T Gamma,
      appears_free_in x t ->
      Gamma |- t ? T ->
      exists T', Gamma x = Some T'.
  Proof.
    intros x t T Gamma Hafi.
    generalize dependent Gamma. generalize dependent T.
    induction Hafi.
    - intros T Gamma H. inversion H; subst. eapply ex_intro. apply H2.
    - intros T Gamma H. inversion H; subst.
      eapply IHHafi. apply H3.
    - intros T Gamma H. inversion H; subst. eapply IHHafi. apply H5.
    - intros T Gamma H1. inversion H1; subst.
      apply (IHHafi T12 (y0 |-> T11; Gamma)) in H6.
      destruct H6. rewrite update_neq in H0.
      + eexists. apply H0.
      + apply H.
    - intros T Gamma H. inversion H; subst.
      eapply IHHafi. apply H4.
    - intros T Gamma H. inversion H; subst.
      eapply IHHafi. apply H6.
    - intros T Gamma H. inversion H; subst.
      eapply IHHafi. apply H7.
  Qed.

  Corollary typable_empty__closed : forall t T,
      empty |- t ? T ->
      closed t.
  Proof.
    unfold closed. intros t T H x0 H1.
    apply (free_in_context x0 t T empty H1) in H.
    inversion H. inversion H0.
  Qed.

  Lemma context_invariance : forall Gamma Gamma' t T,
      Gamma |- t ? T ->
      (forall x, appears_free_in x t -> Gamma x = Gamma' x) ->
      Gamma' |- t ? T.
  Proof.
    intros Gamma Gamma' t T H1 H2.
    generalize dependent Gamma'.
    induction H1; intros Gamma' H2.
    - apply T_Var. rewrite <- H. symmetry.
      eapply H2. apply afi_var.
    - apply T_Abs. apply IHhas_type.
      intros x1 Hafi. destruct (string_dec x0 x1).
      + rewrite e. rewrite update_eq. rewrite update_eq.
        reflexivity.
      + rewrite update_neq.
        * rewrite update_neq.
          { apply H2. apply afi_abs. apply n. apply Hafi. }
          { apply n. }
        * apply n.
    - eapply T_App.
      + apply IHhas_type1. intros x0 H3.
        apply H2. apply afi_app1. apply H3.
      + apply IHhas_type2. intros x0 H3.
        apply H2. apply afi_app2. apply H3.
    - apply T_Tru.
    - apply T_Fls.
    - apply T_Test.
      + apply IHhas_type1. intros x0 H3.
        apply H2. apply afi_test1. apply H3.
      + apply IHhas_type2. intros x0 H3.
        apply H2. apply afi_test2. apply H3.
      + apply IHhas_type3. intros x0 H3.
        apply H2. apply afi_test3. apply H3.
  Qed.

  Lemma substitution_preserves_typing : forall Gamma x U t v T,
      (x |-> U; Gamma) |- t ? T ->
      empty |- v ? U ->
      Gamma |- [x:=v]t ? T.
  Proof with eauto.
    intros Gamma x U t v T Ht Ht'.
    generalize dependent Gamma. generalize dependent T.
    induction t; intros T Gamma H; inversion H; subst; simpl...
    - rename s into y. destruct (eqb_stringP x y) as [Hxy|Hxy].
      + subst. rewrite update_eq in H2. inversion H2; subst.
        eapply context_invariance. eassumption.
        apply typable_empty__closed in Ht'. unfold closed in Ht'.
        intros. apply (Ht' x0) in H0. inversion H0.
      + apply T_Var. rewrite update_neq in H2...
    - eapply T_App.
      + apply IHt1. apply H3.
      + apply IHt2. apply H5.
    - rename s into y. rename t into T. apply T_Abs.
      destruct (eqb_stringP x y) as [Hxy | Hxy].
      + subst. rewrite update_shadow in H5. apply H5.
      + apply IHt. eapply context_invariance...
        intros z Hafi.
        destruct (string_dec y z).
        * subst. rewrite update_eq.
          destruct (string_dec x z).
          { subst. rewrite update_eq. exfalso.
            apply Hxy. reflexivity. }
          { rewrite update_neq. rewrite update_eq.
            reflexivity. apply n. 
          }
        * rewrite update_neq. destruct (string_dec x z).
          { subst. rewrite update_eq. rewrite update_eq. reflexivity. }
          { rewrite update_neq. rewrite update_neq. rewrite update_neq.
            reflexivity. apply n. apply n0. apply n0.
          }
          { apply n. }
    - apply T_Tru.
    - apply T_Fls.
    - apply T_Test.
      + apply IHt1. apply H4.
      + apply IHt2. apply H6.
      + apply IHt3. apply H7.
  Qed.

  Theorem preservation : forall t t' T,
      empty |- t ? T ->
      t --> t' ->
      empty |- t' ? T.
  Proof with eauto.
    remember (@empty ty) as Gamma.
    intros t t' T HT. generalize dependent t'.
    induction HT; intros t' HE.
    - subst Gamma. subst. solve [inversion HE; subst; auto].
    - subst Gamma. subst. solve [inversion HE; subst; auto].
    - subst. inversion HE; subst...
      + apply substitution_preserves_typing with T11...
        inversion HT1...
      + eapply T_App.
        * apply IHHT1. reflexivity. apply H2.
        * apply HT2.
      + eapply T_App.
        * apply HT1.
        * apply IHHT2. reflexivity. apply H3.
    - inversion HE.
    - inversion HE.
    - inversion HE; subst.
      + apply HT2.
      + apply HT3.
      + apply T_Test.
        * apply IHHT1. reflexivity. apply H3.
        * apply HT2.
        * apply HT3.
  Qed.

  Definition stuck (t : tm) : Prop :=
    (normal_form step) t /\ ~ value t.

  Corollary soundness : forall t t' T,
      empty |- t ? T ->
      t -->* t' ->
      ~ (stuck t').
  Proof.
    intros t t' T Hhas_type Hmulti. unfold stuck.
    intros [Hnf Hnot_val]. unfold normal_form in Hnf.
    induction Hmulti.
    - inversion Hhas_type; subst.
      + inversion H.
      + apply Hnot_val. apply v_abs.
      + apply progress in Hhas_type. destruct Hhas_type; contradiction.
      + apply Hnot_val. apply v_tru.
      + apply Hnot_val. apply v_fls.
      + apply progress in Hhas_type. destruct Hhas_type; contradiction.
    - inversion Hhas_type; subst.
      + inversion H0.
      + apply IHHmulti.
        * eapply preservation.
          apply Hhas_type.
          apply H.
        * apply Hnf.
        * apply Hnot_val.
      + apply IHHmulti.
        * eapply preservation.
          apply Hhas_type.
          apply H.
        * apply Hnf.
        * apply Hnot_val.
      + inversion H.
      + inversion H.
      + apply IHHmulti.
        * eapply preservation.
          apply Hhas_type.
          apply H.
        * apply Hnf.
        * apply Hnot_val.
  Qed.

  Theorem unique_types : forall Gamma e T T',
      Gamma |- e ? T ->
      Gamma |- e ? T' ->
      T = T'.
  Proof.
    intros Gamma e T T' HT HT'.
    generalize dependent T'.
    induction HT; intros T' HT'; inversion HT'; subst.
    - rewrite H in H2. inversion H2. reflexivity.
    - apply IHHT in H4. subst. reflexivity.
    - apply IHHT1 in H2.
      apply IHHT2 in H4. subst. inversion H2. reflexivity.
    - reflexivity.
    - reflexivity.
    - apply IHHT3 in H6. apply H6.
  Qed.

  End STLCProp.
