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
   (* intros Gamma Gamma' t T H1 H2.
    induction H1.
    - apply T_Var. rewrite <- H. symmetry. eapply H2. apply afi_var.
    - apply T_Abs. 
    *)
    Admitted.
