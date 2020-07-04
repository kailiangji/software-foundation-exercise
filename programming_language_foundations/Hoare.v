Set Warnings "-notation-overridden,-parsing".
Add LoadPath "/Users/jikl/demos/coq/software-foundation-exercise/logic_foundation" as LF.
From LF Require Import Maps.
From Coq Require Import Bool.Bool.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Arith.PeanoNat. Import Nat.
From Coq Require Import omega.Omega.
From Coq Require Import Logic.FunctionalExtensionality.
From LF Require Import Imp.

Definition Assertion := state -> Prop.

Definition assert_implies (P Q : Assertion) : Prop :=
  forall st, P st -> Q st.

Declare Scope hoare_spec_scope.

Notation "P ->> Q" := (assert_implies P Q)
  (at level 80) : hoare_spec_scope.

Open Scope hoare_spec_scope.

Notation "P <<->> Q" := (P ->> Q /\ Q ->> P)
                          (at level 80) : hoare_spec_scope.

Definition hoare_triple
           (P : Assertion) (c : com) (Q : Assertion) : Prop :=
  forall st st',
    st =[ c ]=> st' -> P st -> Q st'.

Notation "{{ P }} c {{ Q }}" :=
  (hoare_triple P c Q) (at level 90, c at next level) : hoare_spec_scope.

Theorem hoare_post_true : forall (P Q : Assertion) c,
    (forall st, Q st) ->
    {{P}} c {{Q}}.
Proof.
  unfold hoare_triple. intros P Q c H st st' Hcom Hpre.
  apply H.
Qed.

Theorem hoare_pre_false : forall (P Q : Assertion) c,
    (forall st, ~ (P st)) ->
    {{P}} c {{Q}}.
Proof.
  unfold hoare_triple. intros P Q c H st st' Hcom Hpre.
  apply H in Hpre. contradiction.
Qed.

Definition assn_sub X a P : Assertion :=
  fun (st : state) => P (X !-> aeval st a ; st).

Notation "P [ X |-> a ]" := (assn_sub X a P)
  (at level 10, X at next level).

Theorem hoare_asgn : forall (Q : Assertion) X a,
    {{Q [X |-> a]}} X ::= a {{Q}}.
Proof.
  unfold hoare_triple. intros Q X a st st' Hasgn Hpre.
  inversion Hasgn. subst. apply Hpre.
Qed.

Example assn_sub_example :
  {{(fun st => st X < 5) [X |-> X + 1]}}
    X ::= X + 1
  {{fun st => st X < 5}}.
Proof. apply hoare_asgn. Qed.

Example assn_sub_ex1 :
  {{(fun st => st X <= 10) [X |-> 2 * X]}}
    X ::= 2 * X
  {{(fun st => st X <= 10)}}.
Proof. apply hoare_asgn. Qed.

Example assn_sub_ex2 :
  {{(fun st => 0 <= st X /\ st X <= 5) [X |-> 3]}}
    X ::= 3
  {{fun st => 0 <= st X /\ st X <= 5}}.
Proof. apply hoare_asgn. Qed.

Theorem hoare_asgn_fwd :
  forall m a P,
    {{fun st => P st /\ st X = m}}
      X ::= a
    {{fun st => P (X !-> m; st)
                /\ st X = aeval (X !-> m; st) a}}.
Proof.
  intros m a P.
  unfold hoare_triple.
  intros st st' H [H1 H2].
  inversion H.
  assert (Heq : (X !-> m; X !-> n; st) = (X !-> m; st)).
    { apply t_update_shadow. }
    rewrite Heq.
    assert (Heq1 : (X !-> m; st) = st).
    { apply functional_extensionality.
      intro x0. destruct (string_dec X x0).
      + rewrite <- e. rewrite t_update_eq. symmetry. apply H2.
      + rewrite t_update_neq.
        * reflexivity.
        * apply n0.
    }
  split.
  - rewrite Heq1. apply H1.
  - rewrite t_update_eq. rewrite Heq1. symmetry. apply H6.
Qed.

Theorem hoare_asgn_fwd_exists :
  forall a P,
    {{fun st => P st}}
      X ::= a
    {{fun st => exists m, P (X !-> m; st) /\
                          st X = aeval (X !-> m; st) a}}.
Proof.
  intros a P.
  unfold hoare_triple.
  intros st st' H HP.
  inversion H. subst.
  exists (st X).
  assert (Heq : (X !-> st X; X !-> aeval st a; st) = (X !-> st X; st)).
  { apply t_update_shadow. }
  rewrite Heq.
  assert (Heq1 : (X !-> st X; st) = st).
  { apply t_update_same. }
  rewrite Heq1.
  split.
  - apply HP.
  - rewrite t_update_eq. reflexivity.
Qed.

Theorem hoare_consequence_pre : forall (P P' Q : Assertion) c,
    {{P'}} c {{Q}} ->
    P ->> P' ->
    {{P}} c {{Q}}.
Proof.
  intros P P' Q c H1 H2.
  unfold hoare_triple in *.
  unfold assert_implies in H2.
  intros st st' Hc HP.
  apply H1 with st.
  - apply Hc.
  - apply H2. apply HP.
Qed.

Theorem hoare_consequence_post : forall (P Q Q' : Assertion) c,
    {{P}} c {{Q'}} ->
    Q' ->> Q ->
    {{P}} c {{Q}}.
Proof.
  intros P Q Q' c H1 H2.
  unfold hoare_triple in *.
  unfold assert_implies in H2.
  intros st st' Hc Hpre.
  apply H2. apply H1 with st.
  apply Hc. apply Hpre.
Qed.

Example hoare_asgn_example1 :
  {{fun st => True}} X ::= 1 {{fun st => st X = 1}}.
Proof.
  eapply hoare_consequence_pre.
  - apply hoare_asgn.
  - unfold assert_implies.
    intros st _.
    unfold assn_sub.
    rewrite t_update_eq. reflexivity.
Qed.

Example assn_sub_example2 :
  {{fun st => st X < 4}}
    X ::= X + 1
  {{fun st => st X < 5}}.
Proof.
  eapply hoare_consequence_pre.
  - apply hoare_asgn.
  - unfold assert_implies, assn_sub.
    intros st H.
    rewrite t_update_eq.
    simpl. omega.
Qed.

Theorem hoare_consequence : forall (P P' Q Q' : Assertion) c,
    {{P'}} c {{Q'}} ->
    P ->> P' ->
    Q' ->> Q ->
    {{P}} c {{Q}}.
Proof.
  intros P P' Q Q' c H1 H2 H3.
  eapply hoare_consequence_pre.
  - eapply hoare_consequence_post.
    + apply H1.
    + apply H3.
  - apply H2.
Qed.

Lemma silly2_fixed :
  forall (P : nat -> nat -> Prop) (Q : nat -> Prop),
    (exists y, P 42 y) ->
    (forall x y : nat, P x y -> Q x) ->
    Q 42.
Proof.
  intros P Q H1 H2.
  destruct H1.
  eapply H2. apply H.
Qed.

Lemma silly2_eassumption :
  forall (P : nat -> nat -> Prop) (Q : nat -> Prop),
    (exists y, P 42 y) ->
    (forall x y : nat, P x y -> Q x) ->
    Q 42.
Proof.
  intros P Q HP HQ. destruct HP as [y HP'].
  eapply HQ. eassumption.
Qed.

Lemma assn_sub_ex1' :
  {{fun st => st X + 1 <= 5}}
    X ::= X + 1
  {{fun st => st X <= 5}}.
Proof.
  eapply hoare_consequence_pre.
  - apply hoare_asgn.
  - unfold assert_implies, assn_sub.
    intros st H.
    rewrite t_update_eq. simpl. apply H.
Qed.

Lemma assn_sub_ex2' :
  {{fun st => 0 <= 3 /\ 3 <= 5}}
    X ::= 3
  {{fun st => 0 <= st X /\ st X <= 5}}.
Proof.
  eapply hoare_consequence_pre.
  - apply hoare_asgn.
  - unfold assert_implies, assn_sub.
    intros st H. rewrite t_update_eq.
    simpl. omega.
Qed.

Theorem hoare_skip : forall P, {{P}} SKIP {{P}}.
Proof.
  intro P. unfold hoare_triple.
  intros st st' H1 H2.
  inversion H1. subst. apply H2.
Qed.

Theorem hoare_seq : forall P Q R c1 c2,
    {{Q}} c2 {{R}} ->
    {{P}} c1 {{Q}} ->
    {{P}} c1;;c2 {{R}}.
Proof.
  intros P Q R c1 c2 H1 H2.
  unfold hoare_triple in *. intros st st1 H3 H4.
  inversion H3. subst.
  eapply H1. apply H8.
  eapply H2. apply H5.
  apply H4.
Qed.

Example hoare_asgn_example3 : forall a n,
  {{fun st => aeval st a = n}}
  X ::= a;; SKIP
  {{fun st => st X = n}}.
Proof.
  intros a n.
  eapply hoare_seq.
  - apply hoare_skip.
  - eapply hoare_consequence_pre.
    + apply hoare_asgn.
    + unfold assert_implies, assn_sub.
      intros st H. rewrite t_update_eq. apply H.
Qed.

Example hoare_asgn_example4 :
  {{fun st => True}}
    X ::= 1;; Y ::= 2
  {{fun st => st X = 1 /\ st Y = 2}}.
Proof.
  eapply hoare_seq.
  - apply hoare_asgn.
  - eapply hoare_consequence_pre.
    + apply hoare_asgn.
    + unfold assert_implies, assn_sub.
      intros st _. simpl. split.
      * rewrite t_update_neq.
        { rewrite t_update_eq. reflexivity. }
        { intro H. inversion H. }
      * rewrite t_update_eq. reflexivity.
Qed.

Definition swap_program : com :=
  X ::= X + Y;;
  Y ::= X - Y;;
  X ::= X - Y.

Theorem swap_exercise :
  {{fun st => st X <= st Y}}
    swap_program
  {{fun st => st Y <= st X}}.
Proof.
  unfold swap_program.
  eapply hoare_seq.
  - eapply hoare_seq.
    + apply hoare_asgn.
    + apply hoare_asgn.
  - eapply hoare_consequence_pre.
    + apply hoare_asgn.
    + unfold assert_implies, assn_sub.
      intros st H. rewrite t_update_eq.
      simpl. repeat rewrite t_update_eq.
      rewrite t_update_neq.
      * repeat rewrite t_update_eq.
        rewrite t_update_neq.
        rewrite t_update_neq.
        rewrite t_update_eq. omega.
        intros H1. inversion H1.
        intros H1. inversion H1.
      * intros H1. inversion H1.
Qed.

Definition bassn b : Assertion :=
  fun st => (beval st b = true).

Lemma bexp_eval_true : forall b st,
    beval st b = true -> (bassn b) st.
Proof.
  intros b st H.
  unfold bassn. apply H.
Qed.

Lemma bexp_eval_false : forall b st,
    beval st b = false -> ~((bassn b) st).
Proof.
  intros b st H.
  unfold bassn. rewrite H.
  intro Hft. inversion Hft.
Qed.

Theorem hoare_if : forall P Q b c1 c2,
    {{fun st => P st /\ bassn b st}} c1 {{Q}} ->
    {{fun st => P st /\ ~(bassn b st)}} c2 {{Q}} ->
    {{P}} TEST b THEN c1 ELSE c2 FI {{Q}}.
Proof.
  intros P Q b c1 c2 H1 H2.
  unfold hoare_triple in *.
  intros st st' Hc Hpre.
  inversion Hc.
  - subst. eapply H1.
    + apply H7.
    + split.
      * apply Hpre.
      * apply bexp_eval_true. apply H6.
  - subst. eapply H2.
    + apply H7.
    + split.
      * apply Hpre.
      * apply bexp_eval_false. apply H6.
Qed.

Example if_example :
  {{fun st => True}}
    TEST X = 0 THEN Y ::= 2 ELSE Y ::= X + 1 FI
  {{fun st => st X <= st Y}}.
Proof.
  eapply hoare_if.
  - eapply hoare_consequence_pre.
    + apply hoare_asgn.
    + unfold assert_implies, assn_sub.
      intros st [_ H].
      simpl. rewrite t_update_eq.
      rewrite t_update_neq.
      * unfold bassn in H. simpl in H.
        rewrite eqb_eq in H. rewrite H. omega.
      * intro HYX. inversion HYX.
  - eapply hoare_consequence_pre.
    + apply hoare_asgn.
    + unfold assert_implies, assn_sub.
      intros st [_ H].
      simpl. rewrite t_update_eq.
      rewrite t_update_neq.
      * omega.
      * intro HYX. inversion HYX.
Qed.

Theorem if_minus_plus :
  {{fun st => True}}
  TEST X <= Y
    THEN Z ::= Y - X
    ELSE Y ::= X + Z
  FI
  {{fun st => st Y = st X + st Z}}.
Proof.
  eapply hoare_if.
  - eapply hoare_consequence_pre.
    + apply hoare_asgn.
    + unfold assert_implies, assn_sub.
      intros st [_ H]. simpl.
      rewrite t_update_eq.
      rewrite t_update_neq.
      * rewrite t_update_neq.
        { Search plus. apply le_plus_minus.
          unfold bassn in H. simpl in H. rewrite leb_le in H.
          apply H.
        }
        { intro HZX. inversion HZX. }
      * intro HZY. inversion HZY.
  - eapply hoare_consequence_pre.
    + apply hoare_asgn.
    + unfold assert_implies, assn_sub.
      * intros st [_ H]. simpl.
        rewrite t_update_eq.
        rewrite t_update_neq.
        { rewrite t_update_neq.
          { reflexivity. }
          { intro HYZ. inversion HYZ. }
        }
        { intro HYX. inversion HYX. }
Qed.

Module If1.

  Inductive com : Type :=
  | CSkip : com
  | CAss : string -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com
  | CIf1 : bexp -> com -> com.

  Notation "'SKIP'" :=
    CSkip : imp_scope.
  Notation "c1 ;; c2" :=
    (CSeq c1 c2) (at level 80, right associativity) : imp_scope.
  Notation "X '::=' a" :=
    (CAss X a) (at level 60) : imp_scope.
  Notation "'WHILE' b 'DO' c 'END'" :=
    (CWhile b c) (at level 80, right associativity) : imp_scope.
  Notation "'TEST' e1 'THEN' e2 'ELSE' e3 'FI'" :=
    (CIf e1 e2 e3) (at level 80, right associativity) : imp_scope.
  Notation "'IF1' b 'THEN' c 'FI'" :=
    (CIf1 b c) (at level 80, right associativity) : imp_scope.

  Reserved Notation "st '=[' c ']=>' st'" (at level 40).
  
  Open Scope imp_scope.
  
  Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall st,
      st =[ SKIP ]=> st
  | E_Ass : forall st a1 n x,
      aeval st a1 = n ->
      st =[ x ::= a1 ]=> (x !-> n ; st)
  | E_Seq : forall c1 c2 st st' st'',
      st =[ c1 ]=> st' ->
      st' =[ c2 ]=> st'' ->
      st =[ c1 ;; c2 ]=> st''
  | E_IfTrue : forall st st' b c1 c2,
      beval st b = true ->
      st =[ c1 ]=> st' ->
      st =[ TEST b THEN c1 ELSE c2 FI ]=> st'
  | E_IfFalse : forall st st' b c1 c2,
      beval st b = false ->
      st =[ c2 ]=> st' ->
      st =[ TEST b THEN c1 ELSE c2 FI ]=> st'
  | E_WhileFalse : forall b st c,
      beval st b = false ->
      st =[ WHILE b DO c END ]=> st
  | E_WhileTrue : forall st st' st'' b c,
      beval st b = true ->
      st =[ c ]=> st' ->
      st' =[ WHILE b DO c END ]=> st'' ->
      st =[ WHILE b DO c END ]=> st''
  | E_If1True : forall st st' b c,
      beval st b = true ->
      st =[ c ]=> st' ->
      st =[ IF1 b THEN c FI ]=> st'
  | E_If1False : forall st b c,
      beval st b = false ->
      st =[ IF1 b THEN c FI ]=> st

  where "st '=[' c ']=>' st'" := (ceval c st st').

  Close Scope imp_scope.

  Definition hoare_triple
             (P : Assertion) (c : com) (Q : Assertion) : Prop :=
    forall st st',
      st =[ c ]=> st' ->
      P st ->
      Q st'.

  Notation "{{ P }} c {{ Q }}" := (hoare_triple P c Q)
                                    (at level 90, c at next level) : hoare_spec_scope.

  Open Scope imp_scope.
  Theorem hoare_if1 : forall P Q b c,
      {{fun st => P st /\ bassn b st}} c {{Q}} ->
      {{fun st => P st /\ ~(bassn b st)}} SKIP {{Q}} ->
      {{P}} IF1 b THEN c FI {{Q}}.
  Proof.
    intros P Q b c H1 H2.
    unfold hoare_triple in *.
    intros st st' Hif Hpre.
    inversion Hif.
    - subst. eapply H1.
      + apply H6.
      + split.
        * apply Hpre.
        * apply bexp_eval_true. apply H3.
    - subst. eapply H2.
      + apply E_Skip.
      + split.
        * apply Hpre.
        * apply bexp_eval_false. apply H5.
  Qed.
  Close Scope imp_scope.

  Theorem hoare_post_true : forall (P Q : Assertion) c,
      (forall st, Q st) ->
      {{P}} c {{Q}}.
  Proof.
    unfold hoare_triple. intros P Q c H st st' Hcom Hpre.
    apply H.
  Qed.
  
  Theorem hoare_pre_false : forall (P Q : Assertion) c,
      (forall st, ~ (P st)) ->
      {{P}} c {{Q}}.
  Proof.
    unfold hoare_triple. intros P Q c H st st' Hcom Hpre.
    apply H in Hpre. contradiction.
  Qed.
  
  Definition assn_sub X a P : Assertion :=
    fun (st : state) => P (X !-> aeval st a ; st).
  
  Notation "P [ X |-> a ]" := (assn_sub X a P)
                                (at level 10, X at next level).
  
  Theorem hoare_asgn : forall (Q : Assertion) X a,
      {{Q [X |-> a]}} (X ::= a)%imp {{Q}}.
  Proof.
    unfold hoare_triple. intros Q X a st st' Hasgn Hpre.
    inversion Hasgn. subst. apply Hpre.
  Qed.

  Theorem hoare_consequence_pre : forall (P P' Q : Assertion) c,
      {{P'}} c {{Q}} ->
      P ->> P' ->
      {{P}} c {{Q}}.
  Proof.
    intros P P' Q c H1 H2.
    unfold hoare_triple in *.
    unfold assert_implies in H2.
    intros st st' Hc HP.
    apply H1 with st.
    - apply Hc.
    - apply H2. apply HP.
  Qed.

  Theorem hoare_skip : forall P, {{P}} SKIP%imp {{P}}.
  Proof.
    intro P. unfold hoare_triple.
    intros st st' H1 H2.
    inversion H1. subst. apply H2.
  Qed.
  
  Lemma hoare_if1_good :
    {{fun st => st X + st Y = st Z}}
      (IF1 ~(Y = 0) THEN
        X ::= X + Y
      FI)%imp
    {{fun st => st X = st Z}}.
  Proof.
    eapply hoare_if1.
    - eapply hoare_consequence_pre.
      + apply hoare_asgn.
      + unfold assert_implies, assn_sub.
        intros st [H1 H2].
        simpl. rewrite t_update_eq.
        rewrite t_update_neq.
        * apply H1.
        * intro HXZ. inversion HXZ.
    - eapply hoare_consequence_pre.
      + apply hoare_skip.
      + unfold assert_implies.
        intros st [H1 H2].
        unfold bassn in H2. simpl in H2.
        Search negb. apply eq_true_negb_classical in H2.
        rewrite eqb_eq in H2. rewrite H2 in H1.
        Search plus. rewrite add_0_r in H1.
        apply H1.
  Qed.

End If1.

Theorem hoare_while : forall P b c,
    {{fun st => P st /\ bassn b st}} c {{P}} ->
    {{P}} WHILE b DO c END {{fun st => P st /\ ~ (bassn b st)}}.
Proof.
  intros P b c H.
  remember (WHILE b DO c END)%imp as while eqn:Heqwhile.
  unfold hoare_triple in *.
  intros st st' Hwc Hpre.
  induction Hwc; try inversion Heqwhile.
  - subst. split.
    + apply Hpre.
    + apply bexp_eval_false. apply H0.
  - subst. apply IHHwc2.
    + reflexivity.
    + eapply H.
      * eassumption.
      * split.
        { apply Hpre. }
        { apply bexp_eval_true. apply H0. }
Qed.

Example while_example :
  {{fun st => st X <= 3}}
    WHILE X <= 2 DO
      X ::= X + 1
    END
  {{fun st => st X = 3}}.
Proof.
  eapply hoare_consequence_post.
  - eapply hoare_consequence_pre.
    + apply hoare_while.
      eapply (hoare_consequence_pre _ _ (fun st => st X <= 3)).
      * apply hoare_asgn.
      * unfold assert_implies, assn_sub.
        intros st [H1 H2]. simpl.
        rewrite t_update_eq. unfold bassn in H2.
        simpl in H2. rewrite leb_le in H2. omega.
    + unfold assert_implies. auto.
  - simpl. unfold assert_implies.
    intros st [H1 H2]. unfold bassn in H2.
    simpl in H2. unfold not in H2. rewrite leb_le in H2. omega.
Qed.

Theorem always_loop_hoare : forall P Q,
    {{P}} WHILE true DO SKIP END {{Q}}.
Proof.
  intros P Q.
  eapply hoare_consequence_post.
  - eapply hoare_consequence_pre.
    + apply hoare_while. eapply hoare_consequence_pre.
      * apply hoare_skip.
      * unfold assert_implies. intros st [H1 H2]. assumption.
    + unfold assert_implies. intros st H. eassumption.
  - unfold assert_implies. intros st [H1 H2].
    unfold bassn in H2. simpl in H2. unfold not in H2.
    exfalso. apply H2. reflexivity.
Qed.

Module RepeatExercise.

  Inductive com : Type :=
  | CSkip : com
  | CAsgn : string -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com
  | CRepeat : com -> bexp -> com.

  Notation "'SKIP'" :=
    CSkip.
  Notation "c1 ;; c2" :=
    (CSeq c1 c2) (at level 80, right associativity).
  Notation "X '::=' a" :=
    (CAsgn X a) (at level 60).
  Notation "'WHILE' b 'DO' c 'END'" :=
    (CWhile b c) (at level 80, right associativity).
  Notation "'TEST' e1 'THEN' e2 'ELSE' e3 'FI'" :=
    (CIf e1 e2 e3) (at level 80, right associativity).
  Notation "'REPEAT' e1 'UNTIL' b2 'END'" :=
    (CRepeat e1 b2) (at level 80, right associativity).

  Reserved Notation "st '=[' c ']=>' st'" (at level 40).
  Inductive ceval : state -> com -> state -> Prop :=
  | E_Skip : forall st,
      st =[ SKIP ]=> st
  | E_Ass : forall st a1 n x,
      aeval st a1 = n ->
      st =[ x ::= a1 ]=> (x !-> n ; st)
  | E_Seq : forall c1 c2 st st' st'',
      st =[ c1 ]=> st' ->
      st' =[ c2 ]=> st'' ->
      st =[ c1 ;; c2 ]=> st''
  | E_IfTrue : forall st st' b c1 c2,
      beval st b = true ->
      st =[ c1 ]=> st' ->
      st =[ TEST b THEN c1 ELSE c2 FI ]=> st'
  | E_IfFalse : forall st st' b c1 c2,
      beval st b = false ->
      st =[ c2 ]=> st' ->
      st =[ TEST b THEN c1 ELSE c2 FI ]=> st'
  | E_WhileFalse : forall b st c,
      beval st b = false ->
      st =[ WHILE b DO c END ]=> st
  | E_WhileTrue : forall st st' st'' b c,
      beval st b = true ->
      st =[ c ]=> st' ->
      st' =[ WHILE b DO c END ]=> st'' ->
      st =[ WHILE b DO c END ]=> st''
  | E_RepeatTrue : forall b st st' c,
      st =[ c ]=> st' ->
      beval st' b = true ->
      st =[ REPEAT c UNTIL b END ]=> st'
  | E_RepeatFalse : forall st st' st'' b c,
      st =[ c ]=> st' ->
      beval st' b = false ->
      st' =[ REPEAT c UNTIL b END]=> st'' ->
      st =[ REPEAT c UNTIL b END]=> st''
      
  where "st '=[' c ']=>' st'" := (ceval st c st').

  Definition hoare_triple (P : Assertion) (c : com) (Q : Assertion)
    : Prop :=
    forall st st', st =[ c ]=> st' -> P st -> Q st'.
  
  Notation "{{ P }} c {{ Q }}" :=
    (hoare_triple P c Q) (at level 90, c at next level).

  Definition ex1_repeat :=
  REPEAT
    X ::= 1;;
    Y ::= Y + 1
  UNTIL X = 1 END.
  
  Theorem ex1_repeat_works :
    empty_st =[ ex1_repeat ]=> (Y !-> 1 ; X !-> 1).
  Proof.
    unfold ex1_repeat.
    apply E_RepeatTrue.
    - eapply E_Seq.
      + apply E_Ass. reflexivity.
      + simpl. apply E_Ass. simpl. reflexivity.
    - reflexivity.
  Qed.

  Theorem hoare_asgn : forall (Q : Assertion) X a,
    {{Q [X |-> a]}} X ::= a {{Q}}.
  Proof.
    unfold hoare_triple. intros Q X a st st' Hasgn Hpre.
    inversion Hasgn. subst. apply Hpre.
  Qed.

  Theorem hoare_consequence_pre : forall (P P' Q : Assertion) c,
    {{P'}} c {{Q}} ->
    P ->> P' ->
    {{P}} c {{Q}}.
  Proof.
    intros P P' Q c H1 H2.
    unfold hoare_triple in *.
    unfold assert_implies in H2.
    intros st st' Hc HP.
    apply H1 with st.
    - apply Hc.
    - apply H2. apply HP.
  Qed.

  Theorem hoare_consequence_post : forall (P Q Q' : Assertion) c,
    {{P}} c {{Q'}} ->
    Q' ->> Q ->
    {{P}} c {{Q}}.
  Proof.
    intros P Q Q' c H1 H2.
    unfold hoare_triple in *.
    unfold assert_implies in H2.
    intros st st' Hc Hpre.
    apply H2. apply H1 with st.
    apply Hc. apply Hpre.
  Qed.

  Theorem hoare_consequence : forall (P P' Q Q' : Assertion) c,
    {{P'}} c {{Q'}} ->
    P ->> P' ->
    Q' ->> Q ->
    {{P}} c {{Q}}.
  Proof.
    intros P P' Q Q' c H1 H2 H3.
    eapply hoare_consequence_pre.
    - eapply hoare_consequence_post.
      + apply H1.
      + apply H3.
    - apply H2.
  Qed.
  
  Theorem hoare_skip : forall P, {{P}} SKIP {{P}}.
  Proof.
    intro P. unfold hoare_triple.
    intros st st' H1 H2.
    inversion H1. subst. apply H2.
  Qed.
  
  Theorem hoare_seq : forall P Q R c1 c2,
      {{Q}} c2 {{R}} ->
      {{P}} c1 {{Q}} ->
      {{P}} c1;;c2 {{R}}.
  Proof.
    intros P Q R c1 c2 H1 H2.
    unfold hoare_triple in *. intros st st1 H3 H4.
    inversion H3. subst.
    eapply H1. apply H8.
    eapply H2. apply H6.
    apply H4.
  Qed.

  Theorem hoare_while : forall P b c,
    {{fun st => P st /\ bassn b st}} c {{P}} ->
    {{P}} WHILE b DO c END {{fun st => P st /\ ~ (bassn b st)}}.
  Proof.
    intros P b c H.
    remember (WHILE b DO c END) as while eqn:Heqwhile.
    unfold hoare_triple in *.
    intros st st' Hwc Hpre.
    induction Hwc; try inversion Heqwhile.
    - subst. split.
      + apply Hpre.
      + apply bexp_eval_false. apply H0.
    - subst. apply IHHwc2.
      + reflexivity.
      + eapply H.
        * eassumption.
        * split.
          { apply Hpre. }
          { apply bexp_eval_true. apply H0. }
  Qed.
  
  Theorem hoare_repeat : forall P Q b c,
      {{P}} c {{Q}} ->
      {{fun st => Q st /\ ~(bassn b st)}} c {{Q}} ->
      {{P}} REPEAT c UNTIL b END {{fun st => Q st /\ bassn b st}}.
  Proof.
    intros P Q b c H1 H2.
    remember (REPEAT c UNTIL b END) as rep eqn:Heqrep.
    unfold hoare_triple in *. intros st st' H3 Hpre.
    inversion H3.
    - subst. inversion H0.
    - subst. inversion H4.
    - subst. inversion H5.
    - subst. inversion H5.
    - subst. inversion H5.
    - subst. inversion H4.
    - subst. inversion H6.
    - subst. inversion H5.
      subst. split.
      + apply H1 with st; assumption.
      + apply bexp_eval_true. apply H0.
    - subst. inversion H6. subst.
      assert (Hpre' : Q st'0).
      { apply H1 with st; assumption. }
      remember (REPEAT c UNTIL b END) as rep eqn:Heqrep.
      clear H. clear H6.
      induction H4; try inversion Heqrep.
      + subst. split.
        * apply H2 with st0.
          { assumption. }
          { split.
            { assumption. }
            { apply bexp_eval_false. apply H0. }
          }
        * apply bexp_eval_true. apply H.
      + subst. apply IHceval2.
        * reflexivity.
        * apply H3.
        * apply H.
        * apply H2 with st0.
          { apply H4_. }
          { split.
            { apply Hpre'. }
            { apply bexp_eval_false. apply H0. }
          }
  Qed.

  Example test_hoare_repeat:
    {{fun st => st X > 0}}
      REPEAT
        Y ::= X;;
        X ::= X - 1
      UNTIL X = 0 END
    {{fun st => st X = 0 /\ st Y > 0}}.
  Proof.
    eapply hoare_consequence_post. 
    apply (hoare_repeat (fun st => st X > 0) (fun st => st Y > 0)).
    - eapply hoare_seq.
      + apply hoare_asgn.
      + eapply hoare_consequence_pre.
        * apply hoare_asgn.
        * unfold assert_implies, assn_sub.
          intros st H.
          rewrite t_update_neq.
          { simpl. rewrite t_update_eq. apply H. }
          { intro HXY. inversion HXY. }
    - eapply hoare_seq.
      + apply hoare_asgn.
      + eapply hoare_consequence_pre.
        * apply hoare_asgn.
        * unfold assert_implies, assn_sub.
          intros st [H1 H2].
          simpl. rewrite t_update_neq.
          { rewrite t_update_eq. unfold bassn in H2. simpl in H2. 
            Search eqb. unfold not in H2. Search eqb. rewrite eqb_eq in H2.
            assert (H3: {st X = 0} + {st X > 0}).
            { destruct (st X).
              { left. reflexivity. }
              { right. Search gt. apply gt_Sn_O. }
            }
            destruct H3.
            { congruence. }
            { apply g. }
          }
          { intro HXY. inversion HXY. }
    - unfold assert_implies.
      intros st [H1 H2].
      split.
      + unfold bassn in H2. simpl in H2.
        rewrite eqb_eq in H2. apply H2.
      + apply H1.
  Qed.

End RepeatExercise.

Module Himp.
  Inductive com : Type :=
  | CSkip : com
  | CAsgn : string -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com
  | CHavoc : string -> com.

  Notation "'SKIP'" :=
    CSkip.
  Notation "X '::=' a" :=
    (CAsgn X a) (at level 60).
  Notation "c1 ;; c2" :=
    (CSeq c1 c2) (at level 80, right associativity).
  Notation "'WHILE' b 'DO' c 'END'" :=
    (CWhile b c) (at level 80, right associativity).
  Notation "'TEST' e1 'THEN' e2 'ELSE' e3 'FI'" :=
    (CIf e1 e2 e3) (at level 80, right associativity).
  Notation "'HAVOC' X" := (CHavoc X) (at level 60).
  Reserved Notation "st '=[' c ']=>' st'" (at level 40).
  Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall st,
      st =[ SKIP ]=> st
  | E_Ass : forall st a1 n x,
      aeval st a1 = n ->
      st =[ x ::= a1 ]=> (x !-> n ; st)
  | E_Seq : forall c1 c2 st st' st'',
      st =[ c1 ]=> st' ->
      st' =[ c2 ]=> st'' ->
      st =[ c1 ;; c2 ]=> st''
  | E_IfTrue : forall st st' b c1 c2,
      beval st b = true ->
      st =[ c1 ]=> st' ->
      st =[ TEST b THEN c1 ELSE c2 FI ]=> st'
  | E_IfFalse : forall st st' b c1 c2,
      beval st b = false ->
      st =[ c2 ]=> st' ->
      st =[ TEST b THEN c1 ELSE c2 FI ]=> st'
  | E_WhileFalse : forall b st c,
      beval st b = false ->
      st =[ WHILE b DO c END ]=> st
  | E_WhileTrue : forall st st' st'' b c,
      beval st b = true ->
      st =[ c ]=> st' ->
      st' =[ WHILE b DO c END ]=> st'' ->
      st =[ WHILE b DO c END ]=> st''
  | E_Havoc : forall st X n,
      st =[ HAVOC X ]=> (X !-> n ; st)

  where "st '=[' c ']=>' st'" := (ceval c st st').

  Definition hoare_triple (P:Assertion) (c:com) (Q:Assertion) : Prop :=
    forall st st', st =[ c ]=> st' -> P st -> Q st'.
  
  Notation "{{ P }} c {{ Q }}" := (hoare_triple P c Q)
                                    (at level 90, c at next level)
                                  : hoare_spec_scope.

  Definition havoc_pre (X : string) (Q : Assertion) : Assertion :=
    fun st => forall n, Q (X !-> n; st).

  Theorem hoare_havoc : forall (Q : Assertion) (X : string),
      {{ havoc_pre X Q}} HAVOC X {{Q}}.
  Proof.
    unfold hoare_triple. intros.
    inversion H. unfold havoc_pre in *.
    unfold assn_sub in *.
    apply H0.
  Qed.

End Himp.

Module HoareAssertAssume.

  Inductive com : Type :=
  | CSkip : com
  | CAss : string -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com
  | CAssert : bexp -> com
  | CAssume : bexp -> com.
  
  Notation "'SKIP'" :=
    CSkip.
  Notation "x '::=' a" :=
    (CAss x a) (at level 60).
  Notation "c1 ;; c2" :=
    (CSeq c1 c2) (at level 80, right associativity).
  Notation "'WHILE' b 'DO' c 'END'" :=
    (CWhile b c) (at level 80, right associativity).
  Notation "'TEST' c1 'THEN' c2 'ELSE' c3 'FI'" :=
    (CIf c1 c2 c3) (at level 80, right associativity).
  Notation "'ASSERT' b" :=
    (CAssert b) (at level 60).
  Notation "'ASSUME' b" :=
    (CAssume b) (at level 60).

  Inductive result : Type :=
  | RNormal : state -> result
  | RError : result.

  Inductive ceval : com -> state -> result -> Prop :=
  (* Old rules, several modified *)
  | E_Skip : forall st,
      st =[ SKIP ]=> RNormal st
  | E_Ass : forall st a1 n x,
      aeval st a1 = n ->
      st =[ x ::= a1 ]=> RNormal (x !-> n ; st)
  | E_SeqNormal : forall c1 c2 st st' r,
      st =[ c1 ]=> RNormal st' ->
      st' =[ c2 ]=> r ->
      st =[ c1 ;; c2 ]=> r
  | E_SeqError : forall c1 c2 st,
      st =[ c1 ]=> RError ->
      st =[ c1 ;; c2 ]=> RError
  | E_IfTrue : forall st r b c1 c2,
      beval st b = true ->
      st =[ c1 ]=> r ->
      st =[ TEST b THEN c1 ELSE c2 FI ]=> r
  | E_IfFalse : forall st r b c1 c2,
      beval st b = false ->
      st =[ c2 ]=> r ->
      st =[ TEST b THEN c1 ELSE c2 FI ]=> r
  | E_WhileFalse : forall b st c,
      beval st b = false ->
      st =[ WHILE b DO c END ]=> RNormal st
  | E_WhileTrueNormal : forall st st' r b c,
      beval st b = true ->
      st =[ c ]=> RNormal st' ->
      st' =[ WHILE b DO c END ]=> r ->
      st =[ WHILE b DO c END ]=> r
  | E_WhileTrueError : forall st b c,
      beval st b = true ->
      st =[ c ]=> RError ->
      st =[ WHILE b DO c END ]=> RError
  (* Rules for Assert and Assume *)
  | E_AssertTrue : forall st b,
      beval st b = true ->
      st =[ ASSERT b ]=> RNormal st
  | E_AssertFalse : forall st b,
      beval st b = false ->
      st =[ ASSERT b ]=> RError
  | E_Assume : forall st b,
      beval st b = true ->
      st =[ ASSUME b ]=> RNormal st

  where "st '=[' c ']=>' r" := (ceval c st r).

  Definition hoare_triple
             (P : Assertion) (c : com) (Q : Assertion) : Prop :=
    forall st r,
      st =[ c ]=> r -> P st -> (exists st', r = RNormal st' /\ Q st').

  Notation "{{ P }} c {{ Q }}" := (hoare_triple P c Q)
    (at level 90, c at next level) : hoare_spec_scope.

  Theorem assert_assume_differ : exists P b Q,
      ({{P}} ASSUME b {{Q}}) /\ ~({{P}} ASSERT b {{Q}}).
  Proof.
    unfold hoare_triple.
    exists (fun st => True).
    exists false.
    exists (fun st => False).
    split.
    - intros st r H1 _.
      inversion H1. simpl in H0. inversion H0.
    - intro H. destruct (H empty_st RError).
      + apply E_AssertFalse. reflexivity.
      + apply I.
      + destruct H0. apply H1.
  Qed.

  Theorem assert_implies_assume : forall P b Q,
      ({{P}} ASSERT b {{Q}}) ->
      ({{P}} ASSUME b {{Q}}).
  Proof.
    unfold hoare_triple.
    intros P b Q H1.
    intros st r H2 H3.
    inversion H2.
    exists st.
    split.
    - reflexivity.
    - subst. destruct (H1 st (RNormal st)).
      + apply E_AssertTrue. apply H0.
      + apply H3.
      + destruct H. inversion H. subst. apply H4.
  Qed.

  Theorem hoare_asgn : forall Q X a,
      {{Q [X |-> a]}} X ::= a {{Q}}.
  Proof.
    intros Q X a.
    unfold hoare_triple.
    intros st r Hass Hpre.
    inversion Hass. subst.
    eexists. split.
    - reflexivity.
    - unfold assn_sub in Hpre. apply Hpre.
  Qed.

  Theorem hoare_consequence_pre : forall (P P' Q : Assertion) c,
      {{P'}} c {{Q}} ->
      P ->> P' ->
      {{P}} c {{Q}}.
  Proof.
    intros P P' Q c H1 H2.
    unfold hoare_triple in *.
    intros st r H3 H4.
    inversion H3; try (subst; eapply H1; [ (apply H3) | (apply H2; apply H4)]).
  Qed.

  Theorem hoare_consequence_post : forall (P Q Q' : Assertion) c,
      {{P}} c {{Q'}} ->
      Q' ->> Q ->
      {{P}} c {{Q}}.
  Proof.
    intros P Q Q' c H1 H2.
    unfold hoare_triple in *.
    intros st r H3 H4.
    apply (H1 st r H3) in H4.
    destruct H4. destruct H.
    exists x.
    split.
    - apply H.
    - apply H2. apply H0.
  Qed.

  Theorem hoare_seq : forall P Q R c1 c2,
  {{Q}} c2 {{R}} ->
  {{P}} c1 {{Q}} ->
  {{P}} c1;;c2 {{R}}.
  Proof.
    intros.
    unfold hoare_triple in *.
    intros st r H1 H2.
    inversion H1; subst.
    - eapply H.
      + apply H8.
      + apply (H0 st (RNormal st') H5) in H2.
        destruct H2. destruct H2.
        inversion H2. apply H3.
    - apply (H0 st RError H7) in H2.
      destruct H2. destruct H2. inversion H2.
  Qed.

  Theorem hoare_assert : forall P b,
      {{fun st => P st /\ bassn b st}} ASSERT b {{ P }}.
  Proof.
    unfold hoare_triple.
    intros. inversion H.
    - subst. exists st. split.
      + reflexivity.
      + apply H0. 
    - subst. unfold bassn in H0. destruct H0. congruence.
  Qed.

  Theorem hoare_assume : forall P b,
      {{ P }} ASSUME b {{ fun st => P st /\ bassn b st}}.
  Proof.
    unfold hoare_triple.
    intros. inversion H.
    subst. exists st. split.
    - reflexivity.
    - split.
      + apply H0.
      + apply H2. 
  Qed.

  Theorem hoare_skip : forall P,
      {{P}} SKIP {{P}}.
  Proof.
    unfold hoare_triple.
    intros. inversion H. subst.
    exists st. split.
    - reflexivity.
    - apply H0.
  Qed.

  Theorem hoare_if : forall P Q b c1 c2,
      {{fun st => P st /\ bassn b st}} c1 {{Q}} ->
      {{fun st => P st /\ ~(bassn b st)}} c2 {{Q}} ->
      {{P}} TEST b THEN c1 ELSE c2 FI {{Q}}.
  Proof.
    unfold hoare_triple. intros.
    inversion H1.
    - eapply H.
      + apply H9.
      + split; assumption.
    - eapply H0.
      + apply H9.
      + split.
        * apply H2.
        * apply bexp_eval_false. apply H8.
  Qed.

  Theorem hoare_while : forall P b c,
      {{fun st => P st /\ bassn b st}} c {{P}} ->
      {{P}} WHILE b DO c END {{fun st => P st /\ ~(bassn b st)}}.
  Proof.
    intros P b c Hhoare st st' He HP.
    remember (WHILE b DO c END) as wcom eqn:Heqwcom.
    induction He;
      try (inversion Heqwcom); subst; clear Heqwcom.
    - (* E_WhileFalse *)
      eexists. split. reflexivity. split.
      assumption. apply bexp_eval_false. assumption.
    - (* E_WhileTrueNormal *)
      clear IHHe1.
      apply IHHe2. reflexivity.
      clear IHHe2 He2 r.
      unfold hoare_triple in Hhoare.
      apply Hhoare in He1.
      + destruct He1 as [st1 [Heq Hst1]].
        inversion Heq; subst.
        assumption.
      + split; assumption.
    - (* E_WhileTrueError *)
      exfalso. clear IHHe.
      unfold hoare_triple in Hhoare.
      apply Hhoare in He.
      + destruct He as [st' [C _]]. inversion C.
      + split; assumption.
  Qed.

  Example assert_assume_example:
    {{fun st => True}}
      ASSUME (X = 1);;
      X ::= X + 1;;
      ASSERT (X = 2)
    {{fun st => True}}.
  Proof.
    eapply hoare_seq.
    - eapply hoare_seq.
      + apply hoare_assert.
      + apply hoare_asgn.
    - eapply hoare_consequence_pre.
      + eapply hoare_consequence_post.
        * apply hoare_assume.
        * unfold assert_implies, assn_sub.
          intros. split.
          { apply I. }
          { unfold bassn in *. simpl. rewrite t_update_eq.
            simpl in H. destruct H. rewrite eqb_eq in H0.
            rewrite H0. simpl. reflexivity. 
          }
      + unfold assert_implies.
        intros st _. apply I.
  Qed.
End HoareAssertAssume.