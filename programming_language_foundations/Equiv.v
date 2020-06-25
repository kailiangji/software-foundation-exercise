Set Warnings "-notation-overridden,-parsing".
Add LoadPath "/Users/jikl/demos/coq/software-foundation-exercise/logic_foundation" as LF.
From LF Require Import Maps.
From Coq Require Import Bool.Bool.
From Coq Require Import Arith.Arith.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.PeanoNat. Import Nat.
From Coq Require Import Arith.EqNat.
From Coq Require Import omega.Omega.
From Coq Require Import Lists.List.
From Coq Require Import Logic.FunctionalExtensionality.
Import ListNotations.
From LF Require Import Imp.

Definition aequiv (a1 a2 : aexp) : Prop :=
  forall (st : state),
    aeval st a1 = aeval st a2.

Definition bequiv (b1 b2 : bexp) : Prop :=
  forall (st : state),
    beval st b1 = beval st b2.

Example aequiv_example : aequiv (X - X) 0.
Proof.
  unfold aequiv. intro st. simpl.
  destruct (st X).
  - omega.
  - omega.
Qed.

Example bequiv_example : bequiv (X - X = 0)%imp true.
Proof.
  unfold bequiv. intro st. unfold beval.
  rewrite aequiv_example. simpl. reflexivity.
Qed.

(* two commands are behaviorally equivalent if the first one
terminates in a particular state then so does the second, and vice
versa. *)
Definition cequiv (c1 c2 : com) : Prop :=
  forall (st st' : state),
    (st =[ c1 ]=> st') <-> (st =[ c2 ]=> st').

Theorem skip_left : forall c,
    cequiv (SKIP ;; c) c.
Proof.
  unfold cequiv. split.
  - intro H. inversion H. inversion H2.
    subst. apply H5.
  - intro H. eapply E_Seq.
    + apply E_Skip.
    + apply H.
Qed.

Theorem skip_right : forall c,
    cequiv (c ;; SKIP) c.
Proof.
  unfold cequiv. split.
  - intro H. inversion H. inversion H5. subst. apply H2.
  - intro H. eapply E_Seq.
    + apply H.
    + apply E_Skip.
Qed.

Theorem TEST_true_simple : forall c1 c2,
    cequiv (TEST true THEN c1 ELSE c2 FI) c1.
Proof.
  unfold cequiv. split.
  - intro H. inversion H.
    + apply H6.
    + simpl in H5. discriminate H5.
  - intro H. apply E_IfTrue.
    + reflexivity.
    + apply H.
Qed.

Theorem TEST_true : forall b c1 c2,
    bequiv b BTrue ->
    cequiv (TEST b THEN c1 ELSE c2 FI) c1.
Proof.
  unfold bequiv, cequiv. intros b c1 c2 H1.
  split.
  - intro H2. inversion H2.
    + apply H7.
    + rewrite H1 in H6. inversion H6.
  - intro H2. apply E_IfTrue.
    + apply H1.
    + apply H2.
Qed.

Theorem TEST_false : forall b c1 c2,
    bequiv b BFalse ->
    cequiv (TEST b THEN c1 ELSE c2 FI) c2.
Proof.
  unfold bequiv, cequiv. intros b c1 c2 H1. split.
  - intro H2. inversion H2.
    + rewrite H1 in H6. inversion H6.
    + apply H7.
  - intro H2. apply E_IfFalse.
    + apply H1.
    + apply H2.
Qed.

Theorem swap_if_branches : forall b e1 e2,
    cequiv
      (TEST b THEN e1 ELSE e2 FI)
      (TEST BNot b THEN e2 ELSE e1 FI).
Proof.
  unfold cequiv. split.
  - intro H. inversion H.
    + apply E_IfFalse.
      * simpl. rewrite H5. reflexivity.
      * apply H6.
    + apply E_IfTrue.
      * simpl. rewrite H5. reflexivity.
      * apply H6.
  - intro H. inversion H.
    + apply E_IfFalse.
      * simpl in H5. rewrite negb_true_iff in H5. apply H5.
      * apply H6.
    + apply E_IfTrue.
      * simpl in H5. rewrite negb_false_iff in H5. apply H5.
      * apply H6.
Qed.

Theorem WHILE_false : forall b c,
    bequiv b BFalse ->
    cequiv
      (WHILE b DO c END)
      SKIP.
Proof.
  unfold bequiv, cequiv. intros. split.
  - intro H1. inversion H1.
    + apply E_Skip.
    + rewrite H in H3. inversion H3.
  - intro H1. inversion H1. apply E_WhileFalse.
    apply H.
Qed.

Lemma WHILE_true_nonterm : forall b c st st',
    bequiv b BTrue ->
    ~( st =[WHILE b DO c END]=> st').
Proof.
  unfold bequiv, not. intros b c.
  remember (WHILE b DO c END)%imp as while eqn: Heqwhile.
  intros. induction H0.
  - inversion Heqwhile.
  - inversion Heqwhile.
  - inversion Heqwhile.
  - inversion Heqwhile.
  - inversion Heqwhile.
  - inversion Heqwhile. subst. rewrite H in H0.
    inversion H0.
  - apply IHceval2. apply Heqwhile.
Qed.

Theorem WHILE_true : forall b c,
    bequiv b true ->
    cequiv
      (WHILE b DO c END)
      (WHILE true DO SKIP END).
Proof.
  intros b c H.
  unfold cequiv. split.
  - intro H1. apply (WHILE_true_nonterm b c st st') in H.
    contradiction.
  - intro H1.
    assert (Heq: bequiv true true).
    { unfold bequiv. reflexivity. }
    apply (WHILE_true_nonterm true SKIP st st') in Heq.
    contradiction.
Qed.

Theorem loop_unrolling : forall b c,
    cequiv
      (WHILE b DO c END)
      (TEST b THEN (c ;; WHILE b DO c END) ELSE SKIP FI).
Proof.
  unfold cequiv. split.
  - intro H. inversion H.
    + apply E_IfFalse.
      * apply H4.
      * apply E_Skip.
    + apply E_IfTrue.
      * apply H2.
      * apply (E_Seq _ _ st st'0).
        { apply H3. }
        { apply H6. }
  - intro H. inversion H.
    + subst. inversion H6. apply (E_WhileTrue _ _ st'0).
      * apply H5.
      * apply H2.
      * apply H7.
    + inversion H6. subst. apply E_WhileFalse. apply H5.
Qed.

Theorem seq_assoc : forall c1 c2 c3,
    cequiv ((c1;;c2);;c3) (c1;;(c2;;c3)).
Proof.
  unfold cequiv. split.
  - intro H. inversion H. inversion H2.
    apply (E_Seq _ _ _ st'1).
    + apply H8.
    + apply (E_Seq _ _ _ st'0).
      * apply H11.
      * apply H5.
  - intro H. inversion H. inversion H5.
    apply (E_Seq _ _ _ st'1).
    * apply (E_Seq _ _ _ st'0); assumption.
    * assumption.
Qed.

Theorem identity_assignment : forall x,
    cequiv ( x ::= 0 ;; x ::= x ) ( x ::= 0 ;; SKIP).
Proof.
  unfold cequiv. split.
  - intro H. inversion H. inversion H2.  inversion H5. subst.    
    apply (E_Seq _ _ _ (x !-> aeval st 0; st)).
    + apply E_Ass. reflexivity.
    + assert (Heq : (x !-> aeval st 0; st) = (x !-> aeval (x !-> aeval st 0; st) x; x !-> aeval st 0; st)).
      { apply functional_extensionality.
        intro x0. destruct (string_dec x x0).
        * rewrite e. rewrite t_update_eq. rewrite t_update_eq.
          simpl. rewrite t_update_eq. reflexivity.
        * assert (Heq1 : (x !-> aeval (x !-> aeval st 0; st) x; x !-> aeval st 0; st) x0 = (x !-> aeval st 0; st) x0).
          { apply t_update_neq. apply n. }
          rewrite Heq1. reflexivity.
      }
      rewrite <- Heq. apply E_Skip.
  - intro H. inversion H. inversion H2. inversion H5. subst.
    apply (E_Seq _ _ _ (x !-> aeval st 0; st)).
    + apply E_Ass. reflexivity.
    + assert (Heq : (x !-> aeval st 0; st) = (x !-> aeval (x !-> aeval st 0; st) x; x !-> aeval st 0; st)).
      { apply functional_extensionality.
        intro x0. destruct (string_dec x x0).
        * rewrite e. rewrite t_update_eq. rewrite t_update_eq.
          simpl. rewrite t_update_eq. reflexivity.
        * assert (Heq1 : (x !-> aeval (x !-> aeval st 0; st) x; x !-> aeval st 0; st) x0 = (x !-> aeval st 0; st) x0).
          { apply t_update_neq. apply n. }
          rewrite Heq1. reflexivity.
      }
      assert (Heq1 : (x !-> aeval st 0; st) =[ x ::= x ]=> (x !-> aeval st 0; st) =
                                                           (x !-> aeval st 0; st) =[ x ::= x ]=> (x !-> aeval (x !-> aeval st 0; st) x; x !-> aeval st 0; st)).
      { rewrite <- Heq. reflexivity. }
      rewrite Heq1. apply E_Ass. reflexivity.
Qed.

Theorem assign_aequiv : forall (x : string) e,
    aequiv x e ->
    cequiv SKIP (x ::= e).
Proof.
  unfold aequiv, cequiv. split.
  - intro H1. inversion H1. subst.
    assert (Heq : (x !-> aeval st' e; st') = st').
    { apply functional_extensionality.
      intro x0. destruct (string_dec x x0).
      + rewrite e0. rewrite t_update_eq.
        simpl. destruct (st' x0) eqn:E.
        * rewrite <- H. subst. simpl. apply E. 
        * rewrite <- H. subst. simpl. apply E. 
      + apply t_update_neq. apply n.
    }
    assert (Heq1 : st' =[ x ::= e ]=> st' =
                  st' =[ x ::= e ]=> (x !-> aeval st' e; st')
           ).
    { rewrite Heq. reflexivity. }
    rewrite Heq1. apply E_Ass. reflexivity.
  - intro H1. inversion H1. subst.
    assert (Heq : (x !-> aeval st e; st) = st).
    { apply functional_extensionality.
      intro x0. destruct (string_dec x x0).
      + rewrite e0. rewrite t_update_eq.
        simpl. destruct (st x0) eqn:E.
        * rewrite <- H. subst. simpl. apply E. 
        * rewrite <- H. subst. simpl. apply E. 
      + apply t_update_neq. apply n.
    }
    rewrite Heq. apply E_Skip.
Qed.

Definition prog_a : com :=
  (WHILE ~(X <= 0) DO
     X ::= X + 1
   END)%imp.

Definition prog_b : com :=
  (TEST X = 0 THEN
     X ::= X + 1;;
     Y ::= 1
   ELSE
     Y ::= 0
   FI;;
   X ::= X - Y;;
   Y ::= 0)%imp.

Definition prog_c : com :=
  SKIP%imp.

Definition prog_d : com :=
  (WHILE ~(X = 0) DO
     X ::= (X * Y) + 1
   END)%imp.

Definition prog_e : com :=
  (Y ::= 0)%imp.

Definition prog_f : com :=
  (Y ::= X + 1;;
   WHILE ~(X = Y) DO
     Y ::= X + 1
   END)%imp.

Definition prog_g : com :=
  (WHILE true DO
    SKIP
   END)%imp.

Definition prog_h : com :=
  (WHILE ~(X = X) DO
    X ::= X + 1
   END)%imp.

Definition prog_i : com :=
  (WHILE ~(X = Y) DO
    X ::= Y + 1
   END)%imp.

Definition equiv_classes : list (list com) :=
  [[prog_c; prog_h];
   [prog_a; prog_b; prog_d; prog_e; prog_f; prog_g; prog_i]].

Lemma refl_aequiv : forall (a : aexp), aequiv a a.
Proof. unfold aequiv. reflexivity. Qed.

Lemma sym_aequiv : forall (a1 a2 : aexp),
    aequiv a1 a2 -> aequiv a2 a1.
Proof.
  unfold aequiv. intros. rewrite H. reflexivity.
Qed.

Lemma trans_aequiv : forall (a1 a2 a3 : aexp),
    aequiv a1 a2 -> aequiv a2 a3 -> aequiv a1 a3.
Proof.
  unfold aequiv. intros. rewrite H. rewrite H0. reflexivity.
Qed.

Lemma refl_bequiv : forall (b : bexp), bequiv b b.
Proof. unfold bequiv. reflexivity. Qed.

Lemma sym_bequiv : forall (b1 b2 : bexp),
    bequiv b1 b2 -> bequiv b2 b1.
Proof. unfold bequiv. intros. rewrite H. reflexivity. Qed.

Lemma trans_bequiv : forall (b1 b2 b3 : bexp),
    bequiv b1 b2 -> bequiv b2 b3 -> bequiv b1 b3.
Proof.
  unfold bequiv. intros. rewrite H. rewrite H0. reflexivity.
Qed.

Lemma refl_cequiv : forall (c : com), cequiv c c.
Proof. unfold cequiv. reflexivity. Qed.

Lemma sym_cequiv : forall (c1 c2 : com),
    cequiv c1 c2 -> cequiv c2 c1.
Proof.
  unfold cequiv. intros. rewrite H. reflexivity.
Qed.

Lemma iff_trans : forall (P1 P2 P3 : Prop),
    (P1 <-> P2) -> (P2 <-> P3) -> (P1 <-> P3).
Proof.
  intros. rewrite H. rewrite H0. reflexivity.
Qed.

Lemma trans_cequiv : forall (c1 c2 c3 : com),
    cequiv c1 c2 -> cequiv c2 c3 -> cequiv c1 c3.
Proof.
  unfold cequiv. intros.
  apply iff_trans with (P2 := (st =[ c2 ]=> st')).
  - apply H.
  - apply H0.
Qed.

Lemma test_congruence : forall (b : bool),
    b = true -> b = false -> False.
Proof. intros. congruence. Qed.

Theorem CAss_congruence : forall x a1 a1',
    aequiv a1 a1' ->
    cequiv (CAss x a1) (CAss x a1').
Proof.
  unfold aequiv, cequiv.
  intros. split.
  - intro H1. inversion H1. apply E_Ass.
    rewrite H in H5. apply H5.
  - intro H1. inversion H1. apply E_Ass.
    rewrite <- H in H5. apply H5.
Qed.

Theorem CWhile_congruence : forall b1 b1' c1 c1',
    bequiv b1 b1' -> cequiv c1 c1' ->
    cequiv (WHILE b1 DO c1 END) (WHILE b1' DO c1' END).
Proof.
  unfold bequiv, cequiv.
  intros. split.
  - intro H1. remember (WHILE b1 DO c1 END)%imp as while eqn: Heqwhile. induction H1.
    + inversion Heqwhile.
    + inversion Heqwhile.
    + inversion Heqwhile.
    + inversion Heqwhile.
    + inversion Heqwhile.
    + inversion Heqwhile. subst. apply E_WhileFalse.
      rewrite H in H1. apply H1.
    + inversion Heqwhile. subst. apply (E_WhileTrue _ _ st').
      * rewrite H in H1. apply H1.
      * apply H0. apply H1_.
      * apply IHceval2. reflexivity.
  - intro H1. remember (WHILE b1' DO c1' END)%imp as while eqn: Heqwhile. induction H1.
    + inversion Heqwhile.
    + inversion Heqwhile.
    + inversion Heqwhile.
    + inversion Heqwhile.
    + inversion Heqwhile.
    + inversion Heqwhile. subst. apply E_WhileFalse.
      rewrite <- H in H1. apply H1.
    + inversion Heqwhile. subst. apply (E_WhileTrue _ _ st').
      * rewrite <- H in H1. apply H1.
      * apply H0. apply H1_.
      * apply IHceval2. reflexivity.
Qed.

Theorem CSeq_congruence : forall c1 c1' c2 c2',
    cequiv c1 c1' -> cequiv c2 c2' ->
    cequiv (c1;;c2) (c1';;c2').
Proof.
  unfold cequiv. intros. split.
  - intro H1. inversion H1. subst. apply (E_Seq _ _ _ st'0).
    + apply H. apply H4.
    + apply H0. apply H7.
  - intro H1. inversion H1. subst. apply (E_Seq _ _ _ st'0).
    + apply H. apply H4.
    + apply H0. apply H7.
Qed.

Theorem CIf_congruence : forall b b' c1 c1' c2 c2',
    bequiv b b' -> cequiv c1 c1' -> cequiv c2 c2' ->
    cequiv (TEST b THEN c1 ELSE c2 FI)
           (TEST b' THEN c1' ELSE c2' FI).
Proof.
  unfold bequiv, cequiv.
  intros. split.
  - intro H2. inversion H2.
    + subst. apply E_IfTrue.
      * rewrite H in H8. apply H8.
      * apply H0. apply H9.
    + subst. apply E_IfFalse.
      * rewrite H in H8. apply H8.
      * apply H1. apply H9.
  - intro H2. inversion H2.
     + subst. apply E_IfTrue.
      * rewrite <- H in H8. apply H8.
      * apply H0. apply H9.
    + subst. apply E_IfFalse.
      * rewrite <- H in H8. apply H8.
      * apply H1. apply H9.
Qed.

Example congruence_example:
  cequiv
    (* Program 1: *)
    (X ::= 0;;
     TEST X = 0
     THEN
       Y ::= 0
     ELSE
       Y ::= 42
     FI)
    (* Program 2: *)
    (X ::= 0;;
     TEST X = 0
     THEN
       Y ::= X - X (* <--- Changed here *)
     ELSE
       Y ::= 42
     FI).
Proof.
  apply CSeq_congruence.
  - apply CAss_congruence. apply refl_aequiv.
  - apply CIf_congruence.
    + apply refl_bequiv. 
    + unfold cequiv. split.
      * intro H. inversion H. subst. apply E_Ass.
        simpl. apply sub_diag.
      * intro H. inversion H. subst. simpl.
        rewrite sub_diag. apply E_Ass. reflexivity.
    + apply refl_cequiv.
Qed.

Definition atrans_sound (atrans : aexp -> aexp) : Prop :=
  forall a : aexp, aequiv a (atrans a).

Definition btrans_sound (btrans : bexp -> bexp) : Prop :=
  forall b : bexp, bequiv b (btrans b).

Definition ctrans_sound (ctrans : com -> com) : Prop :=
  forall c : com, cequiv c (ctrans c).

Fixpoint fold_constants_aexp (a : aexp) : aexp :=
  match a with
  | ANum n => ANum n
  | AId x => AId x
  | APlus a1 a2 =>
    match (fold_constants_aexp a1, fold_constants_aexp a2) with
    | (ANum n1, ANum n2) => ANum (n1 + n2)
    | (a1', a2') => APlus a1' a2'
    end
  | AMinus a1 a2 =>
    match (fold_constants_aexp a1, fold_constants_aexp a2) with
    | (ANum n1, ANum n2) => ANum (n1 - n2)
    | (a1', a2') => AMinus a1' a2'
    end
  | AMult a1 a2 =>
    match (fold_constants_aexp a1, fold_constants_aexp a2) with
    | (ANum n1, ANum n2) => ANum (n1 * n2)
    | (a1', a2') => AMult a1' a2'
    end
  end.

Example fold_aexp_ex1 :
  fold_constants_aexp ((1 + 2) * X) = (3 * X)%imp.
Proof. simpl. reflexivity. Qed.

Example fold_aexp_ex2 :
  fold_constants_aexp (X - ((0 * 6) + Y))%imp = (X - (0 + Y))%imp.
Proof. simpl. reflexivity. Qed.

Fixpoint fold_constants_bexp (b : bexp) : bexp :=
  match b with
  | BTrue => BTrue
  | BFalse => BFalse
  | BEq a1 a2 =>
    match (fold_constants_aexp a1, fold_constants_aexp a2) with
    | (ANum n1, ANum n2) =>
      if n1 =? n2 then BTrue else BFalse
    | (a1', a2') =>
      BEq a1' a2'
    end
  | BLe a1 a2 =>
    match (fold_constants_aexp a1, 
           fold_constants_aexp a2) with
    | (ANum n1, ANum n2) =>
      if n1 <=? n2 then BTrue else BFalse
    | (a1', a2') =>
      BLe a1' a2'
    end
  | BNot b1 =>
    match (fold_constants_bexp b1) with
    | BTrue => BFalse
    | BFalse => BTrue
    | b1' => BNot b1'
    end
  | BAnd b1 b2 =>
    match (fold_constants_bexp b1, 
           fold_constants_bexp b2) with
    | (BTrue, BTrue) => BTrue
    | (BTrue, BFalse) => BFalse
    | (BFalse, BTrue) => BFalse
    | (BFalse, BFalse) => BFalse
    | (b1', b2') => BAnd b1' b2'
    end
  end.

Example fold_bexp_ex1 :
  fold_constants_bexp (true && ~(false && true))%imp 
  = true.
Proof. reflexivity. Qed.

Example fold_bexp_ex2 :
  fold_constants_bexp ((X = Y) && (0 = (2 - (1 + 1))))%imp
  = ((X = Y) && true)%imp.
Proof. reflexivity. Qed.

Open Scope imp.
Fixpoint fold_constants_com (c : com) : com :=
  match c with
  | SKIP => SKIP
  | x ::= a => x ::= (fold_constants_aexp a)
  | c1 ;; c2 =>
    (fold_constants_com c1) ;; (fold_constants_com c2)
  | TEST b THEN c1 ELSE c2 FI =>
      match fold_constants_bexp b with
      | BTrue => fold_constants_com c1
      | BFalse => fold_constants_com c2
      | b' => TEST b' THEN fold_constants_com c1
                     ELSE fold_constants_com c2 FI
      end
  | WHILE b DO c END =>
      match fold_constants_bexp b with
      | BTrue => WHILE BTrue DO SKIP END
      | BFalse => SKIP
      | b' => WHILE b' DO (fold_constants_com c) END
      end
  end.
Close Scope imp.

Example fold_com_ex1 :
  fold_constants_com
    (* Original program: *)
    (X ::= 4 + 5;;
     Y ::= X - 3;;
     TEST (X - Y) = (2 + 4) THEN SKIP
     ELSE Y ::= 0 FI;;
     TEST 0 <= (4 - (2 + 1)) THEN Y ::= 0
     ELSE SKIP FI;;
     WHILE Y = 0 DO
       X ::= X + 1
     END)%imp
  = (* After constant folding: *)
    (X ::= 9;;
     Y ::= X - 3;;
     TEST (X - Y) = 6 THEN SKIP 
     ELSE Y ::= 0 FI;;
     Y ::= 0;;
     WHILE Y = 0 DO
       X ::= X + 1
     END)%imp.
Proof. simpl. reflexivity. Qed.

Theorem fold_constants_aexp_sound :
  atrans_sound fold_constants_aexp.
Proof.
  unfold atrans_sound.
  unfold aequiv. intro a.
  induction a.
  - intro st. reflexivity.
  - intro st. reflexivity.
  - intro st. simpl. rewrite IHa1. rewrite IHa2.
    destruct (fold_constants_aexp a1);
      destruct (fold_constants_aexp a2); simpl; reflexivity.
  - intro st. simpl. rewrite IHa1. rewrite IHa2.
    destruct (fold_constants_aexp a1);
      destruct (fold_constants_aexp a2); simpl; reflexivity.
  - intro st. simpl. rewrite IHa1. rewrite IHa2.
    destruct (fold_constants_aexp a1);
      destruct (fold_constants_aexp a2); simpl; reflexivity.
Qed.

Theorem fold_constants_bexp_sound :
  btrans_sound fold_constants_bexp.
Proof.
  unfold btrans_sound. intros b. unfold bequiv.
  induction b.
  - intro st. reflexivity.
  - intro st. reflexivity.
  - intro st. simpl.
    remember (fold_constants_aexp a1) as a1' eqn:Heqa1'.
    remember (fold_constants_aexp a2) as a2' eqn:Heqa2'.
    replace (aeval st a1) with (aeval st a1') by
        (subst a1'; rewrite <- fold_constants_aexp_sound; reflexivity).
    replace (aeval st a2) with (aeval st a2') by
        (subst a2'; rewrite <- fold_constants_aexp_sound; reflexivity).
    destruct a1'; destruct a2'; try reflexivity.
    simpl. destruct (n =? n0); reflexivity.
  - intro st. simpl.
    remember (fold_constants_aexp a1) as a1' eqn:Heqa1'.
    remember (fold_constants_aexp a2) as a2' eqn:Heqa2'.
    replace (aeval st a1) with (aeval st a1') by
        (subst a1'; rewrite <- fold_constants_aexp_sound; reflexivity).
    replace (aeval st a2) with (aeval st a2') by
        (subst a2'; rewrite <- fold_constants_aexp_sound; reflexivity).
    destruct a1'; destruct a2'; try reflexivity.
    simpl. destruct (n <=? n0); reflexivity.
  - intro st. simpl.
    remember (fold_constants_bexp b) as b' eqn:Heqb'.
    rewrite IHb. destruct b'; reflexivity.
  - intro st. simpl.
    remember (fold_constants_bexp b1) as b1' eqn:Heqb1'.
    remember (fold_constants_bexp b2) as b2' eqn:Heqb2'.
    rewrite IHb1. rewrite IHb2.
    destruct b1'; destruct b2'; reflexivity.
Qed.

Theorem fold_constants_com_sound :
  ctrans_sound fold_constants_com.
Proof.
  unfold ctrans_sound. intros c.
  induction c.
  - simpl. apply refl_cequiv.
  - simpl. apply CAss_congruence. apply fold_constants_aexp_sound.
  - simpl. apply CSeq_congruence; assumption.
  - simpl. remember (fold_constants_bexp b) as b' eqn:Heqb'.
    destruct b'.
    + unfold cequiv in *.
      intros st st'. rewrite <- IHc1. apply TEST_true.
      rewrite Heqb'. apply fold_constants_bexp_sound.
    + unfold cequiv in *.
      intros st st'. rewrite <- IHc2. apply TEST_false.
      rewrite Heqb'. apply fold_constants_bexp_sound.
    + apply CIf_congruence.
      * rewrite Heqb'. apply fold_constants_bexp_sound.
      * apply IHc1.
      * apply IHc2.
    + apply CIf_congruence.
      * rewrite Heqb'. apply fold_constants_bexp_sound.
      * apply IHc1.
      * apply IHc2.
    + apply CIf_congruence.
      * rewrite Heqb'. apply fold_constants_bexp_sound.
      * apply IHc1.
      * apply IHc2.
    + apply CIf_congruence.
      * rewrite Heqb'. apply fold_constants_bexp_sound.
      * apply IHc1.
      * apply IHc2.
  - simpl. remember (fold_constants_bexp b) as b' eqn:Heqb'.
    destruct b'.
    + apply WHILE_true. unfold bequiv. intro st. simpl.
      rewrite fold_constants_bexp_sound. rewrite <- Heqb'.
      reflexivity.
    + apply WHILE_false. rewrite Heqb'.
      apply fold_constants_bexp_sound.
    + apply CWhile_congruence.
      * rewrite Heqb'. apply fold_constants_bexp_sound.
      * apply IHc.
    + apply CWhile_congruence.
      * rewrite Heqb'. apply fold_constants_bexp_sound.
      * apply IHc.
    + apply CWhile_congruence.
      * rewrite Heqb'. apply fold_constants_bexp_sound.
      * apply IHc.
    + apply CWhile_congruence.
      * rewrite Heqb'. apply fold_constants_bexp_sound.
      * apply IHc.
Qed.

Fixpoint optimize_0plus_aexp (a : aexp) : aexp :=
  match a with
  | ANum n => ANum n
  | AId x => AId x
  | APlus (ANum 0) a2 => optimize_0plus_aexp a2
  | APlus a1 a2 => APlus (optimize_0plus_aexp a1) (optimize_0plus_aexp a2)
  | AMinus a1 a2 => AMinus (optimize_0plus_aexp a1) (optimize_0plus_aexp a2)
  | AMult a1 a2 => AMult (optimize_0plus_aexp a1) (optimize_0plus_aexp a2)
  end.

Theorem optimize_0plus_aexp_sound :
  atrans_sound optimize_0plus_aexp.
Proof.
  unfold atrans_sound.
  apply aexp_ind.
  - intros n. simpl. apply refl_aequiv.
  - intros x. simpl. apply refl_aequiv.
  - intros. unfold aequiv. simpl. destruct a1.
    + intro st. simpl. rewrite H0. destruct n; reflexivity.
    + intro st. simpl; rewrite H0; reflexivity.
    + intro st. unfold aequiv in *. rewrite H0.
      simpl in *. rewrite H. reflexivity.
    + intro st. unfold aequiv in *. rewrite H0.
      simpl in *. rewrite H. reflexivity.
    + intro st. unfold aequiv in *. rewrite H0.
      simpl in *. rewrite H. reflexivity.
  - intros. unfold aequiv. simpl. destruct a1.
    + intro st. simpl. unfold aequiv in *. rewrite H0; reflexivity.
    + intro st. simpl; rewrite H0; reflexivity.
    + intro st. unfold aequiv in *. rewrite H0.
      simpl in *. rewrite H. reflexivity.
    + intro st. unfold aequiv in *. rewrite H0.
      simpl in *. rewrite H. reflexivity.
    + intro st. unfold aequiv in *. rewrite H0.
      simpl in *. rewrite H. reflexivity.
  - intros. unfold aequiv. simpl. destruct a1.
    + intro st. simpl. unfold aequiv in *. rewrite H0; reflexivity.
    + intro st. simpl; rewrite H0; reflexivity.
    + intro st. unfold aequiv in *. rewrite H0.
      simpl in *. rewrite H. reflexivity.
    + intro st. unfold aequiv in *. rewrite H0.
      simpl in *. rewrite H. reflexivity.
    + intro st. unfold aequiv in *. rewrite H0.
      simpl in *. rewrite H. reflexivity.
Qed.

Fixpoint optimize_0plus_bexp (b : bexp) : bexp :=
  match b with
  | BTrue | BFalse => b
  | BEq a1 a2 => BEq (optimize_0plus_aexp a1) (optimize_0plus_aexp a2)
  | BLe a1 a2 => BLe (optimize_0plus_aexp a1) (optimize_0plus_aexp a2)
  | BNot b1 => BNot (optimize_0plus_bexp b1)
  | BAnd b1 b2 => BAnd (optimize_0plus_bexp b1) (optimize_0plus_bexp b2)
  end.

Theorem optimize_0plus_bexp_sound :
      btrans_sound optimize_0plus_bexp.
Proof.
  unfold btrans_sound.
  apply bexp_ind.
    - apply refl_bequiv. 
    - apply refl_bequiv.
    - intros a1 a2. unfold bequiv.
      intro st. simpl.
      rewrite (optimize_0plus_aexp_sound a1).
      rewrite (optimize_0plus_aexp_sound a2).
      reflexivity.
    - intros a1 a2. unfold bequiv.
      intro st. simpl.
      rewrite (optimize_0plus_aexp_sound a1).
      rewrite (optimize_0plus_aexp_sound a2).
      reflexivity.
    - intros b H. unfold bequiv. simpl. intro st.
      rewrite H. reflexivity.
    - intros b1 H1 b2 H2. unfold bequiv. intro st.
      simpl. rewrite H1, H2. reflexivity.
Qed.

Open Scope imp.
Fixpoint optimize_0plus_com (c : com) : com :=
  match c with
  | SKIP => SKIP
  | x ::= a => x ::= (optimize_0plus_aexp a)
  | c1 ;; c2 =>
    (optimize_0plus_com c1) ;; (optimize_0plus_com c2)
  | TEST b THEN c1 ELSE c2 FI =>
      match optimize_0plus_bexp b with
      | BTrue => optimize_0plus_com c1
      | BFalse => optimize_0plus_com c2
      | b' => TEST b' THEN optimize_0plus_com c1
              ELSE optimize_0plus_com c2 FI
      end
  | WHILE b DO c END =>
      match optimize_0plus_bexp b with
      | BTrue => WHILE BTrue DO SKIP END
      | BFalse => SKIP
      | b' => WHILE b' DO (optimize_0plus_com c) END
      end
  end.
Close Scope imp.

Theorem optimize_0plus_com_sound :
      ctrans_sound optimize_0plus_com.
Proof.
  unfold ctrans_sound.
  intro c. induction c.
  - simpl. apply refl_cequiv.
  - simpl. apply CAss_congruence. apply optimize_0plus_aexp_sound.
  - simpl. apply CSeq_congruence; assumption.
  - simpl. remember (optimize_0plus_bexp b) as b' eqn:Heqb'.
    destruct b'.
    + unfold cequiv in *.
      intros st st'. rewrite <- IHc1. apply TEST_true.
      rewrite Heqb'. apply optimize_0plus_bexp_sound.
    + unfold cequiv in *.
      intros st st'. rewrite <- IHc2. apply TEST_false.
      rewrite Heqb'. apply optimize_0plus_bexp_sound.
    + apply CIf_congruence.
      * rewrite Heqb'. apply optimize_0plus_bexp_sound.
      * apply IHc1.
      * apply IHc2.
    + apply CIf_congruence.
      * rewrite Heqb'. apply optimize_0plus_bexp_sound.
      * apply IHc1.
      * apply IHc2.
    + apply CIf_congruence.
      * rewrite Heqb'. apply optimize_0plus_bexp_sound.
      * apply IHc1.
      * apply IHc2.
    + apply CIf_congruence.
      * rewrite Heqb'. apply optimize_0plus_bexp_sound.
      * apply IHc1.
      * apply IHc2.
  - simpl. remember (optimize_0plus_bexp b) as b' eqn:Heqb'.
    destruct b'.
    + apply WHILE_true. unfold bequiv. intro st. simpl.
      rewrite optimize_0plus_bexp_sound. rewrite <- Heqb'.
      reflexivity.
    + apply WHILE_false. rewrite Heqb'.
      apply optimize_0plus_bexp_sound.
    + apply CWhile_congruence.
      * rewrite Heqb'. apply optimize_0plus_bexp_sound.
      * apply IHc.
    + apply CWhile_congruence.
      * rewrite Heqb'. apply optimize_0plus_bexp_sound.
      * apply IHc.
    + apply CWhile_congruence.
      * rewrite Heqb'. apply optimize_0plus_bexp_sound.
      * apply IHc.
    + apply CWhile_congruence.
      * rewrite Heqb'. apply optimize_0plus_bexp_sound.
      * apply IHc.
Qed.

Fixpoint subst_aexp (x : string) (u : aexp) (a : aexp) : aexp :=
  match a with
  | ANum n => a
  | AId x' => if eqb_string x x' then u else a
  | APlus a1 a2 =>
    APlus (subst_aexp x u a1) (subst_aexp x u a2)
  | AMinus a1 a2 =>
    AMinus (subst_aexp x u a1) (subst_aexp x u a2)
  | AMult a1 a2 =>
    AMult (subst_aexp x u a1) (subst_aexp x u a2)
  end.

Example subst_aexp_ex :
  subst_aexp X (42 + 53) (Y + X)%imp = (Y + (42 + 53))%imp.
Proof. reflexivity. Qed.

Definition subst_equiv_property := forall x1 x2 a1 a2,
    cequiv (x1 ::= a1;; x2 ::= a2)
           (x1 ::= a1;; x2 ::= subst_aexp x1 a1 a2).

Theorem subst_inequiv : ~ subst_equiv_property.
Proof.
  unfold subst_equiv_property. unfold not.
  intros. unfold cequiv in H.
  destruct (H X Y (X + 1)%imp X%imp (X !-> 0) (Y !-> 1; X !-> 1; X !-> 0)).
  simpl in *.
  assert (HTrue : (X !-> 0) =[ X ::= X + 1;; Y ::= X ]=> (Y !-> 1; X !-> 1; X !-> 0)).
  { apply (E_Seq _ _ _ (X !-> 1; X !-> 0)).
    - apply E_Ass. reflexivity.
    - apply E_Ass. reflexivity.
  }
  apply H0 in HTrue. inversion HTrue. inversion H4. subst. simpl in H7.
  inversion H7. simpl in H6. subst.
  assert (Heq : (Y !-> 2; X !-> 1; X !-> 0) Y = (Y !-> 1; X !-> 1; X !-> 0) Y).
  rewrite H8. reflexivity.
  rewrite t_update_eq in Heq. rewrite t_update_eq in Heq. inversion Heq.
Qed.

Inductive var_not_used_in_aexp (x : string) : aexp -> Prop :=
| VNUNum : forall n, var_not_used_in_aexp x (ANum n)
| VNUId : forall y, x <> y -> var_not_used_in_aexp x (AId y)
| VNUPlus : forall a1 a2,
    var_not_used_in_aexp x a1 ->
    var_not_used_in_aexp x a2 ->
    var_not_used_in_aexp x (APlus a1 a2)
| VNUMinus : forall a1 a2,
    var_not_used_in_aexp x a1 ->
    var_not_used_in_aexp x a2 ->
    var_not_used_in_aexp x (AMinus a1 a2)
| VNUMult : forall a1 a2,
    var_not_used_in_aexp x a1 ->
    var_not_used_in_aexp x a2 ->
    var_not_used_in_aexp x (AMult a1 a2).

Lemma aeval_weakening : forall x st a ni,
    var_not_used_in_aexp x a ->
    aeval (x !-> ni ; st) a = aeval st a.
Proof.
  intros x st a ni H. induction H.
  - reflexivity.
  - apply (t_update_neq nat st x y ni) in H.
    simpl. rewrite H. reflexivity.
  - simpl. rewrite IHvar_not_used_in_aexp1.
    rewrite IHvar_not_used_in_aexp2.
    reflexivity.
  - simpl. rewrite IHvar_not_used_in_aexp1.
    rewrite IHvar_not_used_in_aexp2.
    reflexivity.
  - simpl. rewrite IHvar_not_used_in_aexp1.
    rewrite IHvar_not_used_in_aexp2.
    reflexivity.
Qed.

Theorem inequiv_exrcise :
  ~ cequiv (WHILE true DO SKIP END) SKIP.
Proof.
  unfold not, cequiv. intro H.
  destruct (H empty_st empty_st).
  assert (Hskip : empty_st =[ SKIP ]=> empty_st).
  { apply E_Skip. }
  apply H1 in Hskip.
  remember (WHILE true DO SKIP END)%imp as while eqn:Heqwhile.
  induction Hskip; try inversion Heqwhile.
  - subst. inversion H2.
  - subst. apply IHHskip2.
    + reflexivity.
    + apply H.
    + apply H0.
    + apply H1.
Qed.

Module Himp.

  Inductive com : Type :=
  | CSkip : com
  | CAss : string -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com
  | CHavoc : string -> com.

  Notation "'SKIP'" :=
    CSkip : imp_scope.
  Notation "X '::=' a" :=
    (CAss X a) (at level 60) : imp_scope.
  Notation "c1 ;; c2" :=
    (CSeq c1 c2) (at level 80, right associativity) : imp_scope.
  Notation "'WHILE' b 'DO' c 'END'" :=
    (CWhile b c) (at level 80, right associativity) : imp_scope.
  Notation "'TEST' e1 'THEN' e2 'ELSE' e3 'FI'" :=
    (CIf e1 e2 e3) (at level 80, right associativity) : imp_scope.
  Notation "'HAVOC' l" :=
    (CHavoc l) (at level 60) : imp_scope.

  Reserved Notation "st '=[' c ']=>' st'" (at level 40).

  Open Scope imp_scope.
  Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall st, st =[ SKIP ]=> st
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
  | E_Havoc : forall st x n,
      st =[ HAVOC x ]=> ( x !-> n; st)

  where "st =[ c ]=> st'" := (ceval c st st').
  Close Scope imp_scope.

  Example havoc_example1 : empty_st =[ (HAVOC X)%imp ]=> (X !-> 0).
  Proof. apply E_Havoc. Qed.

  Example havoc_example2 :
    empty_st =[ (SKIP ;; HAVOC Z)%imp ]=> (Z !-> 42).
  Proof.
    eapply E_Seq.
    - apply E_Skip.
    - apply E_Havoc.
  Qed.

  Definition cequiv (c1 c2 : com) : Prop := forall st st' : state,
      st =[ c1 ]=> st' <-> st =[ c2 ]=> st'.

  Definition pXY :=
    (HAVOC X;; HAVOC Y)%imp.
  Definition pYX :=
    (HAVOC Y;; HAVOC X)%imp.

  Theorem pXY_cequiv_pYX :
    cequiv pXY pYX \/ ~ cequiv pXY pYX.
  Proof.
    left. unfold pXY, pYX, cequiv.
    split.
    - intro H. inversion H. subst.
      inversion H2. subst.
      inversion H5. subst.
      assert (HeqSt: (Y !-> n0; X !-> n; st) = (X !-> n; Y !-> n0; st)).
      { apply (t_update_permute nat st n0 n Y X). unfold not.
        intro H3. inversion H3.
      }
      rewrite HeqSt.
      apply (E_Seq _ _ _ (Y !-> n0; st)).
      + apply E_Havoc.
      + apply E_Havoc.
    - intro H. inversion H. subst.
      inversion H2. subst.
      inversion H5. subst.
      assert (HeqSt: (X !-> n0; Y !-> n; st) = (Y !-> n; X !-> n0; st)).
      { apply (t_update_permute nat st n0 n X Y). unfold not.
        intro H3. inversion H3.
      }
      rewrite HeqSt.
      apply (E_Seq _ _ _ (X !-> n0; st)).
      + apply E_Havoc.
      + apply E_Havoc.
  Qed.

  Definition ptwice :=
    (HAVOC X;; HAVOC Y)%imp.
  Definition pcopy :=
    (HAVOC X;; Y ::= X)%imp.

  Theorem ptwice_cequiv_pcopy :
    cequiv ptwice pcopy \/ ~ cequiv ptwice pcopy.
  Proof.
    right. unfold not, ptwice, cequiv, pcopy.
    intro H. destruct (H empty_st (Y !-> 1; X !-> 0)).
    assert (H2: empty_st =[ (HAVOC X;; HAVOC Y)%imp ]=> (Y !-> 1; X !-> 0)).
    { apply (E_Seq _ _ _ (X !-> 0)).
      - apply E_Havoc.
      - apply E_Havoc.
    }
    apply H0 in H2. inversion H2. subst.
    inversion H8. subst.
    inversion H5. subst.
    simpl in H9. rewrite t_update_eq in H9.
    assert (Hcontr: n = 1 /\ n = 0).
    { split.
      assert (Heq : (Y !-> n; X !-> n) Y = (Y !-> 1; X !-> 0) Y).
      { rewrite H9. reflexivity. }
      rewrite t_update_eq in Heq. rewrite t_update_eq in Heq.
      apply Heq.
      assert (Heq : (Y !-> n; X !-> n) X = (Y !-> 1; X !-> 0) X).
      { rewrite H9. reflexivity. }
      rewrite t_update_neq in Heq. rewrite t_update_eq in Heq.
      rewrite t_update_neq in Heq. rewrite t_update_eq in Heq.
      apply Heq.
      intro HYX. inversion HYX.
      intro HYX. inversion HYX.
    }
    destruct Hcontr. congruence.
  Qed.

  Definition p1 : com :=
    (WHILE ~(X = 0) DO
       HAVOC Y;;
       X ::= X + 1
     END)%imp.

  Definition p2 : com :=
    (WHILE ~(X = 0) DO
       SKIP
     END)%imp.

  Lemma p1_may_diverge : forall st st',
      st X <> 0 ->
      ~ st =[ p1 ]=> st'.                                  
  Proof.
    intros st st' H1 H2.
    unfold p1 in H2.
    remember ((WHILE ~ X = 0 DO HAVOC Y;; X ::= X + 1 END)%imp) as
        while eqn:Heqwhile.
    induction H2; try (inversion Heqwhile).
    - rewrite H2 in H. simpl in H.
      rewrite negb_false_iff in H.
      rewrite eqb_eq in H.
      congruence.
    - apply IHceval2.
      + subst. inversion H2_. subst. inversion H3.
        subst. inversion H6. subst.
        rewrite t_update_eq. simpl. rewrite t_update_neq. intro Hneq.
        destruct (st X).
        * contradiction.
        * simpl in Hneq. inversion Hneq.
        * intro HYX. inversion HYX.
      + subst. inversion H2_. subst. inversion H3.
        subst. inversion H6. subst.
        reflexivity.
  Qed.

  Lemma p2_may_diverge : forall st st',
      st X <> 0 ->
      ~ st =[ p2 ]=> st'.
  Proof.
    intros st st' H1 H2.
    unfold p2 in H2.
    remember (WHILE ~ X = 0 DO SKIP END)%imp as while eqn:Heqwhile.
    induction H2; try (inversion Heqwhile).
    - rewrite H2 in H. simpl in H.
      rewrite negb_false_iff in H.
      rewrite eqb_eq in H.
      destruct (st X).
      + apply H1. reflexivity. 
      + congruence. 
    - apply IHceval2.
      + subst. inversion H2_. subst. assumption. 
      + subst. inversion H2_. subst. assumption. 
  Qed.

  Theorem p1_p2_equiv : cequiv p1 p2.
  Proof.
    unfold cequiv, p1, p2. split.
    - intro H.
      remember ((WHILE ~ X = 0 DO HAVOC Y;; X ::= X + 1 END)%imp) as
          while eqn:Heqwhile.
      induction H; try inversion Heqwhile.
      + apply E_WhileFalse. rewrite H1 in H. apply H.
      + apply IHceval2 in Heqwhile.
        inversion Heqwhile.
        * subst. inversion H0. subst.
          inversion H4. subst. inversion H7. subst.
          simpl in H8. rewrite negb_false_iff in H8.
          rewrite eqb_eq in H8.
          rewrite t_update_eq in H8.
          destruct ((Y !-> n; st) X).
          inversion H8. inversion H8.
        * subst.
          remember (WHILE ~ X = 0 DO SKIP END)%imp as while1 eqn:Heqwhile1.
          induction H10; try inversion Heqwhile1.
          { inversion H7. subst. congruence. }
          { subst. inversion H7. subst. apply IHceval4.
            { reflexivity. }
            { apply Heqwhile. }
            { intro. apply Heqwhile. }
            { intro H11. inversion H11. }
            { apply H1. }
            { apply H10_. }
          }
    - intro H.
      remember (WHILE ~ X = 0 DO SKIP END)%imp as while1 eqn:Heqwhile.
      induction H; try inversion Heqwhile.
      + apply E_WhileFalse. rewrite H1 in H. apply H.
      + apply IHceval2 in Heqwhile.
        inversion Heqwhile.
        * subst. inversion H0. subst. congruence.
        * subst. inversion H0. subst. apply IHceval2.
          reflexivity.
  Qed.

  Definition p3 : com :=
    (Z ::= 1;;
     WHILE ~(X = 0) DO
       HAVOC X;;
       HAVOC Z
     END)%imp.
  
  Definition p4 : com :=
    (X ::= 0;;
     Z ::= 1)%imp.

  Theorem p3_p4_inequiv : ~ cequiv p3 p4.
  Proof.
    unfold cequiv, p3, p4. intro H.
    destruct (H (X !-> 1) (Z !-> 2;X !-> 0; X !-> 1)).
    assert (HFalse : (X !-> 1) =[ (Z ::= 1;; WHILE ~ X = 0 DO HAVOC X;; HAVOC Z END)%imp
                                ]=> (Z !-> 2; X !-> 0; X !-> 1)).
    { eapply E_Seq. apply E_Ass. reflexivity. simpl. eapply E_WhileTrue. reflexivity. eapply E_Seq. apply (E_Havoc _ _ 0).
      apply (E_Havoc _ _ 2).
      assert (Heq : (Z !-> 2; X !-> 0; Z !-> 1; X !-> 1)
                    = (Z !-> 2; X !-> 0; X !-> 1)).
      { apply functional_extensionality. intro x.
        destruct (string_dec Z x).
        - rewrite e. repeat rewrite t_update_eq. reflexivity.
        - assert (Heq1 :  (Z !-> 2; X !-> 0; Z !-> 1; X !-> 1) x =
                          (X !-> 0; Z !-> 1; X !-> 1) x).
          { apply t_update_neq. apply n. }
          rewrite Heq1. 
          assert (Heq2 : (Z !-> 2; X !-> 0; X !-> 1) x =
                 (X !-> 0; X !-> 1) x).

          { apply t_update_neq. apply n. }
          rewrite Heq2. 
          destruct (string_dec X x).
          + rewrite e. repeat rewrite t_update_eq. reflexivity.
          + assert (Heq3 : (X !-> 0; Z !-> 1; X !-> 1) x
                           = (Z !-> 1; X !-> 1) x).
            { apply t_update_neq. apply n0. }
            rewrite Heq3.
            assert (Heq4 : (X !-> 0; X !-> 1) x = (X !-> 1) x).
            { apply t_update_neq. apply n0. }
            rewrite Heq4.
            apply t_update_neq. apply n.
      }
      rewrite Heq. apply E_WhileFalse. reflexivity.
    }
    apply H0 in HFalse.
    inversion HFalse. subst.
    inversion H4. subst.
    inversion H7. subst. simpl in H8.
    assert (Heq : (Z !-> 1; X !-> 0; X !-> 1) Z = (Z !-> 2; X !-> 0; X !-> 1) Z).
    { rewrite H8. reflexivity. }
    repeat rewrite t_update_eq in Heq.
    inversion Heq. 

  Qed.

  Definition p5 : com :=
  (WHILE ~(X = 1) DO
     HAVOC X
   END)%imp.

  Definition p6 : com :=
    (X ::= 1)%imp.

  Theorem p5_p6_equiv : cequiv p5 p6.
  Proof.
    unfold cequiv, p5, p6.
    split.
    - remember (WHILE ~ X = 1 DO HAVOC X END)%imp as while eqn:Heqwhile.
      intro H. induction H; try inversion Heqwhile.
      + subst. simpl in H. rewrite negb_false_iff in H.
        rewrite eqb_eq in H.
        assert (Heq1 : st = (X !-> 1; st)).
        { apply functional_extensionality.
          intro x. destruct (string_dec X x).
          * rewrite <- e. rewrite t_update_eq. apply H.
          * apply (t_update_neq nat st X x 1) in n. symmetry. apply n.
        }
        assert (Heq2 : st =[ (X ::= 1)%imp ]=> st <->
                       st =[ (X ::= 1)%imp ]=> (X !-> 1; st)
               ).
        { rewrite <- Heq1. reflexivity. }
        rewrite Heq2. apply E_Ass. reflexivity.
      + subst. simpl in H. rewrite negb_true_iff in H.
        rewrite eqb_neq in H.
        inversion H0. subst.
        apply IHceval2 in Heqwhile. inversion Heqwhile.
        subst. simpl.
        assert (Heq: (X !-> 1; X !-> n; st) = (X !-> 1; st)).
        { apply functional_extensionality.
          intro x. rewrite t_update_shadow. reflexivity.
        }
        rewrite Heq. apply E_Ass. reflexivity.
    - intro H. inversion H. subst. simpl in *.
      destruct (st X) eqn: HstX.
      + eapply E_WhileTrue.
        * simpl. rewrite HstX. reflexivity.
        * apply E_Havoc.
        * apply E_WhileFalse. simpl. reflexivity.
      + destruct n as [| n'].
        * assert (Heq : (X !-> 1; st) = st).
          { apply functional_extensionality.
            intro x. destruct (string_dec X x).
            { rewrite <- e. rewrite t_update_eq.
              symmetry. apply HstX.
            }
            { apply (t_update_neq nat st X x 1) in n. apply n. }
          }
          rewrite Heq. apply E_WhileFalse. simpl. rewrite HstX.
          reflexivity.
        * eapply E_WhileTrue.
          { simpl. rewrite HstX. reflexivity. }
          { apply E_Havoc. }
          { apply E_WhileFalse. reflexivity. }
  Qed.

End Himp.

Theorem swap_noninterfering_assignments : forall l1 l2 a1 a2,
    l1 <> l2 ->
    var_not_used_in_aexp l1 a2 ->
    var_not_used_in_aexp l2 a1 ->
    cequiv
      (l1 ::= a1;; l2 ::= a2)
      (l2 ::= a2;; l1 ::= a1).
Proof.
  intros l1 l2 a1 a2 H1 H2 H3.
  unfold cequiv. split.
  - intro H4.
    inversion H4. subst.
    inversion H5. subst.
    inversion H8. subst.
    eapply E_Seq.
    + apply E_Ass. reflexivity.
    + assert (Heq :
      (l2 !-> aeval (l1 !-> aeval st a1; st) a2; l1 !-> aeval st a1; st)
      =
      (l1 !-> aeval st a1; l2 !-> aeval (l1 !-> aeval st a1; st) a2; st)).
      { apply t_update_permute. apply H1. }
      rewrite Heq.
      assert (Heq1 : aeval st a2 = aeval (l1 !-> aeval st a1; st) a2).
      { symmetry. apply aeval_weakening. apply H2. }
      rewrite <- Heq1. apply E_Ass.
      apply aeval_weakening. apply H3.
  - intro H4.
    inversion H4. subst.
    inversion H5. subst.
    inversion H8. subst.
    eapply E_Seq.
    + apply E_Ass. reflexivity.
    + assert (Heq :
      (l1 !-> aeval (l2 !-> aeval st a2; st) a1; l2 !-> aeval st a2; st)
      =
      (l2 !-> aeval st a2; l1 !-> aeval (l2 !-> aeval st a2; st) a1; st)).
      { apply t_update_permute. auto. }
      rewrite Heq.
      assert (Heq1 : aeval st a1 = aeval (l2 !-> aeval st a2; st) a1).
      { symmetry. apply aeval_weakening. apply H3. }
      rewrite <- Heq1. apply E_Ass.
      apply aeval_weakening. apply H2.
Qed.

Definition capprox (c1 c2 : com) : Prop := forall (st st' : state),
    st =[ c1 ]=> st' -> st =[ c2 ]=> st'.

Definition c3 : com :=
  X ::= 1.

Definition c4 : com :=
  X ::= 2.

Theorem c3_c4_different : ~capprox c3 c4 /\ ~ capprox c4 c3.
Proof.
  split.
  - unfold not, capprox. intros.
    assert (Hf : empty_st =[ c3 ]=> (X !-> 1) -> empty_st =[ c4 ]=> (X !-> 1)).
    { apply H. }
    assert (Hf1 : empty_st =[ c4 ]=> (X !-> 1)).
    { apply Hf. apply E_Ass. reflexivity. }
    inversion Hf1. simpl in H3. subst. 
    assert (Heq : (X !-> 2; empty_st) X = (X !-> 1) X).
    { rewrite H4. reflexivity. }
    rewrite t_update_eq in Heq. rewrite t_update_eq in Heq.
    inversion Heq.
  - unfold not, capprox. intros.
    assert (Hf : empty_st =[ c4 ]=> (X !-> 2) -> empty_st =[ c3 ]=> (X !-> 2)).
    { apply H. }
    assert (Hf1 : empty_st =[ c3 ]=> (X !-> 2)).
    { apply Hf. apply E_Ass. reflexivity. }
    inversion Hf1. simpl in H3. subst. 
    assert (Heq : (X !-> 1; empty_st) X = (X !-> 2) X).
    { rewrite H4. reflexivity. }
    rewrite t_update_eq in Heq. rewrite t_update_eq in Heq.
    inversion Heq.
Qed.

Definition cmin : com :=
  WHILE true DO
    SKIP
  END.

Theorem cmin_minimal : forall c, capprox cmin c.
Proof.
  unfold capprox. intros.
  assert (H' : ~ (st =[ cmin ]=> st')).
  { apply WHILE_true_nonterm. simpl. apply refl_bequiv. }
  congruence.
Qed.

Definition zprop (c : com) : Prop :=
  forall c1, capprox c1 c.

Theorem zprop_preserving : forall c c',
    zprop c -> capprox c c' -> zprop c'.
Proof.
  unfold zprop. unfold capprox. intros.
  apply H0. apply (H c1). apply H1.
Qed.

