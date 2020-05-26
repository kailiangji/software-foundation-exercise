From Coq Require Import omega.Omega.
From Coq Require Import Arith.Arith.
From LF Require Import Imp Maps.

Open Scope imp_scope.

Fixpoint ceval_step2 (st : state) (c : com) (i : nat) : state :=
  match i with
  | 0 => empty_st
  | S i' =>
    match c with
    | SKIP => st
    | l ::= a1 =>
      (l |-> aeval st a1 ; st)
    | c1 ;; c2 =>
      let st' := ceval_step2 st c1 i' in
      ceval_step2 st' c2 i'
    | TEST b THEN c1 ELSE c2 FI =>
      if (beval st b)
      then ceval_step2 st c1 i'
      else ceval_step2 st c2 i'
    | WHILE b1 DO c1 END =>
      if (beval st b1)
      then let st' := ceval_step2 st c1 i' in
           ceval_step2 st' c i'
      else st
    end
  end.
Close Scope imp_scope.

Open Scope imp_scope.

Fixpoint ceval_step3 (st : state) (c : com) (i : nat) : option state :=
  match i with
  | 0 => None
  | S i' =>
    match c with
    | SKIP => Some st
    | l ::= a1 =>
      Some (l |-> aeval st a1 ; st)
    | c1 ;; c2 =>
      match (ceval_step3 st c1 i') with
      | Some st' => ceval_step3 st' c2 i'
      | None => None
      end
    | TEST b THEN c1 ELSE c2 FI =>
      if (beval st b)
      then ceval_step3 st c1 i'
      else ceval_step3 st c2 i'
    | WHILE b1 DO c1 END =>
      if (beval st b1)
      then match (ceval_step3 st c1 i') with
           | Some st' => ceval_step3 st' c i'
           | None => None
           end
      else Some st
    end
  end.
Close Scope imp_scope.

Notation "'LETOPT' x <== e1 'IN' e2" :=
  (match e1 with
   | Some x => e2
   | None => None
   end)
    (right associativity, at level 60).

Open Scope imp_scope.

Fixpoint ceval_step (st : state) (c : com) (i : nat) : option state :=
  match i with
  | 0 => None
  | S i' =>
    match c with
    | SKIP =>
      Some st
    | l ::= a1 =>
      Some (l |-> aeval st a1 ; st)
    | c1 ;; c2 =>
      LETOPT st' <== ceval_step st c1 i' IN
             ceval_step st' c2 i'
    | TEST b THEN c1 ELSE c2 FI =>
      if (beval st b)
      then ceval_step st c1 i'
      else ceval_step st c2 i'
    | WHILE b1 DO c1 END =>
      if (beval st b1)
      then LETOPT st' <== ceval_step st c1 i' IN
                  ceval_step st' c i'
      else Some st
    end
  end.
Close Scope imp_scope.

Definition test_ceval (st : state) (c : com) :=
  match ceval_step st c 500 with
  | None => None
  | Some st => Some (st X, st Y, st Z)
  end.

Compute
     (test_ceval empty_st
         (X ::= 2;;
          TEST (X <= 1)
            THEN Y ::= 3
            ELSE Z ::= 4
            FI)).

Definition pup_to_n : com :=
  Y ::= 0;;
  WHILE X > 0 DO
    Y ::= Y + X;;
    X ::= X - 1
  END.

Example pup_to_n_1 :
  test_ceval (X |-> 5) pup_to_n = Some (Some 0, Some 15, None).
Proof. reflexivity. Qed.

Definition is_even : com :=
  WHILE X > 1 DO
    X ::= X - 2
  END;;
  TEST X = 0 THEN
    Z ::= 0
  ELSE
    Z ::= 1
  FI.

Example is_even_10 :
  test_ceval (X |-> 10) is_even = Some (Some 0, None, Some 0).
Proof. reflexivity. Qed.

Theorem ceval_step__ceval : forall c st st',
    (exists i, ceval_step st c i = Some st') ->
    st =[ c ]=> st'.
Proof.
  intro c. induction c.
  - intros st st' H. destruct H. destruct x as [| x' ].
    + inversion H.
    + inversion H. apply E_Skip.
  - intros st st' H. destruct H. destruct x0 as [| x0' ].
    + inversion H.
    + inversion H. apply E_Ass. reflexivity.
  - intros st st' H. destruct H. destruct x as [| x' ].
    + inversion H.
    + inversion H. destruct (ceval_step st c1 x') eqn:E.
      * assert (H2 : st =[ c1 ]=> s).
        { apply IHc1. exists x'. apply E. }
        assert (H3 : s =[ c2 ]=> st').
        { apply IHc2. exists x'. apply H1. }
        apply (E_Seq c1 c2 st s st'); assumption.
      * inversion H1.
  - intros st st' H. destruct H. destruct x as [| x' ].
    + inversion H.
    + destruct (beval st b) eqn:Eb.
      * apply E_IfTrue.
        { apply Eb. }
        { inversion H. rewrite Eb in H1. apply IHc1. eexists. apply H1. }
      * apply E_IfFalse.
        { apply Eb. }
        { inversion H. rewrite Eb in H1. apply IHc2. eexists. apply H1. }
  - intros st st' H. destruct H.
    generalize dependent st'.
    generalize dependent st.
    remember (WHILE b DO c END)%imp as while eqn:Heqwhile.
    induction x as [| x' IH ].
    + intros st st' H. inversion H.
    + intros st st' H. destruct (beval st b) eqn:Eb.
      * inversion H. destruct while.
        { inversion Heqwhile. }
        { inversion Heqwhile. }
        { inversion Heqwhile. }
        { inversion Heqwhile. }
        { inversion Heqwhile. subst. rewrite Eb in H1.
          destruct (ceval_step st c x') eqn:E.
          { apply IH in H1.
            assert (He : exists i, ceval_step st c i = Some s).
            { exists x'. apply E. }
            apply (IHc st s) in He.
            apply (E_WhileTrue b st s).
            { apply Eb. }
            { apply He. }
            { apply H1. }
          }
          { inversion H1. }
        }
      * inversion H. destruct while.
        { inversion Heqwhile. }
        { inversion Heqwhile. }
        { inversion Heqwhile. }
        { inversion Heqwhile. }
        { inversion Heqwhile. subst. rewrite Eb in H1.
          inversion H1. subst. apply E_WhileFalse.
          apply Eb.
        }
Qed.

Theorem ceval_step_more : forall i1 i2 st st' c,
    i1 <= i2 ->
    ceval_step st c i1 = Some st' ->
    ceval_step st c i2 = Some st'.
Proof.
  intro i1. induction i1 as [|i1' IH].
  - intros i2 st st' c H1 H2. inversion H2.
  - intros i2 st st' c H1 H2. inversion H2.
    destruct c.
    + destruct i2. 
      * inversion H1.
      * reflexivity.
    + destruct i2.
      * inversion H1.
      * reflexivity.
    + destruct i2.
      * inversion H1.
      * simpl. destruct (ceval_step st c1 i1') eqn:E.
        { apply (IH i2) in E.
          { rewrite E. rewrite H0. apply (IH i2) in H0.
            { rewrite H0. reflexivity. }
            { apply le_S_n. apply H1. }
          }
          { apply le_S_n. apply H1. }
        }
        { inversion H0. }
    + destruct i2.
      * inversion H1.
      * destruct (beval st b) eqn:Eb.
        { simpl. rewrite Eb. rewrite H0. apply IH.
          { apply le_S_n. apply H1. }
          { apply H0. }
        }
        { simpl. rewrite Eb. rewrite H0. apply IH.
          { apply le_S_n. apply H1. }
          { apply H0. }
        }
    + destruct i2.
      * inversion H1.
      * destruct (beval st b) eqn:Eb.
        { simpl. rewrite Eb.
          destruct (ceval_step st c i1') eqn:E.
          { apply (IH i2) in E.
            { rewrite E. rewrite H0. apply (IH i2) in H0.
              { rewrite H0. reflexivity. }
              { apply le_S_n. apply H1. }
            }
            { apply le_S_n. apply H1. }
          }
          { inversion H0. }
        }
        { simpl. rewrite Eb. reflexivity. }
Qed.

Theorem ceval__ceval_step : forall c st st',
    st =[ c ]=> st' ->
    exists i, ceval_step st c i = Some st'.
Proof.
  intros c st st' Hce.
  induction Hce.
  - exists 1. reflexivity.
  - exists 1. simpl. rewrite H. reflexivity.
  - destruct IHHce1 as [m IHHce1]. destruct IHHce2 as [n IHHce2].
    exists (m + n). destruct (m + n) eqn:E.
    + Search plus. apply plus_is_O in E. destruct E.
      subst. inversion IHHce1.
    + simpl. destruct n as [| n'].
      * inversion IHHce2.
      * destruct m as [| m'] eqn:Em.
        { inversion IHHce1. }
        { assert (Hle : m <= n0).
          { rewrite Nat.add_succ_r in E.
            apply eq_add_S in E.
            rewrite <- E. rewrite <- Em. apply Nat.le_add_r.
          }
          rewrite Em in Hle. apply (ceval_step_more _ _ _ _ _ Hle) in IHHce1.
          rewrite IHHce1. apply (ceval_step_more (S n') n0).
          { rewrite Nat.add_comm in E.
            rewrite Nat.add_succ_r in E.
            apply eq_add_S in E.
            rewrite <- E. apply Nat.le_add_r.
          }
          apply IHHce2.
        }
  - destruct IHHce. exists (S x). simpl. rewrite H.
    apply H0.
  - destruct IHHce. exists (S x). simpl. rewrite H.
    apply H0.
  - exists 1. simpl. rewrite H. reflexivity.
  - destruct IHHce1 as [m IHHce1]. destruct IHHce2 as [n IHHce2].
    exists (m + n). destruct (m + n) eqn:E.
    + apply plus_is_O in E. destruct E.
      subst. inversion IHHce1.
    + simpl. rewrite H. destruct n as [| n'].
      * inversion IHHce2.
      * destruct m as [| m'] eqn:Em.
        { inversion IHHce1. }
        { assert (Hle : m <= n0).
          { rewrite Nat.add_succ_r in E.
            apply eq_add_S in E.
            rewrite <- E. rewrite <- Em. apply Nat.le_add_r.
          }
          rewrite Em in Hle. apply (ceval_step_more _ _ _ _ _ Hle) in IHHce1.
          rewrite IHHce1. apply (ceval_step_more (S n') n0).
          { rewrite Nat.add_comm in E.
            rewrite Nat.add_succ_r in E.
            apply eq_add_S in E.
            rewrite <- E. apply Nat.le_add_r.
          }
          apply IHHce2.
        }
Qed.

Theorem ceval_and_ceval_step_coincide : forall c st st',
    st =[ c ]=> st' <->
    exists i, ceval_step st c i = Some st'.
Proof.
  intros c st st'.
  split. apply ceval__ceval_step. apply ceval_step__ceval.
Qed.

Theorem ceval_deterministic' : forall c st st1 st2,
    st =[ c ]=> st1 ->
    st =[ c ]=> st2 ->
    st1 = st2.
Proof.
  intros c st st1 st2 H1 H2.
  apply (ceval__ceval_step _ _ _) in H1.
  apply (ceval__ceval_step _ _ _) in H2.
  inversion H1 as [i1 E1].
  inversion H2 as [i2 E2].
  apply (ceval_step_more i1 (i1 + i2)) in E1.
  apply (ceval_step_more i2 (i1 + i2)) in E2.
  rewrite E1 in E2. inversion E2. reflexivity.
  rewrite Nat.add_comm. apply Nat.le_add_r.
  apply Nat.le_add_r.
Qed.