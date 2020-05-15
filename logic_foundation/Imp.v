Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import omega.Omega.
From Coq Require Import Lists.List.
From Coq Require Import Strings.String.
Import ListNotations.

From LF Require Import Maps.
From Coq Require Import Logic.FunctionalExtensionality.

Module AExp.

  Inductive aexp : Type :=
  | ANum (n : nat)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp).

  Inductive bexp : Type :=
  | BTrue
  | BFalse
  | BEq (a1 a2 : aexp)
  | BLe (a1 a2 : aexp)
  | BNot (b : bexp)
  | BAnd (b1 b2 : bexp).

  Fixpoint aeval (a : aexp) : nat :=
    match a with
    | ANum n => n
    | APlus a1 a2 => (aeval a1) + (aeval a2)
    | AMinus a1 a2 => (aeval a1) - (aeval a2)
    | AMult a1 a2 => (aeval a1) * (aeval a2)
    end.

  Example test_aeval1: aeval (APlus (ANum 2) (ANum 2)) = 4.
  Proof. reflexivity. Qed.

  Fixpoint beval (b : bexp) : bool :=
    match b with
    | BTrue => true
    | BFalse => false
    | BEq a1 a2 => (aeval a1) =? (aeval a2)
    | BLe a1 a2 => (aeval a1) <=? (aeval a2)
    | BNot b1 => negb (beval b1)
    | BAnd b1 b2 => andb (beval b1) (beval b2)
    end.

  Fixpoint optimize_0plus (a:aexp) : aexp :=
    match a with
    | ANum n => ANum n
    | APlus (ANum 0) e2 => optimize_0plus e2
    | APlus e1 e2 => APlus (optimize_0plus e1) (optimize_0plus e2)
    | AMinus e1 e2 => AMinus (optimize_0plus e1) (optimize_0plus e2)
    | AMult e1 e2 => AMult (optimize_0plus e1) (optimize_0plus e2)
    end.

  Example test_optimize_0plus :
    optimize_0plus (APlus (ANum 2)
                          (APlus (ANum 0)
                                 (APlus (ANum 0) (ANum 1))))
    = APlus (ANum 2) (ANum 1).
  Proof. reflexivity. Qed.

  Example test_optimize_0plus1 :
    optimize_0plus (APlus (ANum 2) (ANum 0)) = APlus (ANum 2) (ANum 0).
  Proof. reflexivity. Qed.
  
  Theorem optimize_0plus_sound : forall a,
      aeval (optimize_0plus a) = aeval a.
  Proof.
    apply aexp_ind.
    - reflexivity.
    - intros a1 H1 a2 H2. simpl.
      destruct a1.
      + destruct n as [| n'].
        * simpl. rewrite H2. reflexivity.
        * simpl. rewrite H2. reflexivity.
      + rewrite <- H1. simpl. rewrite H2. reflexivity.
      + rewrite <- H1. simpl. rewrite H2. reflexivity.
      + rewrite <- H1. simpl. rewrite H2. reflexivity.
    - intros a1 H1 a2 H2. simpl.
      destruct a1.
      + simpl. destruct n as [| n'].
        * rewrite H2. simpl. reflexivity.
        * simpl. rewrite H2. reflexivity.
      + rewrite <- H1. simpl. rewrite H2. reflexivity.
      + rewrite <- H1. simpl. rewrite H2. reflexivity.
      + rewrite <- H1. simpl. rewrite H2. reflexivity.
    - intros a1 H1 a2 H2. simpl.
      destruct a1.
      + simpl. destruct n as [| n'].
        * rewrite H2. simpl. reflexivity.
        * simpl. rewrite H2. reflexivity.
      + rewrite <- H1. simpl. rewrite H2. reflexivity.
      + rewrite <- H1. simpl. rewrite H2. reflexivity.
      + rewrite <- H1. simpl. rewrite H2. reflexivity.
  Qed.

  Fixpoint optimize_0plus_b (b : bexp) : bexp :=
    match b with
    | BTrue | BFalse => b
    | BEq a1 a2 => BEq (optimize_0plus a1) (optimize_0plus a2)
    | BLe a1 a2 => BLe (optimize_0plus a1) (optimize_0plus a2)
    | BNot b1 => BNot (optimize_0plus_b b1)
    | BAnd b1 b2 => BAnd (optimize_0plus_b b1) (optimize_0plus_b b2)
    end.

  Theorem optimize_0plus_b_sound : forall b,
      beval (optimize_0plus_b b) = beval b.
  Proof.
    apply bexp_ind.
    - reflexivity.
    - reflexivity.
    - intros a1 a2. simpl. repeat (rewrite optimize_0plus_sound).
      reflexivity.
    - intros a1 a2. simpl. repeat (rewrite optimize_0plus_sound).
      reflexivity.
    - intros b H. simpl. rewrite H. reflexivity.
    - intros b1 H1 b2 H2. simpl. rewrite H1, H2. reflexivity.
  Qed.

  Fixpoint optimize_plus0 (a:aexp) : aexp :=
    match a with
    | ANum n => ANum n
    | APlus e1 (ANum 0) => optimize_plus0 e1
    | APlus e1 e2 => APlus (optimize_plus0 e1) (optimize_plus0 e2)
    | AMinus e1 e2 => AMinus (optimize_plus0 e1) (optimize_plus0 e2)
    | AMult e1 e2 => AMult (optimize_plus0 e1) (optimize_plus0 e2)
    end.

  Example test_optimize_plus0 :
    optimize_plus0 (APlus (ANum 2) (ANum 0)) = ANum 2.
  Proof. reflexivity. Qed.
  
  Theorem optimize_plus0_sound : forall a,
      aeval (optimize_plus0 a) = aeval a.
  Proof.
    intro a. induction a.
    - reflexivity.
    - simpl. destruct a2 eqn:Ea2.
      + destruct n as [| n'].
        * simpl. rewrite IHa1. Search plus. rewrite <- plus_n_O.
          reflexivity.
        * simpl. rewrite IHa1. reflexivity.
      + simpl in IHa2. simpl. rewrite IHa1, IHa2. reflexivity.
      + simpl in IHa2. simpl. rewrite IHa1, IHa2. reflexivity.
      + simpl in IHa2. simpl. rewrite IHa1, IHa2. reflexivity.
    - simpl. rewrite IHa1, IHa2. reflexivity.
    - simpl. rewrite IHa1, IHa2. reflexivity.
  Qed.

  Fixpoint optimize_plus0_b (b : bexp) : bexp :=
    match b with
    | BTrue | BFalse => b
    | BEq a1 a2 => BEq (optimize_plus0 a1) (optimize_plus0 a2)
    | BLe a1 a2 => BLe (optimize_plus0 a1) (optimize_plus0 a2)
    | BNot b1 => BNot (optimize_plus0_b b1)
    | BAnd b1 b2 => BAnd (optimize_plus0_b b1) (optimize_plus0_b b2)
    end.
  
  Theorem optimize_plus0_b_sound : forall b,
      beval (optimize_plus0_b b) = beval b.
  Proof.
    apply bexp_ind.
    - reflexivity.
    - reflexivity.
    - intros a1 a2. simpl. repeat (rewrite optimize_plus0_sound).
      reflexivity.
    - intros a1 a2. simpl. repeat (rewrite optimize_plus0_sound).
      reflexivity.
    - intros b H. simpl. rewrite H. reflexivity.
    - intros b1 H1 b2 H2. simpl. rewrite H1, H2. reflexivity.
  Qed.

  Reserved Notation "e '\\' n" (at level 90, left associativity).

  Inductive aevalR : aexp -> nat -> Prop :=
  | E_ANum (n : nat) :
      (ANum n) \\ n
  | E_APlus (e1 e2 : aexp) (n1 n2 : nat) :
      (e1 \\ n1) -> (e2 \\ n2) -> (APlus e1 e2) \\ (n1 + n2)
  | E_AMinus (e1 e2 : aexp) (n1 n2 : nat) :
      (e1 \\ n1) -> (e2 \\ n2) -> (AMinus e1 e2) \\ (n1 - n2)
  | E_AMult (e1 e2 : aexp) (n1 n2 : nat) :
      (e1 \\ n1) -> (e2 \\ n2) -> (AMult e1 e2) \\ (n1 * n2)
                                                
  where "e '\\' n" := (aevalR e n) : type_scope.

  Inductive bevalR : bexp -> bool -> Prop :=
  | E_BTrue : bevalR BTrue true
  | E_BFalse : bevalR BFalse false
  | E_BEq (a1 a2 : aexp) (n1 n2 : nat)
          (H1 : a1 \\ n1) (H2 : a2 \\ n2) :
      bevalR (BEq a1 a2) (n1 =? n2)
  | E_BLe (a1 a2 : aexp) (n1 n2 : nat)
          (H1 : a1 \\ n1) (H2 : a2 \\ n2) :
      bevalR (BLe a1 a2) (n1 <=? n2)
  | E_BNot (be : bexp) (b : bool)
           (H : bevalR be b) :
      bevalR (BNot be) (negb b)
  | E_BAnd (be1 be2 : bexp) (b1 b2 : bool)
           (H1 : bevalR be1 b1)
           (H2 : bevalR be2 b2) :
      bevalR (BAnd be1 be2) (andb b1 b2).

  Theorem aeval_iff_aevalR : forall a n, (a \\ n) <-> aeval a = n.
  Proof.
    intros a n. split.
    - intro H. induction H; try (simpl; subst); reflexivity.
    - generalize dependent n.
      induction a; simpl; intros n0 H; rewrite <- H; constructor;
      try (apply IHa1); try apply IHa2; reflexivity.
  Qed.

  Theorem beval_iff_bevalR : forall b bv,
      bevalR b bv <-> beval b = bv.
  Proof.
    intros b bv. split.
    - intro H. induction H.
      + reflexivity.
      + reflexivity.
      + simpl. rewrite aeval_iff_aevalR in H1.
        rewrite aeval_iff_aevalR in H2. rewrite H1. rewrite H2.
        reflexivity.
      + simpl. rewrite aeval_iff_aevalR in H1.
        rewrite aeval_iff_aevalR in H2. rewrite H1. rewrite H2.
        reflexivity.
      + simpl. rewrite IHbevalR. reflexivity.
      + simpl. rewrite IHbevalR1. rewrite IHbevalR2. reflexivity.
    - generalize dependent bv. induction b.
      + simpl. intros bv H. rewrite <- H. constructor.
      + simpl. intros bv H. rewrite <- H. constructor.
      + simpl. intros bv H. rewrite <- H.
        constructor; apply aeval_iff_aevalR; reflexivity.
      + simpl. intros bv H. rewrite <- H.
        constructor; apply aeval_iff_aevalR; reflexivity.
      + simpl. intros bv H. rewrite <- H.
        constructor. apply IHb. reflexivity.
      + simpl. intros bv H. rewrite <- H.
        constructor.
        * apply IHb1. reflexivity.
        * apply IHb2. reflexivity.
  Qed.
  
End AExp.

Module aevalR_division.

  Inductive aexp : Type :=
  | ANum (n : nat)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp)
  | ADiv (a1 a2 : aexp).

  Reserved Notation "e '\\' n"
           (at level 90, left associativity).
  Inductive aevalR : aexp -> nat -> Prop :=
  | E_ANum (n : nat) :
      (ANum n) \\ n
  | E_APlus (a1 a2 : aexp) (n1 n2 : nat) :
      (a1 \\ n1) -> (a2 \\ n2) -> (APlus a1 a2) \\ (n1 + n2)
  | E_AMinus (a1 a2 : aexp) (n1 n2 : nat) :
      (a1 \\ n1) -> (a2 \\ n2) -> (AMinus a1 a2) \\ (n1 - n2)
  | E_AMult (a1 a2 : aexp) (n1 n2 : nat) :
      (a1 \\ n1) -> (a2 \\ n2) -> (AMult a1 a2) \\ (n1 * n2)
  | E_ADiv (a1 a2 : aexp) (n1 n2 n3 : nat) :
      (a1 \\ n1) -> (a2 \\ n2) -> (n2 > 0) ->
      (mult n2 n3 = n1) -> (ADiv a1 a2) \\ n3
                                        
  where "a '\\' n" := (aevalR a n) : type_scope.
  
End aevalR_division.

Module aevalR_extended.

  Reserved Notation "e '\\' n" (at level 90, left associativity).

  Inductive aexp : Type :=
  | AAny (* <--- NEW *)
  | ANum (n : nat)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp).
  
  Inductive aevalR : aexp -> nat -> Prop :=
  | E_Any (n : nat) :
      AAny \\ n (* <--- NEW *)
  | E_ANum (n : nat) :
      (ANum n) \\ n
  | E_APlus (a1 a2 : aexp) (n1 n2 : nat) :
      (a1 \\ n1) -> (a2 \\ n2) -> (APlus a1 a2) \\ (n1 + n2)
  | E_AMinus (a1 a2 : aexp) (n1 n2 : nat) :
      (a1 \\ n1) -> (a2 \\ n2) -> (AMinus a1 a2) \\ (n1 - n2)
  | E_AMult (a1 a2 : aexp) (n1 n2 : nat) :
      (a1 \\ n1) -> (a2 \\ n2) -> (AMult a1 a2) \\ (n1 * n2)
                                              
  where "a '\\' n" := (aevalR a n) : type_scope.
  
End aevalR_extended.

Definition state := partial_map nat.

Inductive aexp : Type :=
| ANum (n : nat)
| AId (x : string)
| APlus (a1 a2 : aexp)
| AMinus (a1 a2 : aexp)
| AMult (a1 a2 : aexp).

Definition W : string := "W".
Definition X : string := "X".
Definition Y : string := "Y".
Definition Z : string := "Z".

Inductive bexp : Type :=
| BTrue
| BFalse
| BEq (a1 a2 : aexp)
| BLe (a1 a2 : aexp)
| BNot (b : bexp)
| BAnd (b1 b2 : bexp).

Coercion AId : string >-> aexp.
Coercion ANum : nat >-> aexp.

Definition bool_to_bexp (b : bool) : bexp :=
  if b then BTrue else BFalse.

Coercion bool_to_bexp : bool >-> bexp.

Declare Scope imp_scope.
Bind Scope imp_scope with aexp.
Bind Scope imp_scope with bexp.
Delimit Scope imp_scope with imp.

Notation "x + y" := (APlus x y) (at level 50, left associativity)
                    : imp_scope.
Notation "x - y" := (AMinus x y) (at level 50, left associativity)
                    : imp_scope.
Notation "x * y" := (AMult x y) (at level 40, left associativity)
                    : imp_scope.
Notation "x <= y" := (BLe x y) (at level 70, no associativity)
                     : imp_scope.
Notation "x < y" := (BLe (APlus x (ANum 1)) y) (at level 70, no associativity)
                    : imp_scope.
Notation "x >= y" := (BLe y x) (at level 70, no associativity)
                     : imp_scope.
Notation "x > y" := (BLe (APlus y (ANum 1)) x) (at level 70, no associativity)
                    : imp_scope.
Notation "x = y" := (BEq x y) (at level 70, no associativity)
                    : imp_scope.
Notation "x && y" := (BAnd x y) (at level 40, left associativity)
                     : imp_scope.
Notation "'~' b" := (BNot b) (at level 75, right associativity)
                    : imp_scope.

Definition example_aexp := (3 + (X * 2))%imp.
Check example_aexp.
Definition example_bexp := (true && ~(X <= 4))%imp.
Check example_bexp.

Set Printing Coercions.

Print example_bexp.
Print example_aexp.

Unset Printing Coercions.

Fixpoint aeval (st : state) (a : aexp) : nat :=
  match a with
  | ANum n => n
  | AId x => match st x with None => 0 | Some n => n end
  | APlus a1 a2 => (aeval st a1) + (aeval st a2)
  | AMinus a1 a2 => (aeval st a1) - (aeval st a2)
  | AMult a1 a2 => (aeval st a1) * (aeval st a2)
  end.

Fixpoint beval (st : state) (b : bexp) : bool :=
  match b with
  | BTrue => true
  | BFalse => false
  | BEq a1 a2 => (aeval st a1) =? (aeval st a2)
  | BLe a1 a2 => (aeval st a1) <=? (aeval st a2)
  | BNot b1 => negb (beval st b1)
  | BAnd b1 b2 => andb (beval st b1) (beval st b2)
  end.

Example aexp1 : aeval (X |-> 5) ( 3 + (X * 2))%imp = 13.
Proof. reflexivity. Qed.

Example bexp1 : beval (X |-> 5) (true && ~(X <= 4))%imp = true.
Proof. reflexivity. Qed.

Inductive com : Type :=
| CSkip
| CAss (x : string) (a : aexp)
| CSeq (c1 c2 : com)
| CIf (b : bexp) (c1 c2 : com)
| CWhile (b : bexp) (c : com).

Bind Scope imp_scope with com.

Notation "'SKIP'" := CSkip : imp_scope.
Notation "x '::=' a" := (CAss x a) (at level 60) : imp_scope.
Notation "c1 ;; c2" := (CSeq c1 c2) (at level 80, right associativity)
                      : imp_scope.
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity) : imp_scope.
Notation "'TEST' c1 'THEN' c2 'ELSE' c3 'FI'" :=
  (CIf c1 c2 c3) (at level 80, right associativity) : imp_scope.

Definition fact_in_coq : com :=
  (
    Z ::= X;;
    Y ::= 1;;
    WHILE ~(Z = 0) DO
      Y ::= Y * Z;;
      Z ::= Z - 1
    END    
  )%imp.

Print fact_in_coq.
Unset Printing Notations.
Print fact_in_coq.
Set Printing Notations.

Set Printing Coercions.
Print fact_in_coq.
Unset Printing Coercions.
Locate aexp.

Definition plus2 : com :=
  X ::= X + 2.

Definition XtimesYinZ : com :=
  Z ::= X * Y.

Definition subtract_slowly_body : com :=
  Z ::= Z - 1;;
  X ::= X - 1.

Definition subtract_slowly : com :=
  (WHILE ~(X = 0) DO
    subtract_slowly_body
   END)%imp.

Definition subtract_3_from_5_slowly : com :=
  X ::= 3 ;;
  Z ::= 5 ;;
  subtract_slowly.

Definition loop : com :=
  WHILE true DO
    SKIP
  END.

Reserved Notation "st '=[' c ']=>' st'" (at level 40).

Inductive ceval : com -> state -> state -> Prop :=
| E_Skip : forall st, st =[ SKIP ]=> st
| E_Ass : forall st a1 n x,
    aeval st a1 = n ->
    st =[ x ::= a1 ]=> (x |->n ; st)
| E_Seq : forall c1 c2 st st' st'',
    st =[ c1 ]=> st' ->
    st' =[ c2 ]=> st'' ->
    st =[ c1 ;; c2]=> st''
| E_IfTrue : forall st st' b c1 c2,
    beval st b = true ->
    st =[ c1 ]=> st' ->
    st =[ TEST b THEN c1 ELSE c2 FI]=> st'
| E_IfFalse : forall st st' b c1 c2,
    beval st b = false ->
    st =[ c2 ]=> st' ->
    st =[ TEST b THEN c1 ELSE c2 FI]=> st'
| E_WhileFalse : forall b st c,
    beval st b = false ->
    st =[ WHILE b DO c END ]=> st
| E_WhileTrue : forall b st st' st'' c,
    beval st b = true ->
    st =[ c ]=> st' ->
    st' =[ WHILE b DO c END ]=> st'' ->
    st =[ WHILE b DO c END]=> st''
where "st =[ c ]=> st'" := (ceval c st st').

Definition empty_st := @empty nat.

Example ceval_example1 :
  empty_st =[
    X ::= 2;;
      TEST X <= 1
        THEN Y ::= 3
        ELSE Z ::= 4
      FI
  ]=> (Z |-> 4; X |-> 2).
Proof.
  apply (E_Seq _ _ _ (X |-> 2)).
  - apply E_Ass. reflexivity.
  - apply E_IfFalse.
    + reflexivity.
    + apply E_Ass. reflexivity.
Qed.

Example ceval_example2 :
  empty_st =[
    X ::= 0;; Y ::= 1;; Z ::= 2
  ]=> (Z |-> 2; Y |-> 1; X |-> 0).
Proof.
  apply (E_Seq _ _ _ (X |-> 0)).
  - apply E_Ass. reflexivity.
  - apply (E_Seq _ _ _ (Y |-> 1; X |-> 0)); apply E_Ass; reflexivity.
Qed.

Definition pup_to_n : com :=
  Y ::= 0;;
  WHILE X > 0 DO
    Y ::= Y + X;;
    X ::= X - 1
  END.

Theorem pup_to_2_ceval :
  (X |-> 2) =[
    pup_to_n
  ]=> (X |-> 0; Y |-> 3; X |-> 1; Y |-> 2; Y |-> 0; X |-> 2).
Proof.
  unfold pup_to_n.
  apply (E_Seq _ _ _ (Y |-> 0; X |-> 2)).
  - apply E_Ass; reflexivity.
  - apply E_WhileTrue with (X |-> 1; Y |-> 2; Y |-> 0; X |-> 2).
    + reflexivity.
    + apply E_Seq with (Y |-> 2; Y |-> 0; X |-> 2).
      * apply E_Ass; reflexivity.
      * apply E_Ass; reflexivity.
    + apply E_WhileTrue with (X |-> 0; Y |-> 3; X |-> 1; Y |-> 2; Y |-> 0; X |-> 2).
      * reflexivity.
      * apply E_Seq with (Y |-> 3; X |-> 1; Y |-> 2; Y |-> 0; X |-> 2).
        { apply E_Ass; reflexivity. }
        { apply E_Ass; reflexivity. }
      * apply E_WhileFalse. reflexivity.
Qed.

Theorem ceval_deterministic : forall c st st1 st2,
    st =[ c ]=> st1 ->
    st =[ c ]=> st2 ->
    st1 = st2.
Proof.
  intros c st st1 st2 H1.
  generalize dependent st2.
  induction H1.
  - intros st2 H2. inversion H2. reflexivity.
  - intros st2 H2. inversion H2. subst. reflexivity.
  - intros st2 H2. inversion H2.
    apply IHceval1 in H1. rewrite <- H1 in H5.
    apply IHceval2 in H5. apply H5.
  - intros st2 H2. inversion H2.
    + apply IHceval. apply H8.
    + rewrite H in H7. discriminate H7.
  - intros st2 H2. inversion H2.
    + rewrite H in H7. discriminate H7.
    + apply IHceval. apply H8.
  - intros st2 H2. inversion H2.
    + reflexivity.
    + rewrite H in H3. discriminate H3.
  - intros st2 H2. inversion H2.
    + subst. rewrite H in H5. discriminate H5.
    + apply IHceval1 in H4. apply IHceval2.
      subst. apply H7.
Qed.

Theorem plus2_spec : forall st n st',
    st X = Some n ->
    st =[ plus2 ]=> st' ->
    st' X = Some (n + 2).
Proof.
  intros st n st' H1 H2. inversion H2.
  simpl in H5. rewrite H1 in H5. subst.
  apply update_eq.
Qed.

Theorem XtimesYinZ_spec : forall st m n st',
    st X = Some m ->
    st Y = Some n ->
    st =[ XtimesYinZ ]=> st' ->
    st' Z = Some (m * n).
Proof.
  intros st m n st' H1 H2 H3.
  inversion H3. simpl in H6. rewrite H1 in H6. rewrite H2 in H6.
  subst. apply update_eq.
Qed.

Theorem loop_never_stops : forall st st',
    ~(st =[ loop ]=> st').
Proof.
  intros st st' constra. unfold loop in constra.
  remember (WHILE true DO SKIP END)%imp as loopdef eqn:Heqloopdef.
  induction constra.
  - inversion Heqloopdef.
  - inversion Heqloopdef.
  - inversion Heqloopdef.
  - inversion Heqloopdef.
  - inversion Heqloopdef.
  - inversion Heqloopdef. rewrite H1 in H. simpl in H. discriminate H.
  - apply IHconstra2. apply Heqloopdef.
Qed.

Open Scope imp_scope.

Fixpoint no_whiles (c : com) : bool :=
  match c with
  | SKIP => true
  | _ ::= _ => true
  | c1 ;; c2 =>
    andb (no_whiles c1) (no_whiles c2)
  | TEST _ THEN ct ELSE cf FI =>
    andb (no_whiles ct) (no_whiles cf)
  | WHILE _ DO _ END => false
  end.

Close Scope imp_scope.

Inductive no_whilesR : com -> Prop :=
| NW_Skip : no_whilesR SKIP
| NW_Ass (x : string) (a : aexp) : no_whilesR (x ::= a)
| NW_Seq (c1 c2 : com) (H1 : no_whilesR c1) (H2 : no_whilesR c2) :
    no_whilesR (c1 ;; c2)
| NW_SIf (b : bexp) (ct cf : com) (H1 : no_whilesR ct) (H2 : no_whilesR cf) :
    no_whilesR (TEST b THEN ct ELSE cf FI).

Theorem no_whiles_eqv :
  forall c, no_whiles c = true <-> no_whilesR c.
Proof.
  intro c. split.
  - intro H. induction c.
    + constructor.
    + constructor.
    + simpl in H. rewrite andb_true_iff in H. destruct H.
      constructor.
      * apply IHc1. assumption.
      * apply IHc2. assumption.
    + simpl in H. rewrite andb_true_iff in H. destruct H.
      constructor.
      * apply IHc1. assumption.
      * apply IHc2. assumption.
    + simpl in H. discriminate H.
  - intro H. induction H.
    + reflexivity.
    + reflexivity.
    + simpl. rewrite andb_true_iff. split; assumption.
    + simpl. rewrite andb_true_iff. split; assumption.
Qed.

Theorem no_whiles_terminating : forall c st,
    no_whilesR c ->
    exists st', st =[ c ]=> st'.
Proof.
  intros c st H. generalize dependent st.
  induction H.
  - eexists. constructor.
  - eexists. eapply E_Ass. eexists.
  - intro st. destruct IHno_whilesR1 with st.
    destruct IHno_whilesR2 with x.
    exists x0. apply E_Seq with x; assumption.
  - intro st. destruct IHno_whilesR1 with st.
    destruct IHno_whilesR2 with st.
    destruct (beval st b) eqn:Eb.
    + exists x. apply E_IfTrue.
      * apply Eb.
      * apply H1.
    + exists x0. apply E_IfFalse.
      * apply Eb.
      * apply H2.
Qed.

Inductive sinstr : Type :=
| SPush (n : nat)
| SLoad (x : string)
| SPlus
| SMinus
| SMult.

Fixpoint s_execute (st : state) (stack : list nat) (prog : list sinstr)
  : list nat :=
  match prog with
  | [] => stack
  | hd :: tl =>
    match hd with
    | SPush n => s_execute st (n :: stack) tl
    | SLoad x => match st x with
                 | None => s_execute st (0 :: stack) tl
                 | Some n => s_execute st (n :: stack) tl
                 end
    | SPlus => match stack with
               | m :: n :: stack' =>
                 s_execute st ((n + m) :: stack') tl
               | _ => []
               end
    | SMinus => match stack with
               | m :: n :: stack' =>
                 s_execute st ((n - m) :: stack') tl
               | _ => []
                end
    | SMult => match stack with
                | m :: n :: stack' =>
                  s_execute st ((n * m) :: stack') tl
                | _ => []
               end
    end
  end.

Example s_execute1 :
  s_execute empty_st [] [SPush 5; SPush 3; SPush 1; SMinus] = [2; 5].
Proof. reflexivity. Qed.

Example s_execute2 :
  s_execute (X |-> 3) [3; 4] [SPush 4; SLoad X; SMult; SPlus]
  = [15; 4].
Proof. reflexivity. Qed.

Fixpoint s_compile (e : aexp) : list sinstr :=
  match e with
  | ANum n => [SPush n]
  | AId x => [SLoad x]
  | APlus a1 a2 => (s_compile a1) ++ (s_compile a2) ++ [SPlus]
  | AMinus a1 a2 => (s_compile a1) ++ (s_compile a2) ++ [SMinus]
  | AMult a1 a2 => (s_compile a1) ++ (s_compile a2) ++ [SMult]
  end.

Example s_compile1 :
  s_compile (X - (2 * Y))%imp
  = [SLoad X; SPush 2; SLoad Y; SMult; SMinus].
Proof. reflexivity. Qed.

Theorem s_compile_correct_help :
  forall (st : state) (e : aexp) (stack : list nat) (l : list sinstr),
    s_execute st stack ((s_compile e) ++ l) =
    s_execute st ((aeval st e) :: stack) l.
Proof.
  intros st e. induction e.
  - reflexivity.
  - simpl. destruct (st x); reflexivity.
  - simpl. intros stack l.
    assert (eq : (s_compile e1 ++ s_compile e2 ++ [SPlus]) ++ l
                 = s_compile e1 ++ (s_compile e2 ++ [SPlus] ++ l)).
    { repeat (rewrite app_assoc_reverse). reflexivity. }
    rewrite eq.
    rewrite (IHe1 stack (s_compile e2 ++ [SPlus] ++ l)).
    rewrite (IHe2 (aeval st e1 :: stack) ([SPlus] ++ l)).
    simpl. reflexivity.
  - simpl. intros stack l.
    assert (eq : (s_compile e1 ++ s_compile e2 ++ [SMinus]) ++ l
                 = s_compile e1 ++ (s_compile e2 ++ [SMinus] ++ l)).
    { repeat (rewrite app_assoc_reverse). reflexivity. }
    rewrite eq.
    rewrite (IHe1 stack (s_compile e2 ++ [SMinus] ++ l)).
    rewrite (IHe2 (aeval st e1 :: stack) ([SMinus] ++ l)).
    simpl. reflexivity.
  - simpl. intros stack l.
    assert (eq : (s_compile e1 ++ s_compile e2 ++ [SMult]) ++ l
                 = s_compile e1 ++ (s_compile e2 ++ [SMult] ++ l)).
    { repeat (rewrite app_assoc_reverse). reflexivity. }
    rewrite eq.
    rewrite (IHe1 stack (s_compile e2 ++ [SMult] ++ l)).
    rewrite (IHe2 (aeval st e1 :: stack) ([SMult] ++ l)).
    simpl. reflexivity.
Qed.

Theorem s_compile_correct : forall (st : state) (e : aexp),
    s_execute st [] (s_compile e) = [ aeval st e ].
Proof.
  intros st e.
  assert (eq : s_compile e = (s_compile e) ++ []).
  { rewrite app_nil_r. reflexivity. }
  rewrite eq.
  apply (s_compile_correct_help st e [] []).
Qed.

Fixpoint beval_short (st : state) (b : bexp) : bool :=
  match b with
  | BTrue => true
  | BFalse => false
  | BEq a1 a2 => (aeval st a1) =? (aeval st a2)
  | BLe a1 a2 => (aeval st a1) <=? (aeval st a2)
  | BNot b1 => negb (beval_short st b1)
  | BAnd b1 b2 => if beval_short st b1 then beval_short st b2 else false
  end.

Theorem beval_eq_beval_short : beval = beval_short.
Proof.
  apply functional_extensionality.
  intro st.
  apply functional_extensionality.
  intro b.
  induction b.
  - reflexivity.
  - reflexivity.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. rewrite IHb. reflexivity.
  - simpl. rewrite IHb1. rewrite IHb2.
    destruct (beval_short st b1) eqn:E.
    + simpl. reflexivity.
    + simpl. reflexivity.
Qed.

Module BreakImp.

  Inductive com : Type :=
  | CSkip
  | CBreak
  | CAss (x : string) (a : aexp)
  | CSeq (c1 c2 : com)
  | CIf (b : bexp) (c1 c2 : com)
  | CWhile (b : bexp) (c : com).

  Notation "'SKIP'" :=
    CSkip.
  Notation "'BREAK'" :=
    CBreak.
  Notation "x '::=' a" :=
    (CAss x a) (at level 60).
  Notation "c1 ;; c2" :=
    (CSeq c1 c2) (at level 80, right associativity).
  Notation "'WHILE' b 'DO' c 'END'" :=
    (CWhile b c) (at level 80, right associativity).
  Notation "'TEST' c1 'THEN' c2 'ELSE' c3 'FI'" :=
    (CIf c1 c2 c3) (at level 80, right associativity).

  Inductive result : Type :=
  | SContinue
  | SBreak.
  
  Reserved Notation "st '=[' c ']=>' st' '/' s"
           (at level 40, st' at next level).

  Inductive ceval : com -> state -> result -> state -> Prop :=
  | E_Skip : forall st, st =[ SKIP ]=> st / SContinue
  | E_Break : forall st, st =[ BREAK ]=> st / SBreak
  | E_Ass : forall st x a n,
      aeval st a = n ->
      st =[ x ::= a ]=> (x |-> n; st) / SContinue
  | E_Seq_Continue : forall st st' st'' r c1 c2,
      st =[ c1 ]=> st' / SContinue ->
      st' =[ c2 ]=> st'' / r ->
      st =[ c1 ;; c2 ]=> st'' / r
  | E_Seq_Break : forall st st' c1 c2,
      st =[ c1 ]=> st' / SBreak ->
      st =[ c1 ;; c2 ]=> st' / SBreak 
  | E_IfTrue : forall st st' b r c1 c2,
      beval st b = true ->
      st =[ c1 ]=> st' / r ->
      st =[ TEST b THEN c1 ELSE c2 FI]=> st' / r
  | E_IfFalse : forall st st' b r c1 c2,
      beval st b = false ->
      st =[ c2 ]=> st' / r ->
      st =[ TEST b THEN c1 ELSE c2 FI]=> st' / r
  | E_WhileFalse : forall b st c,
      beval st b = false ->
      st =[ WHILE b DO c END ]=> st / SContinue
  | E_WhileTrue_Break : forall b st st' c,
      beval st b = true ->
      st =[ c ]=> st' / SBreak ->
      st =[ WHILE b DO c END ]=> st' / SContinue
  | E_WhileTrue_Continue : forall b st st' st'' r c,
      beval st b = true ->
      st =[ c ]=> st' / SContinue ->
      st' =[ WHILE b DO c END ]=> st'' / r ->
      st =[ WHILE b DO c END ]=> st'' / r
                                                                  
  where "st '=[' c ']=>' st' '/' s" := (ceval c st s st').
  
  Theorem break_ignore : forall c st st' s,
      st =[ BREAK ;; c]=> st' / s ->
      st = st'.
  Proof.
    intros c st st' s H. inversion H.
    - inversion H2.
    - inversion H5. reflexivity.
  Qed.

  Theorem while_continue : forall b c st st' s,
      st =[ WHILE b DO c END ]=> st' / s ->
      s = SContinue.
  Proof.
    intros b c st st' s. destruct s.
    - intros. reflexivity.
    - intro H. remember (WHILE b DO c END) as while eqn:Heqwhile.
      induction H; try reflexivity; try (inversion Heqwhile).
      apply IHceval2. apply Heqwhile.
  Qed.

  Theorem while_stops_on_break : forall b c st st',
      beval st b = true ->
      st =[ c ]=> st' / SBreak ->
      st =[ WHILE b DO c END ]=> st' / SContinue.
  Proof.
    intros b c st st' H1 H2. constructor; assumption.
  Qed.

  Theorem while_break_true : forall b c st st',
      st =[ WHILE b DO c END ]=> st' / SContinue ->
      beval st' b = true ->
      exists st'', st'' =[ c ]=> st' / SBreak.
  Proof.
    intros b c st st' H1 H2. remember (WHILE b DO c END) as while eqn:Heqwhile.
    induction H1.
    - inversion Heqwhile.
    - inversion Heqwhile.
    - inversion Heqwhile.
    - inversion Heqwhile.
    - inversion Heqwhile.
    - inversion Heqwhile.
    - inversion Heqwhile.
    - inversion Heqwhile. subst. rewrite H in H2. discriminate H2.
    - inversion Heqwhile. subst. exists st. apply H1.
    - apply IHceval2.
      + apply Heqwhile.
      + apply H2.
  Qed.

  Theorem ceval_deterministic : forall (c : com) st st1 st2 s1 s2,
      st =[ c ]=> st1 / s1 ->
      st =[ c ]=> st2 / s2 ->
      st1 = st2 /\ s1 = s2.
  Proof.
    intros c st st1 st2 s1 s2 H1.
    generalize dependent s2.
    generalize dependent st2.
    induction H1.
    - intros st2 s2 H2. inversion H2. split; reflexivity.
    - intros st2 s2 H2. inversion H2. split; reflexivity.
    - intros st2 s2 H2. inversion H2. subst; split; reflexivity.
    - intros st2 s2 H2. inversion H2.
      + subst.
        apply IHceval2. apply IHceval1 in H1.
        destruct H1. subst. apply H6.
      + subst. apply IHceval1 in H5. destruct H5. inversion H0.
    - intros st2 s2 H2. inversion H2.
      + subst. apply IHceval in H3. destruct H3. inversion H0.
      + subst. apply IHceval. apply H6.
    - intros st2 s2 H2. inversion H2.
      + subst. apply IHceval. apply H9.
      + rewrite H in H8. discriminate H8.
    - intros st2 s2 H2. inversion H2.
      + rewrite H in H8. discriminate H8.
      + subst. apply (IHceval _ _ H9).
    - intros st2 s2 H2. inversion H2.
      + split; reflexivity.
      + rewrite H in H3. discriminate H3.
      + rewrite H in H3. discriminate H3.
    - intros st2 s2 H2. inversion H2.
      + subst. rewrite H in H7. discriminate H7.
      + subst. apply IHceval in H8. destruct H8.
        split.
        * apply H0.
        * reflexivity.
      + subst. apply IHceval in H5. destruct H5. inversion H3.
    - intros st2 s2 H2. inversion H2.
      + subst. rewrite H in H6. discriminate H6.
      + subst. apply IHceval1 in H7. destruct H7. inversion H1.
      + subst. apply IHceval1 in H4. destruct H4. clear H1.
        subst. apply IHceval2. apply H8.
  Qed.

End BreakImp.

Module ForLoopImp.

  Inductive com : Type :=
  | CSkip
  | CBreak
  | CAss (x : string) (a : aexp)
  | CSeq (c1 c2 : com)
  | CIf (b : bexp) (c1 c2 : com)
  | CWhile (b : bexp) (c : com)
  | CFor (c1 c2 c3 : com) (b : bexp).

  Notation "'SKIP'" :=
    CSkip.
  Notation "'BREAK'" :=
    CBreak.
  Notation "x '::=' a" :=
    (CAss x a) (at level 60).
  Notation "c1 ;; c2" :=
    (CSeq c1 c2) (at level 80, right associativity).
  Notation "'WHILE' b 'DO' c 'END'" :=
    (CWhile b c) (at level 80, right associativity).
  Notation "'TEST' c1 'THEN' c2 'ELSE' c3 'FI'" :=
    (CIf c1 c2 c3) (at level 80, right associativity).
  Notation "'FOR' c1 ; b ; c2 'DO' c3 'END'" :=
    (CFor c1 c2 c3 b) (at level 80, right associativity).
  
  Inductive result : Type :=
  | SContinue
  | SBreak.
  
  Reserved Notation "st '=[' c ']=>' st' '/' s"
           (at level 40, st' at next level).

  Inductive ceval : com -> state -> result -> state -> Prop :=
  | E_Skip : forall st, st =[ SKIP ]=> st / SContinue
  | E_Break : forall st, st =[ BREAK ]=> st / SBreak
  | E_Ass : forall st x a n,
      aeval st a = n ->
      st =[ x ::= a ]=> (x |-> n; st) / SContinue
  | E_Seq_Continue : forall st st' st'' r c1 c2,
      st =[ c1 ]=> st' / SContinue ->
      st' =[ c2 ]=> st'' / r ->
      st =[ c1 ;; c2 ]=> st'' / r
  | E_Seq_Break : forall st st' c1 c2,
      st =[ c1 ]=> st' / SBreak ->
      st =[ c1 ;; c2 ]=> st' / SBreak 
  | E_IfTrue : forall st st' b r c1 c2,
      beval st b = true ->
      st =[ c1 ]=> st' / r ->
      st =[ TEST b THEN c1 ELSE c2 FI]=> st' / r
  | E_IfFalse : forall st st' b r c1 c2,
      beval st b = false ->
      st =[ c2 ]=> st' / r ->
      st =[ TEST b THEN c1 ELSE c2 FI]=> st' / r
  | E_WhileFalse : forall b st c,
      beval st b = false ->
      st =[ WHILE b DO c END ]=> st / SContinue
  | E_WhileTrue_Break : forall b st st' c,
      beval st b = true ->
      st =[ c ]=> st' / SBreak ->
      st =[ WHILE b DO c END ]=> st' / SContinue
  | E_WhileTrue_Continue : forall b st st' st'' r c,
      beval st b = true ->
      st =[ c ]=> st' / SContinue ->
      st' =[ WHILE b DO c END ]=> st'' / r ->
      st =[ WHILE b DO c END ]=> st'' / r
  | E_For : forall b st st' c1 c2 c3 r,
      st =[ c1 ;; WHILE b DO c2;; c3 END ]=> st' / r ->
      st =[ FOR c1 ; b ; c3 DO c2 END ]=> st' / r           
                                                                  
  where "st '=[' c ']=>' st' '/' s" := (ceval c st s st').

End ForLoopImp.