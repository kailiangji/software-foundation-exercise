Set Warnings "-notation-overridden,-parsing".
Add LoadPath "/Users/jikl/demos/coq/software-foundation-exercise/logic_foundation" as LF.
From Coq Require Import Bool.Bool.
From LF Require Import Maps.
From PLF Require Import SmallStep.
From PLF Require Import Stlc.
From PLF Require MoreStlc.

Module STLCTypes.
  Export STLC.

  Fixpoint eqb_ty (T1 T2 : ty) : bool :=
    match T1, T2 with
    | Bool, Bool => true
    | Arrow T11 T12, Arrow T21 T22 =>
      andb (eqb_ty T11 T21) (eqb_ty T12 T22)
    | _, _ => false
    end.

  Lemma eqb_ty_refl : forall T1,
      eqb_ty T1 T1 = true.
  Proof.
    intro T1. induction T1.
    - reflexivity.
    - simpl. rewrite IHT1_1, IHT1_2. reflexivity.
  Qed.

  Lemma eqb_ty__eq : forall T1 T2,
      eqb_ty T1 T2 = true -> T1 = T2.
  Proof.
    intro T1. induction T1.
    - intro T2. induction T2.
      + reflexivity.
      + intro H. inversion H.
    - intro T2. induction T2.
      + intro H. inversion H.
      + intro H. inversion H.
        Search andb.
        apply andb_prop in H1.
        destruct H1 as [H1 H2].
        apply IHT1_1 in H1.
        apply IHT1_2 in H2.
        subst. reflexivity.
  Qed.

End STLCTypes.

Module FirstTry.
  Import STLCTypes.

  Fixpoint type_check (Gamma : context ) (t : tm) : option ty :=
    match t with
    | var x => Gamma x
    | abs x T11 t12 =>
      match type_check (update Gamma x T11) t12 with
      | Some T12 => Some (Arrow T11 T12)
      | _ => None
      end
    | app t1 t2 =>
      match type_check Gamma t1, type_check Gamma t2 with
      | Some (Arrow T11 T12), Some T2 =>
        if eqb_ty T11 T2 then Some T12 else None
      | _, _ => None
      end
    | tru | fls => Some Bool
    | test guard t f =>
      match type_check Gamma guard with
      | Some Bool =>
        match type_check Gamma t, type_check Gamma f with
        | Some T1, Some T2 =>
          if eqb_ty T1 T2 then Some T1 else None
        | _, _ => None
        end
      | _ => None
      end
    end.
  
End FirstTry.

Notation " x <- e1 ;; e2" := (match e1 with
                              | Some x => e2
                              | None => None
                              end)
                               (right associativity, at level 60).

Notation " 'return' e " := (Some e) (at level 60).

Notation " 'fail' " := None.

Module STLCChecker.
  Import STLCTypes.

  Fixpoint type_check (Gamma : context) (t : tm) : option ty :=
    match t with
    | var x =>
      match Gamma x with
      | Some T => return T
      | None => fail
      end
    | abs x T11 t12 =>
      T12 <- type_check (update Gamma x T11) t12 ;;
    return (Arrow T11 T12)
    | app t1 t2 =>
      T1 <- type_check Gamma t1 ;;
      T2 <- type_check Gamma t2 ;;
      match T1 with
      | Arrow T11 T12 =>
        if eqb_ty T11 T2 then return T12 else fail
      | _ => fail
      end
    | tru | fls => return Bool
    | test guard t1 t2 =>
      Tguard <- type_check Gamma guard ;;
      T1 <- type_check Gamma t1 ;;
      T2 <- type_check Gamma t2 ;;
      match Tguard with
      | Bool =>
        if eqb_ty T1 T2 then return T1 else fail
      | _ => fail
      end
    end.

  Theorem type_checking_sound : forall Gamma t T,
      type_check Gamma t = Some T -> has_type Gamma t T.
  Proof with eauto with db.
    intros Gamma t. generalize dependent Gamma.
    induction t; intros Gamma T Htc; inversion Htc.
    - rename s into x. destruct (Gamma x) eqn:H.
      rename t into T'. inversion H0; subst.
      + apply T_Var...
      + inversion H0.
    - (* app *)
      remember (type_check Gamma t1) as TO1.
      destruct TO1 as [T1 |]; try solve_by_invert.
      destruct T1 as [|T11 T12]; try solve_by_invert;
      remember (type_check Gamma t2) as TO2;
      destruct TO2 as [T2 |]; try solve_by_invert.
      destruct (eqb_ty T11 T2) eqn: Heqb.
      apply eqb_ty__eq in Heqb.
      inversion H0; subst...
      inversion H0.
    - rename s into x. rename t into T1.
      remember (x |-> T1; Gamma) as G'.
      remember (type_check G' t0) as TO2.
      destruct TO2; try solve_by_invert.
      inversion H0; subst...
    - eauto with db.
    - eauto with db.
    - remember (type_check Gamma t1) as TOc.
      remember (type_check Gamma t2) as TO1.
      remember (type_check Gamma t3) as TO2.
      destruct TOc as [Tc|]; try solve_by_invert.
      destruct Tc; try solve_by_invert;
        destruct TO1 as [T1|]; try solve_by_invert;
          destruct TO2 as [T2|]; try solve_by_invert.
      destruct (eqb_ty T1 T2) eqn:Heqb;
        try solve_by_invert.
      apply eqb_ty__eq in Heqb.
      inversion H0. subst. subst...
  Qed.

  Theorem type_checking_complete : forall Gamma t T,
      has_type Gamma t T -> type_check Gamma t = Some T.
  Proof with auto with db.
    intros Gamma t T Hty.
    induction Hty; simpl.
    - destruct (Gamma x0) eqn:H0; assumption.
    - rewrite IHHty...
    - rewrite IHHty1. rewrite IHHty2.
      rewrite (eqb_ty_refl T11)...
    - reflexivity.
    - reflexivity.
    - rewrite IHHty1. rewrite IHHty2.
      rewrite IHHty3. rewrite (eqb_ty_refl T)...
  Qed.

End STLCChecker.

Module TypecheckerExtensions.

  Definition manual_grade_for_type_checking_sound : option (nat * string) :=
    None.

  Definition manual_grade_for_type_checking_complete : option (nat * string) := None.

  Import MoreStlc.
  Import STLCExtended.

  Fixpoint eqb_ty (T1 T2 : ty) : bool :=
    match T1, T2 with
    | Nat, Nat => true
    | Unit, Unit => true
    | Arrow T11 T12, Arrow T21 T22 =>
      (eqb_ty T11 T21) && (eqb_ty T12 T22)
    | Prod T11 T12, Prod T21 T22 =>
      (eqb_ty T11 T21) && (eqb_ty T12 T22)
    | Sum T11 T12, Sum T21 T22 =>
      (eqb_ty T11 T21) && (eqb_ty T12 T22)
    | List T11, List T21 => eqb_ty T11 T21
    | _, _ => false
    end.

  Lemma eqb_ty_refl : forall T1,
      eqb_ty T1 T1 = true.
  Proof.
    intro T1.
    induction T1; simpl.
    - rewrite IHT1_1, IHT1_2. auto.
    - auto.
    - rewrite IHT1_1, IHT1_2. auto.
    - assumption.
    - auto.
    - rewrite IHT1_1, IHT1_2. auto.
  Qed.

  Lemma eqb_ty__eq : forall T1 T2,
  eqb_ty T1 T2 = true -> T1 = T2.
  Proof.
    intros T1.
    induction T1; intros T2 Hbeq; destruct T2; inversion Hbeq;
      try reflexivity;
      try (rewrite andb_true_iff in H0; inversion H0 as [Hbeq1 Hbeq2];
           apply IHT1_1 in Hbeq1; apply IHT1_2 in Hbeq2; subst; auto);
      try (apply IHT1 in Hbeq; subst; auto).
  Qed.

  Fixpoint type_check (Gamma : context) (t : tm) : option ty :=
  match t with
  | var x =>
      match Gamma x with
      | Some T => return T
      | None => fail
      end
  | abs x1 T1 t2 =>
      T2 <- type_check (update Gamma x1 T1) t2 ;;
      return (Arrow T1 T2)
  | app t1 t2 =>
      T1 <- type_check Gamma t1 ;;
      T2 <- type_check Gamma t2 ;;
      match T1 with 
      | Arrow T11 T12 =>
          if eqb_ty T11 T2 then return T12 else fail
      | _ => fail
      end
  | const _ =>
      return Nat
  | scc t1 =>
      T1 <- type_check Gamma t1 ;;
      match T1 with 
      | Nat => return Nat
      | _ => fail
      end
  | prd t1 =>
      T1 <- type_check Gamma t1 ;;
      match T1 with 
      | Nat => return Nat
      | _ => fail
      end
  | mlt t1 t2 =>
      T1 <- type_check Gamma t1 ;;
      T2 <- type_check Gamma t2 ;;
      match T1, T2 with
      | Nat, Nat => return Nat
      | _,_ => fail
      end
  | test0 guard t f =>
      Tguard <- type_check Gamma guard ;;
      T1 <- type_check Gamma t ;;
      T2 <- type_check Gamma f ;;
      match Tguard with
      | Nat => if eqb_ty T1 T2 then return T1 else fail
      | _ => fail
      end
  | tinl T t =>
    T1 <- type_check Gamma t;;
      return (Sum T1 T)
  | tinr T t =>
    T2 <- type_check Gamma t;;
      return (Sum T T2)
  | tcase t0 x1 t1 x2 t2 =>
    T0 <- type_check Gamma t0 ;;
    match T0 with
    | Sum T01 T02 =>
      T1 <- type_check (x1 |-> T01; Gamma) t1 ;;
      T2 <- type_check (x2 |-> T02; Gamma) t2 ;;
      if eqb_ty T1 T2 then return T1 else fail
    | _ => fail
    end
  | tnil T => return (List T)
  | tcons t1 t2 =>
    T1 <- type_check Gamma t1 ;;
    T2 <- type_check Gamma t2 ;;
    match T2 with
    | List T3 =>
      if eqb_ty T1 T3 then return T2 else fail
    | _ => fail
    end
  | tlcase t0 t1 x21 x22 t2 =>
    match type_check Gamma t0 with
    | Some (List T) =>
      T1' <- type_check Gamma t1 ;;
      T2' <- type_check (x21 |-> T; x22 |-> (List T); Gamma) t2 ;;
      if eqb_ty T1' T2' then return T1' else fail
    | _ => fail
    end
  (* unit *)
  | unit => return Unit
  (* pairs *)
  | tpair t1 t2 =>
    T1 <- type_check Gamma t1 ;;
    T2 <- type_check Gamma t2 ;;
      return (Prod T1 T2)
  | tfst t =>
    T <- type_check Gamma t ;;
    match T with
    | Prod T1 T2 => return T1
    | _ => fail
    end
  | tsnd t =>
    T <- type_check Gamma t ;;
    match T with
    | Prod T1 T2 => return T2
    | _ => fail
    end
  | tlet x t1 t2 =>
    T1 <- type_check Gamma t1 ;;
    type_check (x |-> T1; Gamma) t2
  | tfix t1 =>
    T <- type_check Gamma t1 ;;
    match T with
    | Arrow T1 T2 =>
      if eqb_ty T1 T2 then return T1 else fail
    | _ => fail
    end
  end.

  Ltac invert_typecheck Gamma t T :=
    remember (type_check Gamma t) as TO;
    destruct TO as [T|];
    try solve_by_invert; try (inversion H0; eauto with db); try (subst; eauto with db).

  Ltac analyze T T1 T2 :=
    destruct T as [T1 T2 | |T1 T2|T1| |T1 T2]; try solve_by_invert.

  Ltac fully_invert_typecheck Gamma t T T T2 :=
    let TX := fresh T in
    remember (type_check Gamma t) as TO;
    destruct TO as [TX|]; try solve_by_invert;
    destruct TX as [T1 T2| |T1 T2|T1| |T1 T2];
    try solve_by_invert; try (inversion H0; eauto with db);
    try (subst; eauto with db).

  Ltac case_equality S T :=
    destruct (eqb_ty S T) eqn: Heqb;
    inversion H0; apply eqb_ty__eq in Heqb; subst; subst; eauto with db.

  Theorem type_checking_sound : forall Gamma t T,
      type_check Gamma t = Some T -> has_type Gamma t T.
  Proof with eauto with db.
    intros Gamma t. generalize dependent Gamma.
    induction t; intros Gamma T Htc; inversion Htc.
    - rename s into x. destruct (Gamma x) eqn:H.
      + inversion H0; subst. apply T_Var...
      + inversion H0.
    - invert_typecheck Gamma t1 T1.
      invert_typecheck Gamma t2 T2.
      analyze T1 T11 T12.
      case_equality T11 T2.
    - rename s into x. rename t into T1.
      remember (x |-> T1; Gamma) as Gamma'.
      invert_typecheck Gamma' t0 T0.
    - eauto with db.
    - rename t into t1.
      fully_invert_typecheck Gamma t1 T1 T11 T12.
    - rename t into t1.
      fully_invert_typecheck Gamma t1 T1 T11 T12.
    - invert_typecheck Gamma t1 T1.
      invert_typecheck Gamma t2 T2.
      analyze T1 T11 T12; analyze T2 T21 T22.
      inversion H0. subst...
    - invert_typecheck Gamma t1 T1.
      invert_typecheck Gamma t2 T2.
      invert_typecheck Gamma t3 T3.
      destruct T1; try solve_by_invert.
      case_equality T2 T3.
    - invert_typecheck Gamma t0 T1.
    - invert_typecheck Gamma t0 T2.
    - destruct (type_check Gamma t1) eqn:TS.
      + destruct t; try inversion H0.
        invert_typecheck (s |-> t4; Gamma) t2 T1.
        invert_typecheck (s0 |-> t5; Gamma) t3 T2.
        case_equality T1 T2.
      + inversion H0.
    - eauto with db.
    - invert_typecheck Gamma t1 T1.
      destruct (type_check Gamma t2) eqn: TL.
      + rename t into T'. destruct T'; try inversion H0.
        case_equality T1 T'.
      + inversion H0.
    - rename s into x31. rename s0 into x32.
      fully_invert_typecheck Gamma t1 T1 T11 T12.
      invert_typecheck Gamma t2 T2.
      remember (x31 |-> T1; x32 |-> List T1; Gamma) as G'.
      invert_typecheck G' t3 T3.
      case_equality T2 T3.
    - apply T_Unit.
    - invert_typecheck Gamma t1 T1.
      invert_typecheck Gamma t2 T2.
    - fully_invert_typecheck Gamma t T1 T11 T12.
    - fully_invert_typecheck Gamma t T1 T11 T12.
    - invert_typecheck Gamma t1 T1.
    - fully_invert_typecheck Gamma t T1 T11 T12.
      case_equality T1 T12.
  Qed.

  Theorem type_checking_complete : forall Gamma t T,
      has_type Gamma t T -> type_check Gamma t = Some T.
  Proof.
    intros Gamma t T Hty.
    induction Hty; simpl;
      try (rewrite IHHty);
      try (rewrite IHHty1);
      try (rewrite IHHty2);
      try (rewrite IHHty3);
      try (rewrite (eqb_ty_refl T)); 
      try (rewrite (eqb_ty_refl T1)); 
      try (rewrite (eqb_ty_refl T2)); 
      eauto.
    - destruct (Gamma x); try solve_by_invert. eauto with db.
  Qed.

End TypecheckerExtensions.
