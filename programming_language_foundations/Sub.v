Set Warnings "-notation-overridden,-parsing".
Add LoadPath "/Users/jikl/demos/coq/software-foundation-exercise/logic_foundation" as LF.
From Coq Require Import Strings.String.
From LF Require Import Maps.
From PLF Require Import Types.
From PLF Require Import SmallStep.

Inductive ty : Type :=
| Top : ty
| Bool : ty
| Base : string -> ty
| Arrow : ty -> ty -> ty
| Unit : ty
| Prod : ty -> ty -> ty.

Inductive tm : Type :=
| var : string -> tm
| app : tm -> tm -> tm
| abs : string -> ty -> tm -> tm
| tru : tm
| fls : tm
| test : tm -> tm -> tm -> tm
| unit : tm
| pair : tm -> tm -> tm
| fst : tm -> tm
| snd : tm -> tm.

Fixpoint subst (x : string) (s : tm) (t : tm) : tm :=
  match t with
  | var y =>
    if eqb_string x y then s else t
  | abs y T t1 =>
    abs y T (if eqb_string x y then t1 else (subst x s t1))
  | app t1 t2 =>
    app (subst x s t1) (subst x s t2)
  | tru | fls | unit => t
  | test t1 t2 t3 =>
    test (subst x s t1) (subst x s t2) (subst x s t3)
  | pair t1 t2 =>
    pair (subst x s t1) (subst x s t2)
  | fst t1 =>
    fst (subst x s t1)
  | snd t1 =>
    snd (subst x s t1)
  end.

Notation "'[' x ':=' s ']' t" := (subst x s t) (at level 20).

Inductive value : tm -> Prop :=
| v_abs : forall x T t,
    value (abs x T t)
| v_true :
    value tru
| v_false :
    value fls
| v_unit :
    value unit
| v_pair : forall v1 v2,
    value v1 ->
    value v2 ->
    value (pair v1 v2).

Hint Constructors value : db.

Reserved Notation "t1 '-->' t2" (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_AppAbs : forall x T t12 v2,
         value v2 ->
         (app (abs x T t12) v2) --> [x:=v2]t12
  | ST_App1 : forall t1 t1' t2,
         t1 --> t1' ->
         (app t1 t2) --> (app t1' t2)
  | ST_App2 : forall v1 t2 t2',
         value v1 ->
         t2 --> t2' ->
         (app v1 t2) --> (app v1 t2')
  | ST_TestTrue : forall t1 t2,
      (test tru t1 t2) --> t1
  | ST_TestFalse : forall t1 t2,
      (test fls t1 t2) --> t2
  | ST_Test : forall t1 t1' t2 t3,
      t1 --> t1' ->
      (test t1 t2 t3) --> (test t1' t2 t3)
  | ST_Pair1 : forall t1 t1' t2,
      t1 --> t1' ->
      (pair t1 t2) --> (pair t1' t2)
  | ST_Pair2 : forall v1 t2 t2',
      value v1 ->
      t2 --> t2' ->
      (pair v1 t2) --> (pair v1 t2')
  | ST_Fst : forall t1 t1',
      t1 --> t1' ->
      (fst t1) --> (fst t1')
  | ST_FstPair : forall v1 v2,
      value v1 ->
      value v2 ->
      (fst (pair v1 v2)) --> v1
  | ST_Snd : forall t1 t1',
      t1 --> t1' ->
      (snd t1) --> (snd t1')
  | ST_SndPair : forall v1 v2,
      value v1 ->
      value v2 ->
      (snd (pair v1 v2)) --> v2
where "t1 '-->' t2" := (step t1 t2).

Hint Constructors step : db.

Reserved Notation "T '<:' U" (at level 40).

Inductive subtype : ty -> ty -> Prop :=
| S_Refl : forall T,
    T <: T
| S_Trans : forall S U T,
    S <: U ->
    U <: T ->
    S <: T
| S_Top : forall S,
    S <: Top
| S_Arrow : forall S1 S2 T1 T2,
    T1 <: S1 ->
    S2 <: T2 ->
    (Arrow S1 S2) <: (Arrow T1 T2)
| S_Prod : forall S1 S2 T1 T2,
    S1 <: T1 ->
    S2 <: T2 ->
    Prod S1 S2 <: Prod T1 T2
                       
where "T '<:' U" := (subtype T U).

Hint Constructors subtype : db.

Module Examples.

  Open Scope string_scope.
  Notation x := "x".
  Notation y := "y".
  Notation z := "z".
  Notation A := (Base "A").
  Notation B := (Base "B").
  Notation C := (Base "C").
  Notation String := (Base "String").
  Notation Float := (Base "Float").
  Notation Integer := (Base "Integer").
  
  Example subtyping_example_0 :
    (Arrow C Bool) <: (Arrow C Top).
  Proof. auto with db. Qed.

  (* Person := { name : String }
     Student := { name : String; gpa : Float }
     Employee := { name : String; ssn : Interger }
   *)

  Definition Person : ty := Prod (Prod A String) Top.

  Definition Student : ty := Prod (Prod A String) (Prod B Float).

  Definition Employee : ty := Prod (Prod A String) (Prod C Integer).

  Example sub_student_person :
    Student <: Person.
  Proof.
    unfold Student, Person.
    apply S_Prod.
    - apply S_Refl.
    - apply S_Top.
  Qed.

  Example sub_employee_person :
    Employee <: Person.
  Proof.
    unfold Employee, Person.
    apply S_Prod.
    - apply S_Refl.
    - apply S_Top.
  Qed.

  Example subtyping_example_1 :
    (Arrow Top Student) <: (Arrow (Arrow C C) Person).
  Proof.
    apply S_Arrow.
    - apply S_Top.
    - apply sub_student_person.
  Qed.

  Example subtyping_example_2 :
    (Arrow Top Person) <: (Arrow Person Top).
  Proof with eauto.
    apply S_Arrow.
    - apply S_Top.
    - apply S_Top.
  Qed.

End Examples.

Definition context := partial_map ty.

Reserved Notation "Gamma '|-' t '\in' T" (at level 40).
Inductive has_type : context -> tm -> ty -> Prop :=
  (* Same as before *)
  | T_Var : forall Gamma x T,
      Gamma x = Some T ->
      Gamma |- var x \in T
  | T_Abs : forall Gamma x T11 T12 t12,
      (x |-> T11 ; Gamma) |- t12 \in T12 ->
      Gamma |- abs x T11 t12 \in Arrow T11 T12
  | T_App : forall T1 T2 Gamma t1 t2,
      Gamma |- t1 \in Arrow T1 T2 ->
      Gamma |- t2 \in T1 ->
      Gamma |- app t1 t2 \in T2
  | T_True : forall Gamma,
       Gamma |- tru \in Bool
  | T_False : forall Gamma,
       Gamma |- fls \in Bool
  | T_Test : forall t1 t2 t3 T Gamma,
       Gamma |- t1 \in Bool ->
       Gamma |- t2 \in T ->
       Gamma |- t3 \in T ->
       Gamma |- test t1 t2 t3 \in T
  | T_Unit : forall Gamma,
      Gamma |- unit \in Unit
  (* New rule of subsumption *)
  | T_Sub : forall Gamma t S T,
      Gamma |- t \in S ->
      S <: T ->
      Gamma |- t \in T
  | T_Pair : forall t1 t2 T1 T2 Gamma,
      Gamma |- t1 \in T1 ->
      Gamma |- t2 \in T2 ->
      Gamma |- (pair t1 t2) \in Prod T1 T2
  | T_Fst : forall Gamma t T1 T2,
      Gamma |- t \in (Prod T1 T2) ->
      Gamma |- (fst t) \in T1
  | T_Snd : forall Gamma t T1 T2,
      Gamma |- t \in (Prod T1 T2) ->
      Gamma |- (snd t) \in T2

where "Gamma '|-' t '\in' T" := (has_type Gamma t T).

Hint Constructors has_type : db.

Hint Extern 2 (has_type _ (app _ _) _) =>
eapply T_App; auto : db.

Hint Extern 2 (_ = _) => compute; reflexivity: db.

Module Examples2.
  Import Examples.

  Example typing_example_0 :
    empty |- pair (abs z A (var z)) (abs z B (var z)) \in Prod (Arrow A A) (Arrow B B).
  Proof with eauto.
    auto with db.
  Qed.

  Example typing_example_1 :
    empty |- app (abs x (Prod Top (Arrow B B)) (snd (var x)))
                 (pair (abs z A (var z)) (abs z B (var z))) \in Arrow B B.
  Proof with eauto.
    eapply T_App.
    - eapply T_Abs. eapply T_Snd. apply T_Var. rewrite update_eq. auto with db.
    - apply T_Pair.
      + eapply T_Sub. apply T_Abs. apply T_Var. auto with db. apply S_Top.
      + apply T_Abs. apply T_Var. auto with db.
  Qed.

  Example typing_example_2 :
    empty |- app (abs z (Arrow (Arrow C C) (Prod Top (Arrow B B)))
                      (snd (app (var z) (abs x C (var x)))))
                 (abs z (Arrow C C) (pair (abs z A (var z)) (abs z B (var z)))) \in Arrow B B.
  Proof with eauto.
    eapply T_App...
    - apply T_Abs. eapply T_Snd. eapply T_App.
      + apply T_Var. auto with db.
      + apply T_Abs. apply T_Var. auto with db.
    - apply T_Abs. apply T_Pair.
      + eapply T_Sub.
        * apply T_Abs. apply T_Var. auto with db.
        * apply S_Top.
      + apply T_Abs. apply T_Var. auto with db.
  Qed.

End Examples2.

Lemma sub_inversion_Bool : forall U,
    U <: Bool ->
    U = Bool.
Proof with auto with db.
  intros U Hs.
  remember Bool as V eqn:EVBool.
  induction Hs; try solve [inversion EVBool].
  - reflexivity.
  - assert (U = T) as EUT.
    { apply IHHs2. apply EVBool. }
    rewrite <- EUT. apply IHHs1. subst...
Qed.

Lemma sub_inversion_arrow : forall U V1 V2,
    U <: Arrow V1 V2 ->
    exists U1 U2,
    U = Arrow U1 U2 /\ V1 <: U1 /\ U2 <: V2.
Proof.
  intros U V1 V2 Hs.
  remember (Arrow V1 V2) as V.
  generalize dependent V2. generalize dependent V1.
  induction Hs; intros V1 V2 H; try (inversion H).
  - exists V1, V2. auto with db.
  - assert (H1 : exists U1 U2 : ty,
               U = Arrow U1 U2 /\ V1 <: U1 /\ U2 <: V2).
    { apply IHHs2. apply H. }
    destruct H1 as [U1' [U2' [H1 [ H2 H3]] ]].
    assert (H4 : exists U1 U2 : ty,
               S = Arrow U1 U2 /\ U1' <: U1 /\ U2 <: U2').
    { apply IHHs1. apply H1. }
    destruct H4 as [U1 [U2 [H5 [H6 H7]]]].
    exists U1, U2.
    split.
    + apply H5.
    + split.
      * apply (S_Trans _ _ _ H2 H6).
      * apply (S_Trans _ _ _ H7 H3).
  - subst. exists S1, S2. auto with db.
Qed.

Lemma sub_inversion_prod : forall U V1 V2,
    U <: Prod V1 V2 ->
    exists U1 U2,
    U = Prod U1 U2 /\ U1 <: V1 /\ U2 <: V2.
Proof.
  intros U V1 V2 Hs.
  remember (Prod V1 V2) as V.
  generalize dependent V2. generalize dependent V1.
  induction Hs; intros V1 V2 H; try (inversion H).
  - exists V1, V2. auto with db.
  - assert (H1 : exists U1 U2 : ty,
               U = Prod U1 U2 /\ U1 <: V1 /\ U2 <: V2).
    { apply IHHs2. apply H. }
    destruct H1 as [U1' [U2' [H1 [ H2 H3]] ]].
    assert (H4 : exists U1 U2 : ty,
               S = Prod U1 U2 /\ U1 <: U1' /\ U2 <: U2').
    { apply IHHs1. apply H1. }
    destruct H4 as [U1 [U2 [H5 [H6 H7]]]].
    exists U1, U2.
    split.
    + apply H5.
    + split.
      * apply (S_Trans _ _ _ H6 H2).
      * apply (S_Trans _ _ _ H7 H3).
  - subst. exists S1, S2. auto with db.
Qed.

Lemma canonical_forms_of_arrow_types : forall Gamma s T1 T2,
  Gamma |- s \in Arrow T1 T2 ->
  value s ->
  exists x S1 s2, s = abs x S1 s2.
Proof.
  intros Gamma s T1 T2 H1.
  remember (Arrow T1 T2) as ATT.
  generalize dependent T2. generalize dependent T1.
  induction H1; intros T1' T2' H2 H3; try (inversion H2); try (inversion H3).
  - exists x, T11, t12. subst; reflexivity.
  - subst. clear H0. exists x, T0, t0. reflexivity.
  - subst. clear H0.
    assert (HTS : exists U1 U2, S = Arrow U1 U2 /\ T1' <: U1 /\ U2 <: T2').
    { apply sub_inversion_arrow. apply H. }
    destruct HTS as [U1 [U2 [H4 [H5 H6]]]].
    apply (IHhas_type _ _) in H4.
    { apply H4. }
    { apply v_true. }
  - subst. clear H0.
    assert (HTS : exists U1 U2, S = Arrow U1 U2 /\ T1' <: U1 /\ U2 <: T2').
    { apply sub_inversion_arrow. apply H. }
    destruct HTS as [U1 [U2 [H4 [H5 H6]]]].
    apply (IHhas_type _ _) in H4.
    { apply H4. }
    { apply v_false. }
  - subst. clear H0.
    assert (HTS : exists U1 U2, S = Arrow U1 U2 /\ T1' <: U1 /\ U2 <: T2').
    { apply sub_inversion_arrow. apply H. }
    destruct HTS as [U1 [U2 [H4 [H5 H6]]]].
    apply (IHhas_type _ _) in H4.
    { apply H4. }
    { apply v_unit. }
  - subst. clear H0.
    assert (HTS : exists U1 U2, S = Arrow U1 U2 /\ T1' <: U1 /\ U2 <: T2').
    { apply sub_inversion_arrow. apply H. }
    destruct HTS as [U1 [U2 [H6 [H7 H8]]]].
    apply (IHhas_type _ _) in H6.
    { apply H6. }
    { apply v_pair; assumption. }
Qed.

Lemma canonical_forms_of_Bool : forall Gamma s,
  Gamma |- s \in Bool ->
  value s ->
  s = tru \/ s = fls.
Proof with eauto with db.
  intros Gamma s H1.
  remember Bool as TB.
  induction H1; intro Hval; try (inversion Hval); try (inversion HeqTB); subst...
  - clear H2. apply (sub_inversion_Bool _) in H. auto.
  - clear H2. apply (sub_inversion_Bool _) in H. auto.
  - clear H4. apply (sub_inversion_Bool _) in H. auto.
Qed.

Lemma canonical_forms_of_prod_types : forall Gamma s T1 T2,
    Gamma |- s \in Prod T1 T2 ->
                   value s ->
                   exists s1 s2,
                     s = pair s1 s2.
Proof with eauto with db.
  intros Gamma s T1 T2 H1.
  remember (Prod T1 T2) as PTT.
  generalize dependent T2. generalize dependent T1.
  induction H1; intros T1' T2' H2 H3; try (inversion H2); try (inversion H3).
  - subst. clear H0.
    assert (HTS : exists U1 U2, S = Prod U1 U2 /\ U1 <: T1' /\ U2 <: T2').
    { apply sub_inversion_prod. apply H. }
    destruct HTS as [U1 [U2 [H4 [H5 H6]]]].
    apply (IHhas_type _ _) in H4.
    { apply H4. }
    { apply v_abs. }
  - subst. clear H0.
    assert (HTS : exists U1 U2, S = Prod U1 U2 /\ U1 <: T1' /\ U2 <: T2').
    { apply sub_inversion_prod. apply H. }
    destruct HTS as [U1 [U2 [H4 [H5 H6]]]].
    apply (IHhas_type _ _) in H4.
    { apply H4. }
    { apply v_true. }
  - subst. clear H0.
    assert (HTS : exists U1 U2, S = Prod U1 U2 /\ U1 <: T1' /\ U2 <: T2').
    { apply sub_inversion_prod. apply H. }
    destruct HTS as [U1 [U2 [H4 [H5 H6]]]].
    apply (IHhas_type _ _) in H4.
    { apply H4. }
    { apply v_false. }
  - subst. clear H0.
    assert (HTS : exists U1 U2, S = Prod U1 U2 /\ U1 <: T1' /\ U2 <: T2').
    { apply sub_inversion_prod. apply H. }
    destruct HTS as [U1 [U2 [H4 [H5 H6]]]].
    apply (IHhas_type _ _) in H4.
    { apply H4. }
    { apply v_unit. }
  - eauto with db.
  - eauto with db.
Qed.
  
Theorem progress : forall t T,
    empty |- t \in T ->
    value t \/ exists t', t --> t'.
Proof with eauto with db.
  intros t T Ht.
  remember empty as Gamma.
  revert HeqGamma.
  induction Ht; intros HeqGamma; subst...
  - inversion H.
  - right.
    destruct IHHt1; subst...
    + destruct IHHt2; subst...
      * destruct (canonical_forms_of_arrow_types empty t1 T1 T2)
          as [x [S1 [t12 Heqt1]]]...
        subst. exists ([x:=t2]t12)...
      * inversion H0 as [t2' Hstp]. exists (app t1 t2')...
    + inversion H as [t1' Hstp]. exists (app t1' t2)...
  - right.
    destruct IHHt1.
    + auto.
    + assert (t1 = tru \/ t1 = fls) by (eapply canonical_forms_of_Bool; eauto).
      inversion H0; subst...
    + inversion H. rename x into t1'. eauto with db.
  - destruct IHHt1; subst...
    + destruct IHHt2; subst...
      right. inversion H0 as [t2' Hstp]. exists (pair t1 t2')...
    + right. inversion H as [t1' Hstp]. exists (pair t1' t2)...
  - destruct IHHt; subst...
    + right. destruct (canonical_forms_of_prod_types empty t T1 T2)
        as [t1 [t2 Heqt]].
      * apply Ht.
      * apply H.
      * subst. inversion H. exists t1. apply ST_FstPair; assumption.
    + right. inversion H as [t' Hstp]. exists (fst t')...
  - destruct IHHt; subst...
    + right. destruct (canonical_forms_of_prod_types empty t T1 T2)
        as [t1 [t2 Heqt]].
      * apply Ht.
      * apply H.
      * subst. inversion H. exists t2. apply ST_SndPair; assumption.
    + right. inversion H as [t' Hstp]. exists (snd t')...
Qed.

Lemma typing_inversion_abs : forall Gamma x S1 t2 T,
    Gamma |- (abs x S1 t2) \in T ->
    exists S2,
      Arrow S1 S2 <: T
      /\ (x |-> S1; Gamma) |- t2 \in S2.
Proof with eauto with db.
  intros Gamma x S1 t2 T H.
  remember (abs x S1 t2) as t.
  induction H; inversion Heqt; subst; intros; try solve_by_invert.
  - exists T12...
  - destruct IHhas_type as [S2 [Hsub Hty]]...
Qed.

Lemma typing_inversion_var : forall Gamma x T,
    Gamma |- (var x) \in T ->
    exists S,
      Gamma x = Some S /\ S <: T.
Proof with eauto with db.
  intros Gamma x T H.
  remember (var x) as v.
  induction H; inversion Heqv; subst; intros; try solve_by_invert.
  - exists T...
  - destruct IHhas_type as [S1 [Hsub Hty]]...
Qed.

Lemma typing_inversion_app : forall Gamma t1 t2 T2,
    Gamma |- (app t1 t2) \in T2 ->
    exists T1,
      Gamma |- t1 \in (Arrow T1 T2) /\
      Gamma |- t2 \in T1.
Proof with eauto with db.
  intros Gamma t1 t2 T2 H.
  remember (app t1 t2) as Tapp.
  induction H; inversion HeqTapp; subst; intros; try solve_by_invert.
  - exists T1...
  - destruct IHhas_type as [T1 [Habs Ht]]...
Qed.

Lemma typing_inversion_true : forall Gamma T,
    Gamma |- tru \in T ->
    Bool <: T.
Proof with eauto with db.
  intros Gamma T H.
  remember tru as tt.
  induction H; inversion Heqtt; subst... 
Qed.

Lemma typing_inversion_false : forall Gamma T,
    Gamma |- fls \in T ->
    Bool <: T.
Proof with eauto with db.
  intros Gamma T H.
  remember fls as tf.
  induction H; inversion Heqtf; subst...
Qed.

Lemma typing_inversion_if : forall Gamma t1 t2 t3 T,
    Gamma |- (test t1 t2 t3) \in T ->
    Gamma |- t1 \in Bool
    /\ Gamma |- t2 \in T
    /\ Gamma |- t3 \in T.
Proof with eauto with db.
  intros Gamma t1 t2 t3 T H.
  remember (test t1 t2 t3) as ttest.
  induction H; inversion Heqttest; subst...
  destruct IHhas_type as [H2 [H3 H4]]...
Qed.

Lemma typing_inversion_unit : forall Gamma T,
    Gamma |- unit \in T ->
    Unit <: T.
Proof with eauto with db.
  intros Gamma T H.
  remember unit as tu.
  induction H; inversion Heqtu; subst...
Qed.

Lemma typing_inversion_pair : forall Gamma t1 t2 T,
    Gamma |- (pair t1 t2) \in T ->
    exists T1 T2,
    Gamma |- t1 \in T1 /\ Gamma |- t2 \in T2 /\ Prod T1 T2 <: T.
Proof with eauto with db.
  intros Gamma t1 t2 T H.
  remember (pair t1 t2) as tp.
  induction H; inversion Heqtp; subst...
  destruct IHhas_type as [T1 [T2 [H2 [H3 H4]]]]...
  exists T1, T2...
Qed.

Lemma typing_inversion_fst : forall Gamma t T1,
    Gamma |- fst t \in T1 ->
    exists T2,
    Gamma |- t \in Prod T1 T2.
Proof with eauto with db.
  intros Gamma t T1 H.
  remember (fst t) as ft.
  induction H; inversion Heqft; subst...
  destruct IHhas_type as [T2 H2]...
Qed.

Lemma typing_inversion_snd : forall Gamma t T2,
    Gamma |- snd t \in T2 ->
    exists T1,
    Gamma |- t \in Prod T1 T2.
Proof with eauto with db.
  intros Gamma t T1 H.
  remember (snd t) as st.
  induction H; inversion Heqst; subst...
  destruct IHhas_type as [T2 H2]...
Qed.

Lemma abs_arrow : forall x S1 s2 T1 T2,
  empty |- (abs x S1 s2) \in (Arrow T1 T2) ->
  T1 <: S1
  /\ (x |-> S1 ; empty) |- s2 \in T2.
Proof with eauto with db.
  intros x S1 s2 T1 T2 Hty.
  apply typing_inversion_abs in Hty.
  inversion Hty as [S2 [Hsub Hty1]].
  apply sub_inversion_arrow in Hsub.
  inversion Hsub as [U1 [U2 [Heq [Hsub1 Hsub2]]]].
  inversion Heq; subst...
Qed.

Inductive appears_free_in : string -> tm -> Prop :=
  | afi_var : forall x,
      appears_free_in x (var x)
  | afi_app1 : forall x t1 t2,
      appears_free_in x t1 -> appears_free_in x (app t1 t2)
  | afi_app2 : forall x t1 t2,
      appears_free_in x t2 -> appears_free_in x (app t1 t2)
  | afi_abs : forall x y T11 t12,
        y <> x ->
        appears_free_in x t12 ->
        appears_free_in x (abs y T11 t12)
  | afi_test1 : forall x t1 t2 t3,
      appears_free_in x t1 ->
      appears_free_in x (test t1 t2 t3)
  | afi_test2 : forall x t1 t2 t3,
      appears_free_in x t2 ->
      appears_free_in x (test t1 t2 t3)
  | afi_test3 : forall x t1 t2 t3,
      appears_free_in x t3 ->
      appears_free_in x (test t1 t2 t3)
                      | afi_pairL : forall x t1 t2,
      appears_free_in x t1 ->
      appears_free_in x (pair t1 t2)
  | afi_pairR : forall x t1 t2,
      appears_free_in x t2 ->
      appears_free_in x (pair t1 t2)
  | afi_fst : forall x t,
      appears_free_in x t ->
      appears_free_in x (fst t)
  | afi_snd : forall x t,
      appears_free_in x t ->
      appears_free_in x (snd t)
.
Hint Constructors appears_free_in : db.

Lemma context_invariance : forall Gamma Gamma' t S,
     Gamma |- t \in S ->
     (forall x, appears_free_in x t -> Gamma x = Gamma' x) ->
     Gamma' |- t \in S.
Proof with eauto with db.
  intros. generalize dependent Gamma'.
  induction H; intros Gamma' Heqv...
  - apply T_Var... rewrite <- Heqv...
  - apply T_Abs... apply IHhas_type. intros x0 Hafi.
    unfold update, t_update. destruct (eqb_stringP x x0)...
  - eapply T_App...
  - apply T_Test...
  - apply T_Pair...
Qed.

Lemma free_in_context : forall x t T Gamma,
   appears_free_in x t ->
   Gamma |- t \in T ->
   exists T', Gamma x = Some T'.
Proof with eauto with db.
  intros x t T Gamma Hafi Htyp.
  induction Htyp; subst; inversion Hafi; subst...
  destruct (IHHtyp H4) as [T Hctx]. exists T.
  unfold update, t_update in Hctx.
  rewrite <- eqb_string_false_iff in H2.
  rewrite H2 in Hctx...
Qed.

Lemma substitution_preserves_typing : forall Gamma x U v t S,
    (x |-> U; Gamma) |- t \in S ->
    empty |- v \in U ->
    Gamma |- [x:=v]t \in S.
Proof with eauto with db.
  intros Gamma x U v t S Htypt Htypv.
  generalize dependent S. generalize dependent Gamma.
  induction t; intros; simpl.
  - rename s into y.
    destruct (typing_inversion_var _ _ _ Htypt) as
        [T [Hctx Hsub]].
    unfold update, t_update in Hctx.
    destruct (eqb_stringP x y) as [Hxy|Hxy]; eauto; subst...
    inversion Hctx; subst. clear Hctx.
    apply context_invariance with empty...
    intros x Hcontra.
    destruct (free_in_context _ _ S empty Hcontra) as
        [T' HT']...
    inversion HT'.
  - destruct (typing_inversion_app _ _ _ _ Htypt) as
        [T1 [Htypt1 Htypt2]].
    eapply T_App...
  - rename s into y. rename t into T1.
    destruct (typing_inversion_abs _ _ _ _ _ Htypt)
      as [T2 [Hsub Htypt2]].
    apply T_Sub with (Arrow T1 T2)... apply T_Abs...
    destruct (eqb_stringP x y) as [Hxy|Hxy].
    + eapply context_invariance...
      subst.
      intros x Hafi. unfold update, t_update.
      destruct (eqb_string y x)...
    + apply IHt. eapply context_invariance...
      intros z Hafi. unfold update, t_update.
      destruct (eqb_stringP y z)...
      subst.
      rewrite <- eqb_string_false_iff in Hxy. rewrite Hxy...
  - assert (Bool <: S)
      by apply (typing_inversion_true _ _ Htypt)...
  - assert (Bool <: S)
      by apply (typing_inversion_false _ _ Htypt)...
  - assert ((x |-> U; Gamma) |- t1 \in Bool
         /\ (x |-> U; Gamma) |- t2 \in S
         /\ (x |-> U; Gamma) |- t3 \in S)
      by apply (typing_inversion_if _ _ _ _ _ Htypt).
    inversion H as [H1 [H2 H3]].
    apply IHt1 in H1. apply IHt2 in H2. apply IHt3 in H3.
    auto with db.
  - assert (Unit <: S)
      by apply (typing_inversion_unit _ _ Htypt)...
  - destruct (typing_inversion_pair _ _ _ _ Htypt) as
        [T1 [T2 [H1 [H2 H3]]]].
    apply T_Sub with (Prod T1 T2)...
  - destruct (typing_inversion_fst _ _ _ Htypt) as
        [T2 H2]...
  - destruct (typing_inversion_snd _ _ _ Htypt) as
        [T1 H2]...
Qed.

Theorem preservation : forall t t' T,
    empty |- t \in T ->
    t --> t' ->
    empty |- t' \in T.
Proof with eauto with db.
  intros t t' T HT.
  remember empty as Gamma. generalize dependent HeqGamma.
  generalize dependent t'.
  induction HT; intros t' HeqGamma HE; subst; inversion HE; subst...
  - apply (abs_arrow _ _ _ _ _) in HT1.
    destruct HT1 as [Hsub Htypt].
    eapply substitution_preserves_typing.
    + apply Htypt.
    + eapply T_Sub. apply HT2. apply Hsub.
  - apply (typing_inversion_pair _ _ ) in HT.
    destruct HT as [T3 [T4 [H2 [H3 H4]]]].
    apply (sub_inversion_prod _ _ _ ) in H4.
    destruct H4 as [U1 [U2 [Heq [Hsub1 Hsub2]]]].
    inversion Heq; subst.
    eapply T_Sub. apply H2. apply Hsub1.
  - apply (typing_inversion_pair _ _ ) in HT.
    destruct HT as [T3 [T4 [H2 [H3 H4]]]].
    apply (sub_inversion_prod _ _ _ ) in H4.
    destruct H4 as [U1 [U2 [Heq [Hsub1 Hsub2]]]].
    inversion Heq; subst.
    eapply T_Sub. apply H3. apply Hsub2.
Qed.
