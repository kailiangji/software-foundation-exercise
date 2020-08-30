Set Warnings "-notation-overridden, -parsing".
From Coq Require Import Strings.String.
Add LoadPath "/Users/jikl/demos/coq/software-foundation-exercise/logic_foundation" as LF.
From LF Require Import Maps.
From PLF Require Import SmallStep.

Module STLC.

  Inductive ty : Type :=
  | Bool : ty
  | Arrow : ty -> ty -> ty.

  Inductive tm : Type :=
  | var : string -> tm
  | app : tm -> tm -> tm
  | abs : string -> ty -> tm -> tm
  | tru : tm
  | fls : tm
  | test : tm -> tm -> tm -> tm.

  Open Scope string_scope.

  Definition x := "x".
  Definition y := "y".
  Definition z := "z".

  Hint Unfold x.
  Hint Unfold y.
  Hint Unfold z.

  (* idB = \x.Bool.x *)
  Notation idB := (abs x Bool (var x)).

  (* idBB = \x:Bool -> Bool.x *)
  Notation idBB := (abs x (Arrow Bool Bool) (var x)).

  (* idBBBB = \x:(Bool -> Bool) -> (Bool -> Bool).x *)
  Notation idBBBB :=
    (abs x (Arrow (Arrow Bool Bool)
                  (Arrow Bool Bool))
         (var x)).

  (* k = \x:Bool.\y:bool.x *)
  Notation k := (abs x Bool (abs y Bool (var x))).

  (* notB = \x:Bool.test x then fls else tru *)
  Notation notB := (abs x Bool (test (var x) fls tru)).

  Inductive value : tm -> Prop :=
  | v_abs : forall x T t, value (abs x T t)
  | v_tru : value tru
  | v_fls : value fls.

  Hint Constructors value : db.

  Reserved Notation "'[' x ':=' s ']' t" (at level 20).

  Fixpoint subst (x : string) (s : tm) (t : tm) : tm :=
    match t with
    | var x' =>
      if eqb_string x x' then s else t
    | abs x' T t1 =>
      abs x' T (if eqb_string x x' then t1 else ([x:=s] t1))
    | app t1 t2 =>
      app ([x:=s] t1) ([x:=s] t2)
    | tru => tru
    | fls => fls
    | test t1 t2 t3 =>
      test ([x:=s] t1) ([x:=s] t2) ([x:=s] t3)
    end
  where "'[' x ':=' s ']' t" := (subst x s t).

  Inductive substi (s : tm) (x : string) : tm -> tm -> Prop :=
  | s_var1 : substi s x (var x) s
  | s_var2 (x' : string) :
      x <> x' -> substi s x (var x') (var x')
  | s_abs1 (x' : string) (T : ty) (t : tm):
      eqb_string x x' = true ->
      substi s x (abs x' T t) (abs x' T t)
  | s_abs2 (x' : string) (T : ty) (t : tm) (t' : tm):
      eqb_string x x' = false ->
      substi s x t t' ->
      substi s x (abs x' T t) (abs x' T t')
  | s_app (t1 t1' t2 t2': tm) :
      substi s x t1 t1' ->
      substi s x t2 t2' ->
      substi s x (app t1 t2) (app t1' t2')
  | s_tru :
      substi s x tru tru
  | s_fls :
      substi s x fls fls
  | s_test (t1 t1' t2 t2' t3 t3' : tm) :
      substi s x t1 t1' ->
      substi s x t2 t2' ->
      substi s x t3 t3' ->
      substi s x (test t1 t2 t3) (test t1' t2' t3')
  .
  

  Hint Constructors substi.

  Theorem substi_correct : forall s x t t',
      [x:=s]t = t' <-> substi s x t t'.
  Proof.
    split; generalize dependent t'. 
    - induction t; intros t' H; simpl in H.
      + destruct (eqb_string x0 s0) eqn: E.
        * subst. apply eqb_string_true_iff in E. subst. apply s_var1.
        * subst. apply s_var2. apply eqb_string_false_iff. apply E.
      + rewrite <- H. apply s_app.
        * apply IHt1. reflexivity.
        * apply IHt2. reflexivity.
      + destruct (eqb_string x0 s0) eqn:E.
        * rewrite <- H. apply s_abs1. apply E.
        * rewrite <- H. apply s_abs2.
          apply E.
          apply IHt. reflexivity.
      + rewrite <- H. apply s_tru.
      + rewrite <- H. apply s_fls.
      + rewrite <- H. apply s_test.
        * apply IHt1. reflexivity.
        * apply IHt2. reflexivity.
        * apply IHt3. reflexivity.
    - intros t' H. induction H; simpl.
      + rewrite <- eqb_string_refl. reflexivity.
      + rewrite <- eqb_string_false_iff in H. rewrite H.
        reflexivity.
      + rewrite H. reflexivity.
      + rewrite H. rewrite IHsubsti. reflexivity.
      + rewrite IHsubsti1, IHsubsti2. reflexivity.
      + reflexivity.
      + reflexivity.
      + rewrite IHsubsti1, IHsubsti2, IHsubsti3. reflexivity.
  Qed.

  Reserved Notation "t1 '-->' t2" (at level 40).

  Inductive step : tm -> tm -> Prop :=
  | ST_AppAbs : forall x T t12 v2,
      value v2 ->
      (app (abs x T t12) v2) --> [x:=v2]t12
  | ST_App1 : forall t1 t1' t2,
      t1 --> t1' ->
      app t1 t2 --> app t1' t2
  | ST_App2 : forall v1 t2 t2',
      value v1 ->
      t2 --> t2' ->
      app v1 t2 --> app v1 t2'
  | ST_TestTru : forall t1 t2,
      (test tru t1 t2) --> t1
  | ST_TestFls : forall t1 t2,
      (test fls t1 t2) --> t2
  | ST_Test : forall t1 t1' t2 t3,
      t1 --> t1' ->
      (test t1 t2 t3) --> (test t1' t2 t3)
  where "t1 '-->' t2" := (step t1 t2).

  Hint Constructors step : db.

  Notation multistep := (multi step).
  Notation "t1 '-->*' t2" := (multistep t1 t2) (at level 40).

  (* idBB idB -->* idB *)
  Lemma step_example1 :
    (app idBB idB) -->* idB.
  Proof.
    eapply multi_step.
    - apply ST_AppAbs. apply v_abs.
    - simpl. apply multi_refl.
  Qed.

  (* (idBB (idBB idB)) -->* idB *)
  Lemma step_example2 :
    (app idBB (app idBB idB)) -->* idB.
  Proof.
    eapply multi_step.
    - apply ST_App2. apply v_abs. apply ST_AppAbs. apply v_abs.
    - simpl. apply step_example1.
  Qed.

  (* (idBB notB) tru -->* fls. *)
  Lemma step_example3 :
    app (app idBB notB) tru -->* fls.
  Proof.
    eapply multi_step.
    - apply ST_App1. apply ST_AppAbs. apply v_abs.
    - simpl. eapply multi_step.
      + apply ST_AppAbs. apply v_tru.
      + simpl. eapply multi_step.
        * apply ST_TestTru.
        * apply multi_refl.
  Qed.

  (* idBB (notB tru) -->* fls *)
  Lemma step_example4 :
    app idBB (app notB tru) -->* fls.
  Proof.
    eapply multi_step.
    - apply ST_App2. auto.
      apply ST_AppAbs. auto.
    - eapply multi_step.
      + simpl. apply ST_App2.
        * apply v_abs.
        * apply ST_TestTru.
      + eapply multi_step.
        * apply ST_AppAbs. apply v_fls.
        * simpl. apply multi_refl.
  Qed.

  Lemma step_example1' :
    app idBB idB -->* idB.
  Proof. normalize. Qed.
  Lemma step_example2' :
    app idBB (app idBB idB) -->* idB.
  Proof. normalize. Qed.
  Lemma step_example3' :
    app (app idBB notB) tru -->* fls.
  Proof. normalize. Qed.
  Lemma step_example4' :
    app idBB (app notB tru) -->* fls.
  Proof. normalize. Qed.

  Lemma step_example5 :
       app (app idBBBB idBB) idB
           -->* idB.
  Proof.
    eapply multi_step.
    - apply ST_App1. apply ST_AppAbs. apply v_abs.
    - simpl. eapply multi_step.
      + apply ST_AppAbs. apply v_abs.
      + simpl. apply multi_refl.
  Qed.

  Lemma step_example5_with_normalize :
    app (app idBBBB idBB) idB
        -->* idB.
  Proof. normalize. Qed.

  Definition context := partial_map ty.

  Reserved Notation "Gamma '|-' t '?' T" (at level 40).

  Inductive has_type : context -> tm -> ty -> Prop :=
  | T_Var : forall Gamma x T,
      Gamma x = Some T ->
      Gamma |- var x ? T
  | T_Abs : forall Gamma x T11 T12 t12,
      (x |-> T11; Gamma) |- t12 ? T12 ->
      Gamma |- abs x T11 t12 ? Arrow T11 T12
  | T_App : forall T11 T12 Gamma t1 t2,
      Gamma |- t1 ? Arrow T11 T12 ->
      Gamma |- t2 ? T11 ->
      Gamma |- app t1 t2 ? T12
  | T_Tru : forall Gamma,
      Gamma |- tru ? Bool
  | T_Fls : forall Gamma,
      Gamma |- fls ? Bool
  | T_Test : forall t1 t2 t3 T Gamma,
      Gamma |- t1 ? Bool ->
      Gamma |- t2 ? T ->
      Gamma |- t3 ? T ->
      Gamma |- test t1 t2 t3 ? T
  where "Gamma '|-' t '?' T" := (has_type Gamma t T).

  Hint Constructors has_type : db.

  Example typing_example1 :
    empty |- abs x Bool (var x) ? Arrow Bool Bool.
  Proof.
    apply T_Abs. apply T_Var. rewrite update_eq. reflexivity.
  Qed.

  Example typing_example_1' :
    empty |- abs x Bool (var x) ? Arrow Bool Bool.
  Proof. auto with db. Qed.

  Example typing_example_2 :
    empty |-
      (abs x Bool
         (abs y (Arrow Bool Bool)
            (app (var y) (app (var y) (var x))))) ?
      (Arrow Bool (Arrow (Arrow Bool Bool) Bool)).
  Proof.
    apply T_Abs.
    apply T_Abs.
    eapply T_App.
    - apply T_Var. rewrite update_eq. reflexivity.
    - eapply T_App.
      + apply T_Var. rewrite update_eq. reflexivity.
      + apply T_Var. rewrite update_neq.
        * rewrite update_eq. reflexivity.
        * intro H. inversion H.
  Qed.

  Example typing_example_2_full :
    empty |-
      (abs x Bool
         (abs y (Arrow Bool Bool)
            (app (var y) (app (var y) (var x))))) ?
      (Arrow Bool (Arrow (Arrow Bool Bool) Bool)).
  Proof.
    apply T_Abs.
    apply T_Abs.
    apply (T_App Bool).
    - apply T_Var. rewrite update_eq. reflexivity.
    - apply T_App with Bool.
      + apply T_Var. rewrite update_eq. reflexivity.
      + apply T_Var. rewrite update_neq.
        * rewrite update_eq. reflexivity.
        * intro H. inversion H.
  Qed.

  Example typing_example_3 :
    exists T,
      empty |-
        (abs x (Arrow Bool Bool)
           (abs y (Arrow Bool Bool)
              (abs z Bool
                 (app (var y) (app (var x) (var z)))))) ? T.
  Proof.
    eapply ex_intro.
    apply T_Abs.
    apply T_Abs.
    apply T_Abs.
    eapply T_App.
    - apply T_Var. rewrite update_neq.
      + rewrite update_eq. reflexivity.
      + intro Hzy. inversion Hzy.
    - eapply T_App.
      + apply T_Var. rewrite update_neq.
        * rewrite update_neq.
            rewrite update_eq. reflexivity.
            intro Hyx. inversion Hyx.
        * intro Hzx. inversion Hzx.
      + apply T_Var. rewrite update_eq. reflexivity.
  Qed.

  Example typing_nonexample_1 :
    ~ exists T,
        empty |-
          (abs x Bool
             (abs y Bool
                (app (var x) (var y)))) ? T.
  Proof.
    intros Hc. inversion Hc.
    inversion H. subst. clear H.
    inversion H5. subst. clear H5.
    inversion H4. subst. clear H4.
    inversion H2. subst. clear H2.
    inversion H5. subst. clear H5.
    inversion H1.
  Qed.

  Fixpoint ty_length (t : ty) :=
    match t with
    | Bool => 1
    | Arrow t1 t2 => 1 + ty_length t1 + ty_length t2
    end.

  Example typing_nonexample_3:
    ~(exists S T,
         empty |-
           (abs x S
              (app (var x) (var x))) ? T).
  Proof.
    intro Hc. inversion Hc. 
    inversion H. clear H.
    inversion H0. subst. clear H0.
    inversion H5. subst. clear H5.
    inversion H2. subst. clear H2.
    inversion H1.
    inversion H4. subst. clear H4.
    inversion H3.
    assert (Heq : ty_length (Arrow T11 T12) = ty_length T11).
    { rewrite H0. reflexivity. }
    inversion Heq.
    apply eq_sym in H2. 
    rewrite PeanoNat.Nat.add_comm in H2.
    generalize H2. apply Plus.succ_plus_discr.
  Qed.

End STLC.
