Set Warnings "-notation-overridden,-parsing".
Add LoadPath "/Users/jikl/demos/coq/software-foundation-exercise/logic_foundation" as LF.
From LF Require Import Maps.
From PLF Require Import Types.
From PLF Require Import SmallStep.
From PLF Require Import Stlc.
From Coq Require Import Strings.String.

Module STLCExtended.

  Inductive ty : Type :=
  | Arrow : ty -> ty -> ty
  | Nat : ty
  | Sum : ty -> ty -> ty
  | List : ty -> ty
  | Unit : ty
  | Prod : ty -> ty -> ty.

  Inductive tm : Type :=
  (* pure STLC *)
  | var : string -> tm
  | app : tm -> tm -> tm
  | abs : string -> ty -> tm -> tm
  (* numbers *)
  | const : nat -> tm
  | scc : tm -> tm
  | prd : tm -> tm
  | mlt : tm -> tm -> tm
  | test0 : tm -> tm -> tm -> tm
  (* sums *)
  | tinl : ty -> tm -> tm
  | tinr : ty -> tm -> tm
  | tcase : tm -> string -> tm -> string -> tm -> tm
           (* i.e., case t0 of inl x1 => t1 | inr x2 => t2*)
  (* lists *)
  | tnil : ty -> tm
  | tcons : tm -> tm -> tm
  | tlcase : tm -> tm -> string -> string -> tm -> tm
           (* i.e., lcase t1 of | nil => t2 | x :: y => t3*)
  (* unit *)                                           
  | unit : tm
  (* pairs *)
  | tpair : tm -> tm -> tm
  | tfst : tm -> tm
  | tsnd : tm -> tm
  (* let *)
  | tlet : string -> tm -> tm -> tm
          (* i.e., let x = t1 in t2*)
  (* fix *)
  | tfix : tm -> tm.

  (* Substitution *)
  Fixpoint subst (x : string) (s : tm) (t : tm) : tm :=
    match t with
    | var y =>
      if eqb_string x y then s else t
    | abs y T t1 =>
      abs y T (if eqb_string x y then t1 else (subst x s t1))
    | app t1 t2 =>
      app (subst x s t1) (subst x s t2)
    | const n =>
      const n
    | scc t1 =>
      scc (subst x s t1)
    | prd t1 =>
      prd (subst x s t1)
    | mlt t1 t2 =>
      mlt (subst x s t1) (subst x s t2)
    | test0 t1 t2 t3 =>
      test0 (subst x s t1) (subst x s t2) (subst x s t3)
    | tinl T t1 =>
      tinl T (subst x s t1)
    | tinr T t1 =>
      tinr T (subst x s t1)
    | tcase t0 y1 t1 y2 t2 =>
      tcase (subst x s t0)
            y1 (if eqb_string x y1 then t1 else (subst x s t1))
            y2 (if eqb_string x y2 then t2 else (subst x s t2))
    | tnil T =>
      tnil T
    | tcons t1 t2 =>
      tcons (subst x s t1) (subst x s t2)
    | tlcase t1 t2 y1 y2 t3 =>
      tlcase (subst x s t1) (subst x s t2) y1 y2
             (if eqb_string x y1 then
                t3
              else if eqb_string x y2 then t3
                   else (subst x s t3))
    | unit => unit
    | tpair t1 t2 =>
      tpair (subst x s t1) (subst x s t2)
    | tfst t1 =>
      tfst (subst x s t1)
    | tsnd t1 =>
      tsnd (subst x s t1)
    | tlet y t1 t2 =>
      if eqb_string x y then tlet y (subst x s t1) t2
      else tlet y (subst x s t1) (subst x s t2)
    | tfix tf =>
      tfix (subst x s tf)
    end.

  Notation "'[' x ':=' s ']' t" := (subst x s t) (at level 20).

  Inductive value : tm -> Prop :=
  (* In pure STLC, function abstractions are values: *)
  | v_abs : forall x T11 t12,
      value (abs x T11 t12)
  (* Numbers are values: *)
  | v_nat : forall n1,
      value (const n1)
  (* A tagged value is a value:  *)
  | v_inl : forall v T,
      value v ->
      value (tinl T v)
  | v_inr : forall v T,
      value v ->
      value (tinr T v)
  (* A list is a value iff its head and tail are values: *)
  | v_lnil : forall T, value (tnil T)
  | v_lcons : forall v1 vl,
      value v1 ->
      value vl ->
      value (tcons v1 vl)
  (* A unit is always a value *)
  | v_unit : value unit
  (* A pair is a value if both components are: *)
  | v_pair : forall v1 v2,
      value v1 ->
      value v2 ->
      value (tpair v1 v2).

  Hint Constructors value : db.

  Reserved Notation "t1 '-->' t2" (at level 40).

  Inductive step : tm -> tm -> Prop :=
  (* pure STLC *)
  | ST_AppAbs : forall x T11 t12 v2,
         value v2 ->
         (app (abs x T11 t12) v2) --> [x:=v2]t12
  | ST_App1 : forall t1 t1' t2,
         t1 --> t1' ->
         (app t1 t2) --> (app t1' t2)
  | ST_App2 : forall v1 t2 t2',
         value v1 ->
         t2 --> t2' ->
         (app v1 t2) --> (app v1 t2')
  (* numbers *)
  | ST_Succ1 : forall t1 t1',
       t1 --> t1' ->
       (scc t1) --> (scc t1')
  | ST_SuccNat : forall n1,
       (scc (const n1)) --> (const (S n1))
  | ST_Pred : forall t1 t1',
       t1 --> t1' ->
       (prd t1) --> (prd t1')
  | ST_PredNat : forall n1,
       (prd (const n1)) --> (const (pred n1))
  | ST_Mult1 : forall t1 t1' t2,
       t1 --> t1' ->
       (mlt t1 t2) --> (mlt t1' t2)
  | ST_Mult2 : forall v1 t2 t2',
       value v1 ->
       t2 --> t2' ->
       (mlt v1 t2) --> (mlt v1 t2')
  | ST_Mulconsts : forall n1 n2,
       (mlt (const n1) (const n2)) --> (const (mult n1 n2))
  | ST_Test01 : forall t1 t1' t2 t3,
       t1 --> t1' ->
       (test0 t1 t2 t3) --> (test0 t1' t2 t3)
  | ST_Test0Zero : forall t2 t3,
       (test0 (const 0) t2 t3) --> t2
  | ST_Test0Nonzero : forall n t2 t3,
       (test0 (const (S n)) t2 t3) --> t3
  (* sums *)
  | ST_Inl : forall t1 t1' T,
        t1 --> t1' ->
        (tinl T t1) --> (tinl T t1')
  | ST_Inr : forall t1 t1' T,
        t1 --> t1' ->
        (tinr T t1) --> (tinr T t1')
  | ST_Case : forall t0 t0' x1 t1 x2 t2,
        t0 --> t0' ->
        (tcase t0 x1 t1 x2 t2) --> (tcase t0' x1 t1 x2 t2)
  | ST_CaseInl : forall v0 x1 t1 x2 t2 T,
        value v0 ->
        (tcase (tinl T v0) x1 t1 x2 t2) --> [x1:=v0]t1
  | ST_CaseInr : forall v0 x1 t1 x2 t2 T,
        value v0 ->
        (tcase (tinr T v0) x1 t1 x2 t2) --> [x2:=v0]t2
  (* lists *)
  | ST_Cons1 : forall t1 t1' t2,
       t1 --> t1' ->
       (tcons t1 t2) --> (tcons t1' t2)
  | ST_Cons2 : forall v1 t2 t2',
       value v1 ->
       t2 --> t2' ->
       (tcons v1 t2) --> (tcons v1 t2')
  | ST_Lcase1 : forall t1 t1' t2 x1 x2 t3,
       t1 --> t1' ->
       (tlcase t1 t2 x1 x2 t3) --> (tlcase t1' t2 x1 x2 t3)
  | ST_LcaseNil : forall T t2 x1 x2 t3,
       (tlcase (tnil T) t2 x1 x2 t3) --> t2
  | ST_LcaseCons : forall v1 vl t2 x1 x2 t3,
       value v1 ->
       value vl ->
       (tlcase (tcons v1 vl) t2 x1 x2 t3)
         --> (subst x2 vl (subst x1 v1 t3))
  | ST_Pair1 : forall t1 t1' t2,
      t1 --> t1' ->
      (tpair t1 t2) --> (tpair t1' t2)
  | ST_Pair2 : forall v1 t2 t2',
      value v1 ->
      t2 --> t2' ->
      (tpair v1 t2) --> (tpair v1 t2')
  | ST_Fst : forall t1 t1',
      t1 --> t1' ->
      (tfst t1) --> (tfst t1')
  | ST_FstPair : forall v1 v2,
      value v1 ->
      value v2 ->
      (tfst (tpair v1 v2)) --> v1
  | ST_Snd : forall t1 t1',
      t1 --> t1' ->
      (tsnd t1) --> (tsnd t1')
  | ST_SndPair : forall v1 v2,
      value v1 ->
      value v2 ->
      (tsnd (tpair v1 v2)) --> v2
  | ST_Let1 : forall x t1 t1' t2,
      t1 --> t1' ->
      (tlet x t1 t2) --> (tlet x t1' t2)
  | ST_LetValue : forall x v1 t2,
      value v1 ->
      (tlet x v1 t2) --> [x := v1]t2
  | ST_Fix1 : forall t1 t1',
      t1 --> t1' ->
      tfix t1 --> tfix t1'
  | ST_FixAbs : forall xf T1 t2,
      tfix (abs xf T1 t2) --> [xf:=tfix (abs xf T1 t2)] t2
  where "t1 '-->' t2" := (step t1 t2).

  Notation multistep := (multi step).

  Notation "t1 '-->*' t2" := (multistep t1 t2) (at level 40).

  Hint Constructors step : db.

  Definition context := partial_map ty.

  Reserved Notation "Gamma '|-' t '?' T" (at level 40).

  Inductive has_type : context -> tm -> ty -> Prop :=
  | T_Var : forall Gamma x T,
      Gamma x = Some T ->
      Gamma |- (var x) ? T
  | T_Abs : forall Gamma x T11 T12 t12,
      (x |-> T11; Gamma) |- t12 ? T12 ->
      Gamma |- (abs x T11 t12) ? (Arrow T11 T12)
  | T_App : forall T1 T2 Gamma t1 t2,
      Gamma |- t1 ? (Arrow T1 T2) ->
      Gamma |- t2 ? T1 ->
      Gamma |- (app t1 t2) ? T2
  |T_Nat : forall Gamma n1,
      Gamma |- (const n1) ? Nat
  | T_Succ : forall Gamma t1,
      Gamma |- t1 ? Nat ->
      Gamma |- (scc t1) ? Nat
  | T_Pred : forall Gamma t1,
      Gamma |- t1 ? Nat ->
      Gamma |- (prd t1) ? Nat
  | T_Mult : forall Gamma t1 t2,
      Gamma |- t1 ? Nat ->
      Gamma |- t2 ? Nat ->
      Gamma |- (mlt t1 t2) ? Nat
  | T_Test0 : forall Gamma t1 t2 t3 T1,
      Gamma |- t1 ? Nat ->
      Gamma |- t2 ? T1 ->
      Gamma |- t3 ? T1 ->
      Gamma |- (test0 t1 t2 t3) ? T1
  | T_Inl : forall Gamma t1 T1 T2,
      Gamma |- t1 ? T1 ->
      Gamma |- (tinl T2 t1) ? (Sum T1 T2)
  | T_Inr : forall Gamma t2 T1 T2,
      Gamma |- t2 ? T2 ->
      Gamma |- (tinr T1 t2) ? (Sum T1 T2)
  | T_Case : forall Gamma t0 x1 T1 t1 x2 T2 t2 T,
      Gamma |- t0 ? (Sum T1 T2) ->
      (x1 |-> T1; Gamma) |- t1 ? T ->
      (x2 |-> T2; Gamma) |- t2 ? T ->
      Gamma |- (tcase t0 x1 t1 x2 t2) ? T
  | T_Nil : forall Gamma T,
      Gamma |- (tnil T) ? (List T)
  | T_Cons : forall Gamma t1 t2 T1,
      Gamma |- t1 ? T1 ->
      Gamma |- t2 ? (List T1) ->
      Gamma |- (tcons t1 t2) ? (List T1)
  | T_Lcase : forall Gamma t1 T1 t2 x1 x2 t3 T2,
      Gamma |- t1 ? (List T1) ->
      Gamma |- t2 ? T2 ->
      (x1 |-> T1; x2 |-> (List T1); Gamma) |- t3 ? T2 ->
      Gamma |- (tlcase t1 t2 x1 x2 t3) ? T2
  | T_Unit : forall Gamma,
      Gamma |- unit ? Unit
  | T_Pair : forall Gamma t1 T1 t2 T2,
      Gamma |- t1 ? T1 ->
      Gamma |- t2 ? T2 ->
      Gamma |- (tpair t1 t2) ? (Prod T1 T2)
  | T_Fst : forall Gamma t T1 T2,
      Gamma |- t ? (Prod T1 T2) ->
      Gamma |- (tfst t) ? T1
  | T_Snd : forall Gamma t T1 T2,
      Gamma |- t ? (Prod T1 T2) ->
      Gamma |- (tsnd t) ? T2
  | T_Let : forall Gamma x t1 T1 t2 T2,
      Gamma |- t1 ? T1 ->
      (x |-> T1; Gamma) |- t2 ? T2 ->
      Gamma |- tlet x t1 t2 ? T2
  | T_Fix : forall Gamma t1 T1,
      Gamma |- t1 ? (Arrow T1 T1) ->
      Gamma |- (tfix t1) ? T1
  where "Gamma '|-' t '?' T" := (has_type Gamma t T).

  Hint Constructors has_type : db.

  Module Examples.

    Open Scope string_scope.
    Notation x := "x".
    Notation y := "y".
    Notation a := "a".
    Notation f := "f".
    Notation g := "g".
    Notation l := "l".
    Notation k := "k".
    Notation i1 := "i1".
    Notation i2 := "i2".
    Notation processSum := "processSum".
    Notation n := "n".
    Notation eq := "eq".
    Notation m := "m".
    Notation evenodd := "evenodd".
    Notation even := "even".
    Notation odd := "odd".
    Notation eo := "eo".

    Hint Extern 2 (has_type _ (app _ _) _) => eapply T_App; auto : db.
    Hint Extern 2 (has_type _ (tlcase _ _ _ _) _) => eapply T_Lcase; auto : db.
    Hint Extern 2 (_ = _) => compute; reflexivity : db.

    Module Numtest.

      Definition test :=
        test0
          (prd
             (scc
                (prd
                   (mlt
                      (const 2)
                      (const 0)))))
          (const 5)
          (const 6).

      Example typechecks :
        empty |- test ? Nat.
      Proof.
        unfold test.
        auto 10 with db.
      Qed.

      Example numtest_reduces :
        test -->* const 5.
      Proof.
        unfold test.
        normalize.
      Qed.

    End Numtest.

    Module Prodtest.

      Definition test :=
        tsnd
          (tfst
             (tpair
                (tpair
                   (const 5)
                   (const 6))
                (const 7))).

      Example typechecks :
        empty |- test ? Nat.
      Proof.
        unfold test.
        eapply T_Snd.
        eapply T_Fst.
        apply T_Pair.
        - apply T_Pair.
          + apply T_Nat.
          + apply T_Nat.
        - apply T_Nat.
      Qed.

      Example reduces :
        test -->* const 6.
      Proof. unfold test. normalize. Qed.

    End Prodtest.

    Module LetTest.

      Definition test :=
        tlet
          x
          (prd (const 6))
          (scc (var x)).

      Example typechecks :
        empty |- test ? Nat.
      Proof.
        unfold test.
        eapply T_Let.
        - auto with db.
        - auto with db.
      Qed.

      Example reduces :
        test -->* const 6.
      Proof.
        unfold test.
        eapply multi_step.
        - apply ST_Let1. apply ST_PredNat.
        - simpl.
          eapply multi_step.
          + apply ST_LetValue. apply v_nat.
          + simpl. eapply multi_step.
            * apply ST_SuccNat.
            * apply multi_refl.
      Qed.

    End LetTest.

    Module Sumtest1.

      Definition test :=
        tcase (tinl Nat (const 5))
              x (var x)
              y (var y).

      Example typechecks :
        empty |- test ? Nat.
      Proof.
        unfold test.
        eapply T_Case.
        - apply T_Inl. apply T_Nat.
        - apply T_Var. rewrite update_eq. reflexivity.
        - apply T_Var. rewrite update_eq. reflexivity.
      Qed.

      Example reduces:
        test -->* (const 5).
      Proof.
        unfold test.
        eapply multi_step.
        - eapply ST_CaseInl. apply v_nat.
        - simpl. apply multi_refl.
      Qed.

    End Sumtest1.

    Module Sumtest2.

      Definition test :=
        tlet
          processSum
          (abs x (Sum Nat Nat)
               (tcase (var x)
                      n (var n)
                      n (test0 (var n) (const 1) (const 0))))
          (tpair
             (app (var processSum) (tinl Nat (const 5)))
             (app (var processSum) (tinr Nat (const 5)))).

      Example typechecks :
        empty |- test ? (Prod Nat Nat).
      Proof.
        unfold test.
        eapply T_Let.
        - apply T_Abs. eapply T_Case.
          + apply T_Var. rewrite update_eq. reflexivity.
          + apply T_Var. rewrite update_eq. reflexivity.
          + apply T_Test0.
            * apply T_Var. rewrite update_eq. reflexivity.
            * apply T_Nat.
            * apply T_Nat.
        - apply T_Pair.
          + eapply T_App.
            * apply T_Var. rewrite update_eq. reflexivity.
            * apply T_Inl. apply T_Nat.
          + eapply T_App.
            * apply T_Var. rewrite update_eq. reflexivity.
            * apply T_Inr. apply T_Nat.
      Qed.

      Example reduces :
        test -->* (tpair (const 5) (const 0)).
      Proof.
        unfold test. normalize.
      Qed.

    End Sumtest2.

    Module ListTest.

      Definition test :=
        tlet l
             (tcons (const 5) (tcons (const 6) (tnil Nat)))
             (tlcase (var l)
                     (const 0)
                     x y (mlt (var x) (var x))).

      Example typechecks :
        empty |- test ? Nat.
      Proof.
        unfold test.
        eapply T_Let.
        - apply T_Cons.
          + apply T_Nat.
          + apply T_Cons.
            * apply T_Nat.
            * apply T_Nil.
        - eapply T_Lcase.
          + apply T_Var. rewrite update_eq. reflexivity.
          + apply T_Nat.
          + apply T_Mult; apply T_Var; rewrite update_eq; reflexivity.
      Qed.

      Example reduces :
        test -->* (const 25).
      Proof.
        unfold test.
        eapply multi_step.
        - apply ST_LetValue. apply v_lcons.
          + apply v_nat.
          + apply v_lcons.
            * apply v_nat.
            * apply v_lnil.
        - simpl. eapply multi_step.
          + apply ST_LcaseCons.
            * apply v_nat.
            * apply v_lcons.
              { apply v_nat. }
              { apply v_lnil. }
          + simpl. eapply multi_step.
            * apply ST_Mulconsts.
            * simpl. apply multi_refl.
      Qed.

    End ListTest.

    Module FixTest1.

      Definition fact :=
        tfix
          (abs f (Arrow Nat Nat)
               (abs a Nat
                    (test0
                       (var a)
                       (const 1)
                       (mlt
                          (var a)
                          (app (var f) (prd (var a))))))).

      Example typechecks :
        empty |- fact ? (Arrow Nat Nat).
      Proof.
        unfold fact.
        apply T_Fix. apply T_Abs. apply T_Abs.
        apply T_Test0.
        - apply T_Var. rewrite update_eq. reflexivity.
        - apply T_Nat.
        - apply T_Mult.
          + apply T_Var. rewrite update_eq. reflexivity.
          + eapply T_App.
            * apply T_Var. rewrite update_neq.
              { rewrite update_eq. reflexivity. }
              { intro H. inversion H. }
            * apply T_Pred. apply T_Var. rewrite update_eq. reflexivity.
      Qed.

      Example reduces :
        (app fact (const 4)) -->* (const 24).
      Proof.
        unfold fact.
        eapply multi_step.
        - apply ST_App1. apply ST_FixAbs.
        - simpl. eapply multi_step.
          + apply ST_AppAbs. apply v_nat.
          + simpl. eapply multi_step.
            * apply ST_Test0Nonzero.
            * eapply multi_step.
              { apply ST_Mult2.
                { apply v_nat. }
                { apply ST_App1. apply ST_FixAbs. }
              }
              { simpl. eapply multi_step.
                { apply ST_Mult2.
                  { apply v_nat. }
                  { apply ST_App2.
                    { apply v_abs. }
                    { apply ST_PredNat. }
                  }
                }
                { eapply multi_step. 
                  { apply ST_Mult2.
                    { apply v_nat. }
                    { simpl. apply ST_AppAbs. apply v_nat. }
                  }
                  { simpl. eapply multi_step.
                    { apply ST_Mult2.
                      { apply v_nat. }
                      { apply ST_Test0Nonzero. }
                    }
                    { eapply multi_step.
                      { apply ST_Mult2.
                        { apply v_nat. }
                        { apply ST_Mult2.
                          { apply v_nat. }
                          { apply ST_App1. apply ST_FixAbs. }
                        }
                      }
                      { eapply multi_step.
                        { simpl. apply ST_Mult2.
                          { apply v_nat. }
                          { apply ST_Mult2.
                            { apply v_nat. }
                            { apply ST_App2.
                              { apply v_abs. }
                              { apply ST_PredNat. }
                            }
                          }
                        }
                        { simpl. eapply multi_step.
                          { apply ST_Mult2.
                            { apply v_nat. }
                            { apply ST_Mult2.
                              { apply v_nat. }
                              { apply ST_AppAbs. apply v_nat. }
                            }
                          }
                          { simpl. eapply multi_step.
                            { apply ST_Mult2.
                              { apply v_nat. }
                              { apply ST_Mult2.
                                { apply v_nat. }
                                { apply ST_Test0Nonzero. }
                              }
                            }
                            { eapply multi_step.
                              { apply ST_Mult2.
                                { apply v_nat. }
                                { apply ST_Mult2.
                                  { apply v_nat. }
                                  { apply ST_Mult2.
                                    { apply v_nat. }
                                    { apply ST_App1. apply ST_FixAbs. }
                                  }
                                }
                              }
                              { eapply multi_step.
                                { apply ST_Mult2.
                                  { apply v_nat. }
                                  { apply ST_Mult2.
                                    { apply v_nat. }
                                    { apply ST_Mult2.
                                      { apply v_nat. }
                                      { simpl. apply ST_App2.
                                        { apply v_abs. }
                                        { apply ST_PredNat. }
                                      }
                                    }
                                  }
                                }
                                { eapply multi_step.
                                  { apply ST_Mult2.
                                    { apply v_nat. }
                                    { apply ST_Mult2.
                                      { apply v_nat. }
                                      { apply ST_Mult2.
                                        { apply v_nat. }
                                        { apply ST_AppAbs. simpl. apply v_nat. }
                                      }
                                    }
                                  }
                                  { simpl. eapply multi_step.
                                    { apply ST_Mult2.
                                      { apply v_nat. }
                                      { apply ST_Mult2.
                                        { apply v_nat. }
                                        { apply ST_Mult2.
                                          { apply v_nat. }
                                          { apply ST_Test0Nonzero. }
                                        }
                                      }
                                    }
                                    { eapply multi_step.
                                      { apply ST_Mult2.
                                        { apply v_nat. }
                                        { apply ST_Mult2.
                                          { apply v_nat. }
                                          { apply ST_Mult2.
                                            { apply v_nat. }
                                            { apply ST_Mult2.
                                              { apply v_nat. }
                                              { apply ST_App1. apply ST_FixAbs. }
                                            }
                                          }
                                        }
                                      }
                                      { simpl. eapply multi_step.
                                        { apply ST_Mult2.
                                          { apply v_nat. }
                                          { apply ST_Mult2.
                                            { apply v_nat. }
                                            { apply ST_Mult2.
                                              { apply v_nat. }
                                              { apply ST_Mult2.
                                                { apply v_nat. }
                                                { apply ST_App2.
                                                  { apply v_abs. }
                                                  { apply ST_PredNat. }
                                                }
                                              }
                                            }
                                          }
                                        }
                                        { eapply multi_step.
                                          { apply ST_Mult2.
                                            { apply v_nat. }
                                            { apply ST_Mult2.
                                              { apply v_nat. }
                                              { apply ST_Mult2.
                                                { apply v_nat. }
                                                { apply ST_Mult2.
                                                  { apply v_nat. }
                                                  { apply ST_AppAbs.  simpl. apply v_nat. }
                                                }
                                              }
                                            }
                                          }
                                          { simpl. eapply multi_step.
                                            { apply ST_Mult2.
                                              { apply v_nat. }
                                              { apply ST_Mult2.
                                                { apply v_nat. }
                                                { apply ST_Mult2.
                                                  { apply v_nat. }
                                                  { apply ST_Mult2.
                                                    { apply v_nat. }
                                                    { apply ST_Test0Zero. }
                                                  }
                                                }
                                              }
                                            }
                                            { eapply multi_step.
                                              { apply ST_Mult2.
                                                { apply v_nat. }
                                                { apply ST_Mult2.
                                                  { apply v_nat. }
                                                  { apply ST_Mult2.
                                                    { apply v_nat. }
                                                    { apply ST_Mulconsts. }
                                                  }
                                                }
                                              }
                                              { simpl. eapply multi_step.
                                                { eapply ST_Mult2.
                                                  { apply v_nat. }
                                                  { apply ST_Mult2.
                                                    { apply v_nat. }
                                                    { apply ST_Mulconsts. 
                                                    }
                                                  }
                                                }
                                                { simpl. eapply multi_step.
                                                  { apply ST_Mult2.
                                                    { apply v_nat. }
                                                    { apply ST_Mulconsts. }
                                                  }
                                                  { simpl. eapply multi_step.
                                                    { apply ST_Mulconsts. }
                                                    { simpl. apply multi_refl. }
                                                  }
                                                }
                                              }
                                            }
                                          }
                                        }
                                      }
                                    }
                                  }
                                }
                              }
                            }
                          }
                        }
                      }
                    }
                  }
                }
              }
      Qed.

    End FixTest1.

    Module FixTest2.

      Definition map :=
        abs g (Arrow Nat Nat)
            (tfix
               (abs f (Arrow (List Nat) (List Nat))
                    (abs l (List Nat)
                         (tlcase (var l)
                                 (tnil Nat)
                                 a l (tcons (app (var g) (var a))
                                            (app (var f) (var l))))))).

      Example typechecks :
        empty |- map ? (Arrow (Arrow Nat Nat)
                              (Arrow (List Nat)
                                     (List Nat))).
      Proof.
        unfold map.
        apply T_Abs. apply T_Fix. apply T_Abs. apply T_Abs.
        eapply T_Lcase.
        - apply T_Var. rewrite update_eq. reflexivity.
        - apply T_Nil.
        - apply T_Cons.
          + eapply T_App.
            * apply T_Var. rewrite update_neq. rewrite update_neq.
              rewrite update_neq. rewrite update_neq. rewrite update_eq.
              reflexivity.
              intro H; inversion H.
              intro H; inversion H.
              intro H; inversion H.
              intro H; inversion H.
            * apply T_Var. rewrite update_eq. reflexivity.
          + eapply T_App.
            * apply T_Var. rewrite update_neq. rewrite update_neq.
              rewrite update_neq. rewrite update_eq.
              reflexivity.
              intro H; inversion H.
              intro H; inversion H.
              intro H; inversion H.
            * apply T_Var. rewrite update_neq. rewrite update_eq.
              reflexivity.
              intro H; inversion H.
      Qed.

      Example reduces :
        app (app map (abs a Nat (scc (var a))))
            (tcons (const 1) (tcons (const 2) (tnil Nat)))
            -->* (tcons (const 2) (tcons (const 3) (tnil Nat))).
      Proof.
        unfold map. normalize.
      Qed.

    End FixTest2.
    
    Module FixTest3.
      
      Definition equal :=
        tfix
          (abs eq (Arrow Nat (Arrow Nat Nat))
               (abs m Nat
                    (abs n Nat
                         (test0 (var m)
                                (test0 (var n) (const 1) (const 0))
                                (test0 (var n)
                                       (const 0)
                                       (app (app (var eq)
                                                 (prd (var m)))
                                            (prd (var n)))))))).
      Example typechecks :
        empty |- equal ? (Arrow Nat (Arrow Nat Nat)).
      Proof.
        unfold equal.
        apply T_Fix. apply T_Abs. apply T_Abs. apply T_Abs.
        apply T_Test0.
        - apply T_Var. rewrite update_neq. rewrite update_eq.
          reflexivity. intro H; inversion H.
        - apply T_Test0.
          + apply T_Var. rewrite update_eq. reflexivity.
          + apply T_Nat.
          + apply T_Nat.
        - apply T_Test0.
          + apply T_Var. rewrite update_eq. reflexivity.
          + apply T_Nat.
          + eapply T_App.
            * eapply T_App.
              { apply T_Var. rewrite update_neq. rewrite update_neq.
                rewrite update_eq. reflexivity. intro H; inversion H.
                intro H; inversion H.
              }
              { apply T_Pred. apply T_Var. rewrite update_neq.
                rewrite update_eq. reflexivity. intro H; inversion H.
              }
            * apply T_Pred. apply T_Var. rewrite update_eq. reflexivity.
      Qed.
      
      Example reduces :
        (app (app equal (const 4)) (const 4)) -->* (const 1).
        Proof.
          unfold equal. normalize.
        Qed.
        
        Example reduces2 :
          (app (app equal (const 4)) (const 5)) -->* (const 0).
        Proof.
          unfold equal. normalize.
        Qed.
        
    End FixTest3.
    
    Module FixTest4.
      
      Definition eotest :=
        tlet evenodd
             (tfix
                (abs eo (Prod (Arrow Nat Nat) (Arrow Nat Nat))
                     (tpair
                        (abs n Nat
                             (test0 (var n)
                                    (const 1)
                                    (app (tsnd (var eo)) (prd (var n)))))
                        (abs n Nat
                             (test0 (var n)
                                    (const 0)
                                    (app (tfst (var eo)) (prd (var n))))))))
             (tlet even (tfst (var evenodd))
                   (tlet odd (tsnd (var evenodd))
                         (tpair
                            (app (var even) (const 3))
                            (app (var even) (const 4))))).
      
      Example typechecks :
        empty |- eotest ? (Prod Nat Nat).
      Proof.
          unfold eotest.
          eapply T_Let.
          - apply T_Fix. apply T_Abs. apply T_Pair.
            + apply T_Abs. apply T_Test0.
              * apply T_Var. rewrite update_eq. reflexivity.
              * apply T_Nat.
              * eapply T_App.
                { eapply T_Snd. apply T_Var. rewrite update_neq.
                  rewrite update_eq. reflexivity.
                  intro H; inversion H.
                }
                { apply T_Pred. apply T_Var. rewrite update_eq. reflexivity. }
            + apply T_Abs. apply T_Test0.
              * apply T_Var. rewrite update_eq. reflexivity.
              * apply T_Nat.
              * eapply T_App.
                { eapply T_Fst. apply T_Var. rewrite update_neq.
                  rewrite update_eq. reflexivity.
                  intro H; inversion H.
                }
                { apply T_Pred. apply T_Var. rewrite update_eq. auto. }
          - eapply T_Let.
            + eapply T_Fst. apply T_Var. rewrite update_eq. auto.
            + eapply T_Let.
              * eapply T_Snd. apply T_Var. rewrite update_neq.
                rewrite update_eq. auto. intro H; inversion H.
              * apply T_Pair.
                { eapply T_App.
                  { apply T_Var. rewrite update_neq. rewrite update_eq.
                    auto. intro H; inversion H. }
                  { apply T_Nat. }
                }
                { eapply T_App.
                  { apply T_Var. rewrite update_neq. rewrite update_eq.
                    auto. intro H; inversion H.
                  }
                  { apply T_Nat. }
                } 
        Qed.

      Example reduces :
        eotest -->* (tpair (const 0) (const 1)).
      Proof.
        unfold eotest. normalize.
      Qed.
      
    End FixTest4.
  End Examples.

  Theorem progress : forall t T,
      empty |- t ? T ->
      value t \/ exists t', t --> t'.
  Proof.
    intros t.
    induction t.
    - intros T H. inversion H.
      rewrite apply_empty in H2. inversion H2.
    - intros T H. inversion H. subst.
      apply IHt1 in H3. destruct H3.
      + apply IHt2 in H5. destruct H5.
        * right. inversion H0.
          { eexists. apply ST_AppAbs. apply H1. }
          { rewrite <- H2 in H. inversion H. inversion H6. }
          { rewrite <- H3 in H. inversion H. inversion H7. }
          { rewrite <- H3 in H. inversion H. inversion H7. }
          { rewrite <- H2 in H. inversion H. inversion H6. }
          { rewrite <- H4 in H. inversion H. inversion H8. }
          { rewrite <- H2 in H. inversion H. inversion H6. }
          { rewrite <- H4 in H. inversion H. inversion H8. }
        * right. destruct H1. eexists.
          apply (ST_App2 _ _ _ H0 H1).
      + destruct H0. right. eexists. apply (ST_App1 _ _ _ H0).
    - intros T H. left. apply v_abs.
    - intros T H. left. apply v_nat.
    - intros T H. right. inversion H; subst. apply IHt in H2.
      destruct H2.
      + inversion H. subst. inversion H0; subst; try inversion H3.
        eexists. apply ST_SuccNat.
      + destruct H0. exists (scc x). apply (ST_Succ1 _ _ H0).
    - intros T H. right. inversion H; subst. apply IHt in H2.
      destruct H2.
      + inversion H. subst. inversion H0; subst; try inversion H3.
        eexists. apply ST_PredNat.
      + destruct H0. exists (prd x). apply (ST_Pred _ _ H0).
    - intros T H. right. inversion H; subst. apply IHt1 in H3.
      apply IHt2 in H5. destruct H3.
      + destruct H5.
        * inversion H; subst.
          inversion H5; subst; try (inversion H0).
          inversion H6; subst; try (inversion H1).
          eexists. apply ST_Mulconsts.
        * destruct H1. eexists. apply ST_Mult2; eassumption.
      + destruct H0. eexists. apply ST_Mult1. apply H0.
    - intros T H. right. inversion H; subst.
      assert (H8: value t1 \/ (exists t' : tm, t1 --> t')).
      { apply (IHt1 Nat). apply H4. }
      destruct H8.
      + inversion H0; subst; try inversion H4.
        destruct n1; subst.
        * eexists. apply ST_Test0Zero.
        * eexists. apply ST_Test0Nonzero.
      + destruct H0. eexists. apply ST_Test01. apply H0.
    - intros T H. inversion H; subst.
      assert (H5 : value t0 \/ (exists t' : tm, t0 --> t')).
      { eapply IHt. apply H4. }
      destruct H5.
      + left. apply v_inl. apply H0.
      + right. destruct H0. eexists. apply ST_Inl. apply H0.
    - intros T H. inversion H; subst.
      assert (H5 : value t0 \/ (exists t' : tm, t0 --> t')).
      { eapply IHt. apply H4. }
      destruct H5.
      + left. apply v_inr. apply H0.
      + right. destruct H0. eexists. apply ST_Inr. apply H0.
    - intros T H. right. inversion H; subst.
      assert (H10: value t1 \/ (exists t' : tm, t1 --> t')).
      { apply (IHt1 (Sum T1 T2) H7). }
      inversion H7; subst.
      + inversion H0.
      + destruct H10.
        * inversion H2.
        * destruct H2. eexists. apply ST_Case. apply H2.
      + destruct H10.
        * inversion H3.
        * destruct H3. eexists. eapply ST_Case. apply H3.
      + destruct H10.
        * eexists. apply ST_CaseInl. inversion H0. apply H2.
        * destruct H0. eexists. apply ST_Case. apply H0.
      + destruct H10.
        * eexists. apply ST_CaseInr. inversion H0. apply H2.
        * destruct H0. eexists. apply ST_Case. apply H0.
      + destruct H10.
        * inversion H3.
        * destruct H3. eexists. eapply ST_Case. apply H3.
      + destruct H10.
        * inversion H3.
        * destruct H3. eexists. eapply ST_Case. apply H3.
      + destruct H10.
        * inversion H1.
        * destruct H1. eexists. eapply ST_Case. apply H1.
      + destruct H10.
        * inversion H1.
        * destruct H1. eexists. eapply ST_Case. apply H1.
      + destruct H10.
        * inversion H2.
        * destruct H2. eexists. eapply ST_Case. apply H2.
      + destruct H10.
        * inversion H1.
        * destruct H1. eexists. eapply ST_Case. apply H1.
    - intros T H. left. apply v_lnil.
    - intros T H. inversion H; subst.
      assert (H6 : value t1 \/ (exists t' : tm, t1 --> t')).
      { apply (IHt1 T1 H3). }
      assert (H7 : value t2 \/ (exists t' : tm, t2 --> t')).
      { apply (IHt2 (List T1) H5). }
      destruct H6.
      + destruct H7.
        * left. apply v_lcons; assumption.
        * right. destruct H1. eexists. apply ST_Cons2; eassumption.
      + right. destruct H0. eexists. apply ST_Cons1; eassumption.
    - intros T H. inversion H; subst.
      assert (H10 : value t1 \/ (exists t' : tm, t1 --> t')).
      { apply (IHt1 (List T1) H7). }
      destruct H10.
      + right. inversion H0; subst; try inversion H7.
        * subst. eexists. apply ST_LcaseNil.
        * subst. eexists. apply ST_LcaseCons; assumption.
      + right. destruct H0. eexists. apply ST_Lcase1. apply H0.
    - intros T H. left. apply v_unit.
    - intros T H. inversion H; subst.
      assert (H6 : value t1 \/ (exists t' : tm, t1 --> t')).
      { apply (IHt1 _ H3). }
      assert (H7 : value t2 \/ (exists t' : tm, t2 --> t')).
      { apply (IHt2 _ H5). }
      destruct H6.
      + destruct H7.
        * left. apply v_pair; assumption.
        * right. destruct H1. eexists. apply ST_Pair2; eassumption.
      + destruct H0. right. eexists. apply ST_Pair1. apply H0.
    - intros T H. inversion H; subst.
      assert (H3 : value t \/ (exists t' : tm, t --> t')).
      { apply (IHt _ H2). }
      destruct H3.
      + inversion H0; subst; inversion H2; subst. right.
        eexists. apply ST_FstPair; assumption.
      + destruct H0. right. eexists. apply ST_Fst. apply H0.
    - intros T H. inversion H; subst.
      assert (H3 : value t \/ (exists t' : tm, t --> t')).
      { apply (IHt _ H2). }
      destruct H3.
      + inversion H0; subst; inversion H2; subst. right.
        eexists. apply ST_SndPair; assumption.
      + destruct H0. right. eexists. apply ST_Snd. apply H0.
    - intros T H. inversion H; subst.
      assert (H7 : value t1 \/ (exists t' : tm, t1 --> t')).
      { apply (IHt1 _ H5). }
      destruct H7.
      + right. eexists. apply ST_LetValue. apply H0.
      + destruct H0. right. eexists. apply ST_Let1. apply H0.
    - intros T H. inversion H; subst.
      assert (H3 : value t \/ (exists t' : tm, t --> t')).
      { apply (IHt _ H2). }
      destruct H3.
      + inversion H0; subst; try inversion H2; subst.
        right. eexists. apply ST_FixAbs.
      + destruct H0. right. eexists. apply ST_Fix1. apply H0.
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
  (* numbers *)
  | afi_succ : forall x t,
     appears_free_in x t ->
     appears_free_in x (scc t)
  | afi_pred : forall x t,
     appears_free_in x t ->
     appears_free_in x (prd t)
  | afi_mult1 : forall x t1 t2,
     appears_free_in x t1 ->
     appears_free_in x (mlt t1 t2)
  | afi_mult2 : forall x t1 t2,
     appears_free_in x t2 ->
     appears_free_in x (mlt t1 t2)
  | afi_test01 : forall x t1 t2 t3,
     appears_free_in x t1 ->
     appears_free_in x (test0 t1 t2 t3)
  | afi_test02 : forall x t1 t2 t3,
     appears_free_in x t2 ->
     appears_free_in x (test0 t1 t2 t3)
  | afi_test03 : forall x t1 t2 t3,
     appears_free_in x t3 ->
     appears_free_in x (test0 t1 t2 t3)
  (* sums *)
  | afi_inl : forall x t T,
      appears_free_in x t ->
      appears_free_in x (tinl T t)
  | afi_inr : forall x t T,
      appears_free_in x t ->
      appears_free_in x (tinr T t)
  | afi_case0 : forall x t0 x1 t1 x2 t2,
      appears_free_in x t0 ->
      appears_free_in x (tcase t0 x1 t1 x2 t2)
  | afi_case1 : forall x t0 x1 t1 x2 t2,
      x1 <> x ->
      appears_free_in x t1 ->
      appears_free_in x (tcase t0 x1 t1 x2 t2)
  | afi_case2 : forall x t0 x1 t1 x2 t2,
      x2 <> x ->
      appears_free_in x t2 ->
      appears_free_in x (tcase t0 x1 t1 x2 t2)
  (* lists *)
  | afi_cons1 : forall x t1 t2,
     appears_free_in x t1 ->
     appears_free_in x (tcons t1 t2)
  | afi_cons2 : forall x t1 t2,
     appears_free_in x t2 ->
     appears_free_in x (tcons t1 t2)
  | afi_lcase1 : forall x t1 t2 y1 y2 t3,
     appears_free_in x t1 ->
     appears_free_in x (tlcase t1 t2 y1 y2 t3)
  | afi_lcase2 : forall x t1 t2 y1 y2 t3,
     appears_free_in x t2 ->
     appears_free_in x (tlcase t1 t2 y1 y2 t3)
  | afi_lcase3 : forall x t1 t2 y1 y2 t3,
     y1 <> x ->
     y2 <> x ->
     appears_free_in x t3 ->
     appears_free_in x (tlcase t1 t2 y1 y2 t3)
  (* pairs *)
  | afi_pairL : forall x t1 t2,
      appears_free_in x t1 ->
      appears_free_in x (tpair t1 t2)
  | afi_pairR : forall x t1 t2,
      appears_free_in x t2 ->
      appears_free_in x (tpair t1 t2)
  | afi_fst : forall x t,
      appears_free_in x t ->
      appears_free_in x (tfst t)
  | afi_snd : forall x t,
      appears_free_in x t ->
      appears_free_in x (tsnd t)
  (* let *)
  | afi_let1 : forall x y t1 t2,
      appears_free_in x t1 ->
      appears_free_in x (tlet y t1 t2)
  | afi_let2 : forall x y t1 t2,
      y <> x ->
      appears_free_in x t2 ->
      appears_free_in x (tlet y t1 t2)
  (* fix *)
  | afi_fix1 : forall x xf,
      appears_free_in x xf ->
      appears_free_in x (tfix xf).
Hint Constructors appears_free_in : db.

Lemma context_invariance : forall Gamma Gamma' t S,
     Gamma |- t ? S ->
     (forall x, appears_free_in x t -> Gamma x = Gamma' x) ->
     Gamma' |- t ? S.
Proof with eauto 30 with db.
  intros. generalize dependent Gamma'.
  induction H; intros Gamma' Heqv...
  - apply T_Var... rewrite <- Heqv...
  - apply T_Abs... apply IHhas_type. intros y Hafi.
    unfold update, t_update.
    destruct (eqb_stringP x y)...
  - eapply T_Case...
    + apply IHhas_type2. intros y Hafi.
      unfold update, t_update.
      destruct (eqb_stringP x1 y)...
    + apply IHhas_type3. intros y Hafi.
      unfold update, t_update.
      destruct (eqb_stringP x2 y)...
  - eapply T_Lcase... apply IHhas_type3. intros y Hafi.
    unfold update, t_update.
    destruct (eqb_stringP x1 y)...
    destruct (eqb_stringP x2 y)...
  - eapply T_Let...
    apply IHhas_type2.
    intros y Hafi. unfold update, t_update.
    destruct (eqb_stringP x y)...
Qed.

Lemma free_in_context : forall x t T Gamma,
   appears_free_in x t ->
   Gamma |- t ? T ->
   exists T', Gamma x = Some T'.
Proof with eauto with db.
  intros x t T Gamma Hafi Htyp.
  induction Htyp; inversion Hafi; subst...
  - destruct IHHtyp as [T' Hctx]... exists T'.
    unfold update, t_update in Hctx.
    rewrite false_eqb_string in Hctx...
  - destruct IHHtyp2 as [T' Hctx]... exists T'.
    unfold update, t_update in Hctx.
    rewrite false_eqb_string in Hctx...
  - destruct IHHtyp3 as [T' Hctx]... exists T'.
    unfold update, t_update in Hctx.
    rewrite false_eqb_string in Hctx...
  - clear Htyp1 IHHtyp1 Htyp2 IHHtyp2.
    destruct IHHtyp3 as [T' Hctx]... exists T'.
    unfold update, t_update in Hctx.
    rewrite false_eqb_string in Hctx...
    rewrite false_eqb_string in Hctx...
  - destruct IHHtyp2 as [T' Hctx]... exists T'.
    unfold update, t_update in Hctx.
    rewrite false_eqb_string in Hctx...
Qed.

Lemma substitution_preserves_typing : forall Gamma x U v t S,
    (x |-> U; Gamma) |- t ? S ->
    empty |- v ? U ->
    Gamma |- ([x := v]t) ? S.
Proof with eauto with db.
  intros Gamma x U v t S Htypt Htypv.
  generalize dependent Gamma. generalize dependent S.
  induction t; intros S Gamma Htypt; simpl; inversion Htypt; subst...
  - simpl. rename s into y.
    unfold update, t_update in H1.
    destruct (eqb_stringP x y).
    + subst. inversion H1; subst. clear H1.
      eapply context_invariance...
      intros x Hcontra.
      destruct (free_in_context _ _ S empty Hcontra) as [T' HT']...
      inversion HT'.
    + apply T_Var...
  - rename s into y. rename t into T11.
    apply T_Abs...
    destruct (eqb_stringP x y) as [Hxy | Hxy].
    + eapply context_invariance...
      subst.
      intros x Hafi. unfold update, t_update.
      destruct (eqb_string y x)...
    + apply IHt. eapply context_invariance...
      intros z Hafi. unfold update, t_update.
      destruct (eqb_stringP y z) as [Hyz | Hyz]...
      subst.
      rewrite false_eqb_string...
  - rename s into x1. rename s0 into x2.
    eapply T_Case...
    + destruct (eqb_stringP x x1) as [Hxx1 | Hxx1].
      * eapply context_invariance...
        subst.
        intros z Hafi. unfold update, t_update.
        destruct (eqb_string x1 z)...
      * apply IHt2. eapply context_invariance...
        intros z Hafi. unfold update, t_update.
        destruct (eqb_stringP x1 z) as [Hx1z | Hx1z]...
        subst.
        rewrite false_eqb_string...
    + destruct (eqb_stringP x x2) as [Hxx2 |Hxx2].
      * eapply context_invariance...
        subst.
        intros z Hafi. unfold update, t_update.
        destruct (eqb_string x2 z)...
      * apply IHt3. eapply context_invariance...
        intros z Hafi. unfold update, t_update.
        destruct (eqb_stringP x2 z)...
        subst. rewrite false_eqb_string...
  - rename s into y1. rename s0 into y2.
    eapply T_Lcase...
    destruct (eqb_stringP x y1).
    + (* x = y1 *)
      simpl.
      eapply context_invariance...
      subst.
      intros z Hafi. unfold update, t_update.
      destruct (eqb_stringP y1 z)...
    + (* x <> y1 *)
      destruct (eqb_stringP x y2).
      * (* x = y2 *)
        eapply context_invariance...
        subst.
        intros z Hafi. unfold update, t_update.
        destruct (eqb_stringP y2 z)...
      * (* x <> y2 *)
        apply IHt3. eapply context_invariance...
        intros z Hafi. unfold update, t_update.
        destruct (eqb_stringP y1 z)...
        subst. rewrite false_eqb_string...
        destruct (eqb_stringP y2 z)...
        subst. rewrite false_eqb_string...
  - rename s into y.
    destruct (eqb_stringP x y)...
    + subst. rewrite update_shadow in H5.
      eapply T_Let...
    + rewrite update_permute in H5.
      * apply IHt2 in H5. eapply T_Let...
      * apply n.
Qed.

Theorem perservation : forall t t' T,
    empty |- t ? T ->
    t --> t' ->
    empty |- t' ? T.
Proof with eauto with db.
  intros t t' T HT. generalize dependent t'.
  remember empty as Gamma.
  induction HT; intros t' HE; subst; inversion HE; subst...
  - (* T_App *)
    apply substitution_preserves_typing with T1...
    inversion HT1...
  - inversion HT1; subst...
    eapply substitution_preserves_typing...
  - inversion HT1; subst...
    eapply substitution_preserves_typing...
  - inversion HT1; subst.
    apply substitution_preserves_typing with (List T1)...
    apply substitution_preserves_typing with T1...
  - inversion HT; subst. apply H5.
  - inversion HT; subst. apply H7.
  - eapply substitution_preserves_typing...
  - inversion HT; subst. eapply substitution_preserves_typing...
Qed.
