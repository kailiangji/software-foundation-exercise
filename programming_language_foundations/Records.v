Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Strings.String.
Add LoadPath "/Users/jikl/demos/coq/software-foundation-exercise/logic_foundation" as LF.
From LF Require Import Maps.
From LF Require Import Imp.
From PLF Require Import SmallStep.
From PLF Require Import Stlc.

Module STLCExtendedRecords.

  Inductive ty : Type :=
  | Base : string -> ty
  | Arrow : ty -> ty -> ty
  | RNil : ty
  | RCons : string -> ty -> ty -> ty.

  Inductive tm : Type :=
  | var : string -> tm
  | app : tm -> tm -> tm
  | abs : string -> ty -> tm -> tm
  (* records *)
  | rproj : tm -> string -> tm
  | trnil : tm
  | rcons : string -> tm -> tm -> tm.

  Open Scope string_scope.
  Notation a := "a".
  Notation f := "f".
  Notation g := "g".
  Notation l := "l".
  Notation A := (Base "A").
  Notation B := (Base "B").
  Notation k := "k".
  Notation i1 := "i1".
  Notation i2 := "i2".

  Definition weird_type := RCons X A B.

  Inductive record_ty : ty -> Prop :=
  | RTnil : record_ty RNil
  | RTcons : forall i T1 T2, record_ty (RCons i T1 T2).

  Inductive well_formed_ty : ty -> Prop :=
  | wfBase : forall i, well_formed_ty (Base i)
  | wfArrow : forall T1 T2,
      well_formed_ty T1 ->
      well_formed_ty T2 ->
      well_formed_ty (Arrow T1 T2)
  | wfRNil :
      well_formed_ty RNil
  | wfRCons : forall i T1 T2,
      well_formed_ty T1 ->
      well_formed_ty T2 ->
      record_ty T2 ->
      well_formed_ty (RCons i T1 T2).

  Hint Constructors record_ty well_formed_ty : db.

  Inductive record_tm : tm -> Prop :=
  | rtnil : record_tm trnil
  | rtcons : forall i t1 t2, record_tm (rcons i t1 t2).

  Hint Constructors record_tm : db.

  Fixpoint subst (x:string) (s:tm) (t:tm) : tm :=
    match t with
    | var y => if eqb_string x y then s else t
    | abs y T t1 =>
      abs y T (if eqb_string x y then t1 else (subst x s t1))
    | app t1 t2 => app (subst x s t1) (subst x s t2)
    | rproj t1 i => rproj (subst x s t1) i
    | trnil => trnil
    | rcons i t1 tr1 => rcons i (subst x s t1) (subst x s tr1)
    end.

  Notation "'[' x ':=' s ']' t" := (subst x s t) (at level 20).

  Inductive value : tm -> Prop :=
  | v_abs : forall x T11 t12,
      value (abs x T11 t12)
  | v_rnil : value trnil
  | v_rcons : forall i v1 vr,
      value v1 ->
      value vr ->
      value (rcons i v1 vr).

  Fixpoint tlookup (i : string) (tr : tm) : option tm :=
    match tr with
    | rcons i' t tr' => if eqb_string i i' then Some t else tlookup i tr'
    | _ => None
    end.

  Reserved Notation "t1 '-->' t2" (at level 40).

  Inductive step : tm -> tm -> Prop :=
  | ST_AppAbs : forall x T11 t12 v2,
      value v2 ->
      (app (abs x T11 t12) v2) --> ([x:=v2]t12)
  | ST_App1 : forall t1 t1' t2,
      t1 --> t1' ->
      (app t1 t2) --> (app t1' t2)
  | ST_App2 : forall v1 t2 t2',
      value v1 ->
      t2 --> t2' ->
      (app v1 t2) --> (app v1 t2')
  | ST_Proj1 : forall t1 t1' i,
      t1 --> t1' ->
      (rproj t1 i) --> (rproj t1' i)
  | ST_ProjRcd : forall tr i vi,
      value tr ->
      tlookup i tr = Some vi ->
      (rproj tr i) --> vi
  | ST_Rcd_Head : forall i t1 t1' tr2,
      t1 --> t1' ->
      (rcons i t1 tr2) --> (rcons i t1' tr2)
  | ST_Rcd_Tail : forall i v1 tr2 tr2',
      value v1 ->
      tr2 --> tr2' ->
      (rcons i v1 tr2) --> (rcons i v1 tr2')
  where "t1 '-->' t2" := (step t1 t2).

  Notation multistep := (multi step).
  Notation "t1 '-->*' t2" := (multistep t1 t2) (at level 40).

  Hint Constructors step : db.

  Fixpoint Tlookup (i : string) (Tr : ty) : option ty :=
    match Tr with
    | RCons i' T Tr' =>
      if eqb_string i i' then Some T else Tlookup i Tr'
    | _ => None
    end.

  Definition context := partial_map ty.

  Reserved Notation "Gamma '|-' t '\in' T" (at level 40).

  Inductive has_type : context -> tm -> ty -> Prop :=
  | T_Var : forall Gamma x T,
      Gamma x = Some T ->
      well_formed_ty T ->
      Gamma |- (var x) \in T
  | T_Abs : forall Gamma x T11 T12 t12,
      well_formed_ty T11 ->
      (update Gamma x T11) |- t12 \in T12 ->
      Gamma |- (abs x T11 t12) \in (Arrow T11 T12)
  | T_App : forall T1 T2 Gamma t1 t2,
      Gamma |- t1 \in (Arrow T1 T2) ->
      Gamma |- t2 \in T1 ->
      Gamma |- (app t1 t2) \in T2
  | T_Proj : forall Gamma i t Ti Tr,
      Gamma |- t \in Tr ->
      Tlookup i Tr = Some Ti ->
      Gamma |- (rproj t i) \in Ti
  | T_RNil : forall Gamma,
      Gamma |- trnil \in RNil
  | T_RCons : forall Gamma i t T tr Tr,
      Gamma |- t \in T ->
      Gamma |- tr \in Tr ->
      record_ty Tr ->
      record_tm tr ->
      Gamma |- (rcons i t tr) \in (RCons i T Tr)
  where "Gamma '|-' t '\in' T" := (has_type Gamma t T).

  Hint Constructors has_type : db.

  Lemma typing_example_2 :
    empty |-
      (app (abs a (RCons i1 (Arrow A A)
                         (RCons i2 (Arrow B B)
                          RNil))
                (rproj (var a) i2))
              (rcons i1 (abs a A (var a))
              (rcons i2 (abs a B (var a))
               trnil))) \in
      (Arrow B B).
  Proof.
    eapply T_App.
    - eapply T_Abs.
      + apply wfRCons.
        * apply wfArrow; auto with db.
        * apply wfRCons.
          { apply wfArrow; auto with db. }
          { apply wfRNil. }
          { apply RTnil. }
        * apply RTcons.
      + eapply T_Proj.
        * apply T_Var.
          { rewrite update_eq. reflexivity. }
          { apply wfRCons.
            { apply wfArrow; auto with db. }
            { apply wfRCons.
              { apply wfArrow; auto with db. }
              { apply wfRNil. }
              { apply RTnil. }
            }
            { apply RTcons. }
          }
        * simpl. reflexivity.
    - eapply T_RCons.
      + apply T_Abs.
        * apply wfBase.
        * apply T_Var.
          { rewrite update_eq. reflexivity. }
          { apply wfBase. }
      + apply T_RCons.
        * apply T_Abs.
          { apply wfBase. }
          { apply T_Var.
            { rewrite update_eq. reflexivity. }
            { apply wfBase. }
          }
        * apply T_RNil.
        * apply RTnil.
        * apply rtnil.
      + apply RTcons.
      + apply rtcons.
  Qed.
