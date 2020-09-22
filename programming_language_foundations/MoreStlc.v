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
  | pair : tm -> tm -> tm
  | fst : tm -> tm
  | snd : tm -> tm
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
    | pair t1 t2 =>
      pair (subst x s t1) (subst x s t2)
    | fst t1 =>
      fst (subst x s t1)
    | snd t1 =>
      snd (subst x s t1)
    | tlet y t1 t2 =>
      if eqb_string x y then tlet y t1 t2
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
      value (pair v1 v2).

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
  | ST_Let1 : forall x t1 t1' t2,
      t1 --> t1' ->
      (tlet x t1 t2) --> (tlet x t1' t2)
  | ST_LetValue : forall x v1 t2 t2',
      value v1 ->
      t2 --> t2' ->
      (tlet x v1 t2) --> (tlet x v1 t2')
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
  | T_Prd : forall Gamma t1,
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
      Gamma |- (pair t1 t2) ? (Prod T1 T2)
  | T_Let : forall Gamma x t1 T1 t2 T2,
      Gamma |- t1 ? T1 ->
      (x |-> T1; Gamma) |- t2 ? T2 ->
      Gamma |- tlet x t1 t2 ? T2
  | T_Fix : forall Gamma t1 T1,
      Gamma |- t1 ? (Arrow T1 T1) ->
      Gamma |- (tfix t1) ? T1
  where "Gamma '|-' t '?' T" := (has_type Gamma t T).

  Hint Constructors has_type : db.
