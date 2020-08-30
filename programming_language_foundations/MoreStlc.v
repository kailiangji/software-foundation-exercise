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

  
