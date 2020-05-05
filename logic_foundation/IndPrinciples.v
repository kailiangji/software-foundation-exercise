Set Warnings "-notation-overridden,-parsing".
From LF Require Export ProofObjects.

Check nat_ind.

Theorem mult_O_r' : forall n : nat, n * 0 = 0.
Proof.
  apply nat_ind.
  - (* n = 0 *) reflexivity.
  - (* n = S n' *) simpl. intros n' IHn'.
    rewrite -> IHn'. reflexivity.
Qed.

Theorem plus_one_r' : forall n : nat, n + 1 = S n.
Proof.
  apply nat_ind.
  - reflexivity.
  - simpl. intros n' IHn'. rewrite IHn'. reflexivity.
Qed.

Inductive yesno : Type :=
| yes
| no.

Check yesno_rect.
Check yesno_ind.
Check yesno_rec.

Inductive rgb : Type :=
| red
| green
| blue.

Check rgb_ind.

Inductive natlist : Type :=
| nnil
| ncons (n : nat) (l : natlist).

Check natlist_ind.

Inductive natlist1 : Type :=
| nnil1
| nsnoc1 (l : natlist1) (n : nat).

Check natlist1_ind.

Inductive byntree : Type :=
| bempty
| bleaf (yn : yesno)
| nbranch (yn : yesno) (t1 t2 : byntree).

Check byntree_ind.

(*
  ExSet_ind :
    forall P : ExSet -> Prop,
               (forall b : bool, P (con1 b)) ->
               (forall (n : nat) (e : ExSet), P e -> P (con2 n e)) ->
               forall e : ExSet, P e
 *)

Inductive ExSet : Type :=
| con1 (b : bool)
| con2 (n : nat) (e : ExSet).

Check ExSet_ind.

Inductive tree (X : Type) : Type :=
| leaf (x : X)
| node (t1 t2 : tree X).

Check tree_ind.

(*
  mytype_ind :
    forall (X : Type) (P : mytype X -> Prop),
              (forall x : X, P (constr1 X x)) ->
              (forall n : nat, P (constr2 X n)) ->
              (forall m : mytype X, P m ->
                 forall n : nat, P (consr3 X m n)) ->
              forall m : mytype X, P m
 *)

Inductive mytype (X : Type) : Type :=
| constr1 (x : X)
| constr2 (n : nat)
| constr3 (m : mytype X) (n : nat).

Check mytype_ind.

(*
  foo_ind :
    forall (X Y : Type) (P : foo X Y -> Prop),
              (forall x : X, P (bar X Y x)) ->
              (forall y : Y, P (baz X Y y)) ->
              (forall f1 : nat -> foo X Y,
                 (forall n : nat, P (f1 n)) -> P (quux X Y f1)) ->
              forall f2 : foo X Y, P f2
 *)

Inductive foo (X Y : Type) : Type :=
| bar (x : X)
| baz (y : Y)
| quux (f1 : nat -> foo X Y).

Check foo_ind.

Inductive foo' (X : Type) : Type :=
| C1 (l : list X) (f : foo' X)
| C2.

Check foo'_ind.

Definition P_mOr (n : nat) : Prop :=
  n * 0 = 0.

Theorem mult_O_r'' : forall n : nat, P_mOr n.
Proof.
  apply nat_ind.
  - reflexivity.
  - intros n IHn.
    unfold P_mOr in *.
    simpl. apply IHn.
Qed.

Definition P_pcomm (n m : nat) : Prop :=
  n + m = m + n.

Theorem plus_comm' : forall n m : nat, P_pcomm n m.
Proof.
  intro n.
  apply nat_ind.
  - unfold P_pcomm. simpl. rewrite <- plus_n_O. reflexivity.
  - intros n0 IHm. unfold P_pcomm in *.
    simpl. rewrite <- IHm. rewrite <- plus_n_Sm. reflexivity.
Qed.

Definition P_passoc : nat -> nat -> nat -> Prop :=
  fun n => (fun m => (fun p => n + (m + p) = (n + m) + p)).

Theorem plus_assoc' : forall n m p : nat, P_passoc n m p.
Proof.
  intros n m.
  apply nat_ind.
  - unfold P_passoc. rewrite <- plus_n_O. rewrite <- plus_n_O.
    reflexivity.
  - intros n0 IH. unfold P_passoc in *.
    repeat rewrite <- plus_n_Sm. rewrite IH. reflexivity.
Qed.

Check even_ind.
Print even'.

Theorem ev_ev' : forall n , even n -> even' n.
Proof.
  apply even_ind.
  - apply even'_O.
  - intros m Hm IH.
    apply (even'_sum 2 m).
    + apply even'_2.
    + apply IH.
Qed.

Check le_ind.

Inductive le': nat -> nat -> Prop :=
  | le'_n : forall n, le' n n
  | le'_S : forall n m, (le' n m) -> (le' n (S m)).
Check le'_ind.
Check le_ind.

