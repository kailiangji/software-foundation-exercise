Set Warnings "-notation-overridden,-parsing".
From LF Require Export IndProp.

Theorem ev_4' : even 4.
Proof.
  Show Proof.
  apply ev_SS.
  Show Proof.
  apply ev_SS.
  Show Proof.
  apply ev_O.
  Show Proof.
Qed.

Theorem ev_8 : even 8.
Proof.
  apply ev_SS.
  Show Proof.
  apply ev_SS.
  Show Proof.
  apply ev_4'.
  Show Proof.
Qed.

Definition ev_8' : even 8 := ev_SS 6 (ev_SS 4 (ev_SS 2 (ev_SS 0 ev_O))).
Print ev_8'.

Definition ev_plus2 : Prop :=
  forall n, forall (E : even n), even (n + 2).

Definition ev_plus2' : Prop :=
  forall n, forall(_ : even n), even (n + 2).

Definition ev_plus2'' : Prop :=
  forall n, even n -> even (n + 2).

Definition add1 : nat -> nat.
  intro n.
  Show Proof.
  apply S.
  Show Proof.
  apply n.
  Show Proof.
Defined.

Module Props.

  Module And.
    
    Inductive and (P Q : Prop) : Prop :=
    | conj : P -> Q -> and P Q.
    
  End And.

  Print prod.

  Lemma and_comm : forall P Q : Prop, P /\ Q <-> Q /\ P.
  Proof.
    intros P Q.
    Show Proof.
    split.
    Show Proof.
    - intros [HP HQ].
      Show Proof.
      split.
      + apply HQ.
        Show Proof.
      + apply HP.
        Show Proof.
    - Show Proof.
      intros [HQ HP].
      Show Proof.
      split.
      + apply HP.
        Show Proof.
      + apply HQ.
        Show Proof.
  Defined.
  Print and_comm.
  Eval compute in and_comm True False.

  Definition and_comm'_aux P Q (H : P /\ Q) : Q /\ P :=
    match H with
    | conj HP HQ => conj HQ HP
    end.

  Definition and_comm' P Q : P /\ Q <-> Q /\ P :=
    conj (and_comm'_aux P Q) (and_comm'_aux Q P).
  
  Goal forall P Q : Prop, P /\ Q <-> Q /\ P.
  Proof. apply and_comm'. Qed.

  Definition conj_fact : forall P Q R, P /\ Q -> Q /\ R -> P /\ R.
    intros P Q R.
    intros [HP HQ].
    intros [_ HR].
    split.
    - apply HP.
    - apply HR.
  Defined.
  Print conj_fact.

  Module Or.
    Inductive or (P Q : Prop) : Prop :=
    | or_introl : P -> or P Q
    | or_intror : Q -> or P Q.
  End Or.

  Definition or_comm : forall P Q, P \/ Q -> Q \/ P :=    
    let aux P Q (H : P \/ Q) : Q \/ P :=
        match H with
        | or_introl P => or_intror P
        | or_intror Q => or_introl Q
        end
    in
    fun P Q => aux P Q.

  Goal forall P Q, P \/ Q -> Q \/ P.
  Proof. apply or_comm. Qed.

  Module Ex.

    Inductive ex {A : Type} (P : A -> Prop) : Prop :=
    | ex_intro : forall x : A, P x -> ex P.
    
  End Ex.

  Check ex.
  Check ex (fun n => even n).
  Check (fun n => even n).
  Check ex even.

  Definition some_nat_is_even : exists n, even n :=
    ex_intro even 4 (ev_SS 2 (ev_SS 0 ev_O)).

  Check ex_intro.
  Check even.
  Check ex_intro even.
  Check ex_intro even 2.
  Check ex_intro even 2 (ev_SS 0 ev_O).

  Check even.
  Check (fun n => even (S n)).
  Check (ex_intro even).
  Check (ex (fun n => even (S n))).
  Definition ex_ev_Sn : ex (fun n => even (S n)) :=
    ex_intro (fun x => even (S x)) 3 (ev_SS 2 (ev_SS 0 ev_O)).

  Inductive True : Prop :=
  | I : True.

  Inductive False : Prop := .

End Props.

Module MyEquality.

  Inductive eq {X : Type} : X -> X -> Prop :=
  | eq_refl : forall x, eq x x.

  Notation "x == y" := (eq x y) (at level 70, no associativity) : type_scope.

  Lemma four : 2 + 3 == 1 + 4.
  Proof. apply eq_refl. Qed.

  Definition four' : 2 + 2 == 1 + 3 :=
    eq_refl 4.

  Definition singleton : forall (X : Type) (x : X), [] ++ [x] == x :: [].
    intros X x.
    apply (eq_refl [x]).
  Defined.

  Lemma equality__leibniz_equality : forall (X : Type) (x y : X),
      x == y -> forall P : X -> Prop, P x -> P y.
  Proof.
    intros X x y eq P H.
    inversion eq. rewrite <- H1.
    apply H.
  Qed.

  Lemma leibniz_equality__equality : forall (X : Type) (x y : X),
      (forall P : X -> Prop, P x -> P y) -> x == y.
  Proof.
    intros X x y H.
    apply (H (eq x)).
    apply eq_refl.
  Qed.
End MyEquality.

Fixpoint mult (n : nat) (m : nat) : nat :=
  match m with
  | 0 => 0
  | S m' => n + (mult n m')
  end.

Definition mult2: nat -> nat.
  intro n.
  induction n as [| n' IH].
  - Show Proof.
    apply O.
  - apply S. apply S. apply IH.
Defined.
Compute (mult2 10).

  Definition mult': nat -> nat -> nat.
    intros n m.
    induction m as [| m' IH].
    - Show Proof.
      apply O.
    - Show Proof.
      apply (plus n).
      Show Proof.
      apply IH.
  Defined.
  Compute (mult' 10 10).