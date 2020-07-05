Set Warnings "-notation-overridden,-parsing".
Add LoadPath "/Users/jikl/demos/coq/software-foundation-exercise/logic_foundation" as LF.
Add LoadPath "/Users/jikl/demos/coq/software-foundation-exercise/programming_language_foundations" as PLF.
From Coq Require Import Strings.String.
From LF Require Import Maps.
From Coq Require Import Bool.Bool.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Arith.PeanoNat. Import Nat.
From Coq Require Import omega.Omega.
From PLF Require Import Hoare.
From LF Require Import Imp.

Definition reduce_to_zero' : com :=
  (WHILE ~( X = 0) DO
     X ::= X - 1
   END)%imp.

Theorem reduce_to_zero_correct' :
  {{fun st => True}}
    reduce_to_zero'
  {{fun st => st X = 0}}.
Proof.
  unfold reduce_to_zero'.
  eapply hoare_consequence_post.
  - apply hoare_while.
    eapply hoare_consequence_pre.
    + apply hoare_asgn.
    + unfold assert_implies, assn_sub. auto.
  - unfold assert_implies.
    intros st [_ H].
    unfold bassn in H. simpl in H.
    apply eq_true_negb_classical in H.
    rewrite eqb_eq in H. apply H.
Qed.

Fixpoint parity x :=
  match x with
  | 0 => 0
  | 1 => 1
  | S (S x') => parity x'
  end.

Lemma parity_ge_2 : forall x,
    2 <= x -> parity (x - 2) = parity x.
Proof.
  intros x H.
  induction x as [|x' IH].
  - omega.
  - destruct x' as [|x''].
    + omega.
    + simpl. rewrite sub_0_r. reflexivity.
Qed.

Lemma parity_lt_2 : forall x,
    ~ 2 <= x ->
    parity (x) = x.
Proof.
  intros x H.
  destruct x as [| x'].
  - reflexivity.
  - destruct x' as [|x''].
    + reflexivity.
    + omega.
Qed.

Theorem parity_correct : forall m,
    {{fun st => st X = m}}
      WHILE 2 <= X DO
        X ::= X - 2
      END
    {{fun st => st X = parity m}}.
Proof.
  intro m.
  eapply hoare_consequence_post.
  - eapply hoare_consequence_pre.
    + Print hoare_while.
      apply (hoare_while (fun st => parity (st X) = parity m)).
      eapply hoare_consequence_pre.
      * apply hoare_asgn.
      * unfold assert_implies, assn_sub.
        intros st [H1 H2].
        rewrite t_update_eq.
        simpl in *. rewrite <- H1.
        apply parity_ge_2.
        unfold bassn in H2.
        simpl in H2.
        destruct (st X).
        { inversion H2. }
        { destruct n.
          { inversion H2. }
          { omega. }
        }
    + unfold assert_implies.
      intros st H.
      rewrite H. reflexivity.
  - unfold assert_implies.
    intros st [H1 H2].
    unfold bassn in H2.
    simpl in H2. destruct (st X).
    + simpl in H1. apply H1.
    + destruct n.
      * simpl in H1. apply H1.
      * exfalso. apply H2. reflexivity.
Qed.

Definition is_wp P c Q :=
  {{P}} c {{Q}} /\
  forall P', {{P'}} c {{Q}} -> (P' ->> P).

Theorem is_wp_example :
  is_wp (fun st => st Y <= 4)
        (X ::= Y + 1) (fun st => st X <= 5).
Proof.
  unfold is_wp.
  split.
  - eapply hoare_consequence_pre.
    + apply hoare_asgn.
    + unfold assert_implies, assn_sub.
      intros st H.
      rewrite t_update_eq. simpl. omega.
  - unfold assert_implies.
    intros.
    unfold hoare_triple in H.
    assert (H' : (X !-> (st Y + 1); st) X <= 5).
    { apply (H st).
      + eapply E_Ass. reflexivity.
      + apply H0.
    }
    rewrite t_update_eq in H'.
    omega.
Qed.

Theorem hoare_asgn_weakest : forall Q X a,
    is_wp (Q [X |-> a]) (X ::= a) Q.
Proof.
  unfold is_wp.
  intros Q X a. split.
  - apply hoare_asgn.
  - unfold assert_implies, assn_sub.
    intros.
    unfold hoare_triple in H.
    apply (H st).
    eapply E_Ass.
    + reflexivity.
    + apply H0.
Qed.

Module Himp2.
  Import Himp.

  Lemma hoare_havoc_weakest : forall (P Q : Assertion) (X : string),
      {{ P }} HAVOC X {{ Q }} ->
      P ->> havoc_pre X Q.
  Proof.
    unfold havoc_pre.
    intros.
    unfold assert_implies.
    intros st H1.
    intro n.
    unfold hoare_triple in H.
    apply (H st).
    - apply E_Havoc.
    - apply H1.
  Qed.

End Himp2.

Inductive dcom : Type :=
| DCSkip : Assertion -> dcom
| DCSeq : dcom -> dcom -> dcom
| DCAsgn : string -> aexp -> Assertion -> dcom
| DCIf : bexp -> Assertion -> dcom -> Assertion -> dcom -> Assertion -> dcom
| DCWhile : bexp -> Assertion -> dcom -> Assertion -> dcom
| DCPre : Assertion -> dcom -> dcom
| DCPost : dcom -> Assertion -> dcom.

Inductive decorated : Type :=
| Decorated : Assertion -> dcom -> decorated.

Declare Scope default.

Declare Scope dcom_scope.

Notation "'SKIP' {{ P }}" := (DCSkip P) (at level 10) : dcom_scope.

Notation "l '::=' a {{ P }}"
  := (DCAsgn l a P)
       (at level 60, a at next level) : dcom_scope.
Notation "'WHILE' b 'DO' {{ Pbody }} d 'END' {{ Ppost }}"
  := (DCWhile b Pbody d Ppost)
       (at level 80, right associativity) : dcom_scope.
Notation "'TEST' b 'THEN' {{ P }} d 'ELSE' {{ P' }} d' 'FI' {{ Q }}"
  := (DCIf b P d P' d' Q)
       (at level 80, right associativity) : dcom_scope.
Notation "'->>' {{ P }} d"
  := (DCPre P d)
       (at level 90, right associativity) : dcom_scope.
Notation "d '->>' {{ P }}"
  := (DCPost d P)
       (at level 80, right associativity) : dcom_scope.
Notation " d ;; d' "
  := (DCSeq d d')
       (at level 80, right associativity) : dcom_scope.
Notation "{{ P }} d"
  := (Decorated P d)
       (at level 90) : dcom_scope.

Open Scope dcom_scope.

Example dec0 :=
  SKIP {{ fun st => True }}.

Example dec1 :=
  WHILE true DO {{ fun st => True }} SKIP {{ fun st => True }} END
  {{ fun st => True }}.

Set Printing All.

Example dec_while : decorated :=
  {{ fun st => True }}
  WHILE ~(X = 0) DO
    {{ fun st => True /\ st X <> 0 }}
    X ::= X - 1    
    {{ fun _ => True}}
  END
  {{ fun st => True /\ st X = 0}} ->>
  {{ fun st => st X = 0 }}.

Fixpoint extract (d : dcom) : com :=
  match d with
  | DCSkip _ => SKIP
  | DCSeq d1 d2 => (extract d1 ;; extract d2)
  | DCAsgn X a _ => X ::= a
  | DCIf b _ d1 _ d2 _ => TEST b THEN extract d1 ELSE extract d2 FI
  | DCWhile b _ d _ => WHILE b DO extract d END
  | DCPre _ d => extract d
  | DCPost d _ => extract d
  end.

Definition extract_dec (dec : decorated) : com :=
  match dec with
  | Decorated P d => extract d
  end.

Fixpoint post (d : dcom) : Assertion :=
  match d with
  | DCSkip P => P
  | DCSeq d1 d2 => post d2
  | DCAsgn X a Q => Q
  | DCIf _ _ d1 _ d2 Q => Q
  | DCWhile b Pbody c Ppost => Ppost
  | DCPre _ d => post d
  | DCPost c Q => Q
  end.

Definition pre_dec (dec : decorated) : Assertion :=
  match dec with
  | Decorated P d => P
  end.

Definition post_dec (dec : decorated) : Assertion :=
  match dec with
  | Decorated P d => post d
  end.

Definition dec_correct (dec : decorated) :=
  {{pre_dec dec}} (extract_dec dec) {{post_dec dec}}.

Fixpoint verification_conditions (P : Assertion) (d : dcom) : Prop :=
  match d with
  | DCSkip Q =>
    (P ->> Q)
  | DCSeq d1 d2 =>
    verification_conditions P d1
    /\ verification_conditions (post d1) d2
  | DCAsgn X a Q =>
    (P ->> Q [X |-> a])
  | DCIf b P1 d1 P2 d2 Q =>
    ((fun st => P st /\ bassn b st) ->> P1)
      /\ ((fun st => P st /\ ~(bassn b st)) ->> P2)
      /\ (post d1 ->> Q) /\ (post d2 ->> Q)
      /\ verification_conditions P1 d1
      /\ verification_conditions P2 d2
  | DCWhile b Pbody d Ppost =>
    (P ->> post d)
    /\ ((fun st => post d st /\ bassn b st) ->> Pbody)
    /\ ((fun st => post d st /\ ~(bassn b st)) ->> Ppost)
    /\ verification_conditions Pbody d
  | DCPre P' d =>
    (P ->> P') /\ verification_conditions P' d
  | DCPost d Q =>
    verification_conditions P d /\ (post d ->> Q)
  end.

