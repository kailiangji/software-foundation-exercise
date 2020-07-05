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

