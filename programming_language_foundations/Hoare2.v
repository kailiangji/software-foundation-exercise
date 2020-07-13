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

(* Set Printing All.*)

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
  | DCSkip Q => (P ->> Q)
  | DCSeq d1 d2 => verification_conditions P d1 /\
                   verification_conditions (post d1) d2
  | DCAsgn X a Q => (P ->> Q [X |-> a])
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

Theorem verification_correct : forall d P,
    verification_conditions P d -> {{ P }} (extract d) {{ post d }}.
Proof.
  intros d. induction d.
  - intros P H. simpl in *.
    eapply hoare_consequence_pre.
    + apply hoare_skip.
    + apply H.
  - intros P H. simpl in *. destruct H as [H1 H2].
    eapply hoare_seq.
    + apply IHd2. apply H2.
    + apply IHd1. apply H1.
  - intros P H. simpl in *.
    eapply hoare_consequence_pre.
    + apply hoare_asgn.
    + apply H.
  - intros P H. simpl in *.
    destruct H as [H1 [H2 [H3 [H4 [H5 H6]]]]].
    eapply hoare_consequence_pre.
    + apply hoare_if. 
      * unfold hoare_triple.
        intros st st' H7 [H8 H9].
        unfold assert_implies in H3.
        apply H3. unfold hoare_triple in IHd1.
        eapply IHd1.
        { apply H5. }
        { apply H7. }
        { unfold assert_implies in H1. apply H1. split; eassumption. }
      * unfold hoare_triple.
        intros st st' H7 [H8 H9].
        unfold assert_implies in H4.
        apply H4. unfold hoare_triple in IHd2.
        eapply IHd2.
        { apply H6. }
        { apply H7. }
        { unfold assert_implies in H2. apply H2. split; eassumption. }
    + unfold assert_implies. auto.
  - intros P H.
    simpl in *.
    destruct H as [H1 [H2 [H3 H4]]].
    apply IHd in H4.
    apply (hoare_consequence_pre _ (post d)).
    + eapply hoare_consequence_post.
      * apply hoare_while.
        eapply hoare_consequence_pre.
        { apply H4. }
        { apply H2. }
      * apply H3.
    + apply H1.
  - intros P H.
    simpl in *.
    destruct H as [H1 H2].
    eapply hoare_consequence_pre.
    + apply (IHd _ H2).
    + apply H1.
  - intros P H.
    simpl in *.
    destruct H as [H1 H2].
    eapply hoare_consequence_post.
    + apply (IHd _ H1).
    + apply H2.
Qed.

Definition verification_conditions_dec (dec : decorated) : Prop :=
  match dec with
  | Decorated P d => verification_conditions P d
  end.

Lemma verification_correct_dec : forall dec,
    verification_conditions_dec dec -> dec_correct dec.
Proof.
  intros dec.
  destruct dec.
  unfold dec_correct.
  simpl in *.
  apply verification_correct.
Qed.

Eval simpl in (verification_conditions_dec dec_while).

Tactic Notation "verify" :=
  apply verification_correct;
  repeat split;
  simpl; unfold assert_implies;
  unfold bassn in *; unfold beval in *; unfold aeval in *;
  unfold assn_sub; intros;
  repeat rewrite t_update_eq;
  repeat (rewrite t_update_neq; [| (intro X; inversion X)]);
  simpl in *;
  repeat match goal with [H : _ /\ _ |- _] => destruct H end;
  repeat rewrite not_true_iff_false in *;
  repeat rewrite not_false_iff_true in *;
  repeat rewrite negb_true_iff in *;
  repeat rewrite negb_false_iff in *;
  repeat rewrite eqb_eq in *;
  repeat rewrite eqb_neq in *;
  repeat rewrite leb_iff in *;
  repeat rewrite leb_iff_conv in *;
  try subst;
  repeat
    match goal with
      [st : state |- _ ] =>
      match goal with
        [H : st _ = _ |- _] => rewrite -> H in *; clear H
      | [H : _ = st _ |- _] => rewrite <- H in *; clear H
      end
    end;
  try eauto; try omega.

Theorem dec_while_correct :
  dec_correct dec_while.
Proof. verify. Qed.

Example subtract_slowly_dec (m : nat) (p : nat) : decorated :=
    {{ fun st => st X = m /\ st Z = p }} ->>
    {{ fun st => st Z - st X = p - m }}
  WHILE ~(X = 0)
  DO {{ fun st => st Z - st X = p - m /\ st X <> 0 }} ->>
       {{ fun st => (st Z - 1) - (st X - 1) = p - m }}
     Z ::= Z - 1
       {{ fun st => st Z - (st X - 1) = p - m }} ;;
     X ::= X - 1
       {{ fun st => st Z - st X = p - m }}
  END
    {{ fun st => st Z - st X = p - m /\ st X = 0 }} ->>
    {{ fun st => st Z = p - m }}.

Theorem subtract_slowly_dec_correct : forall m p,
    dec_correct (subtract_slowly_dec m p).
Proof. intros m p. verify. Qed.

Definition swap : com :=
  X ::= X + Y;;
  Y ::= X - Y;;
  X ::= X - Y.

Definition swap_dec m n : decorated :=
  {{fun st => st X = m /\ st Y = n}} ->>
  {{fun st => (st X + st Y) - (st X + st Y - st Y) = n /\ (st X + st Y) - st Y = m}}
  X ::= X + Y
  {{fun st => st X - (st X - st Y) = n /\ st X - st Y = m}};;
  Y ::= X - Y
  {{fun st => st X - st Y = n /\ st Y = m}};;
  X ::= X - Y
  {{fun st => st X = n /\ st Y = m}}.

Theorem swap_correct : forall m n,
    dec_correct (swap_dec m n).
Proof. intros m n. verify. Qed.

Definition if_minus_plus_com :=
  (TEST X <= Y
    THEN Z ::= Y - X
    ELSE Y ::= X + Z
   FI)%imp.

Definition if_minus_plus_dec :=
  {{fun st => True}}
  TEST X <= Y THEN
      {{ fun st => True /\ st X <= st Y }} ->>
      {{ fun st => st Y = st X + (st Y - st X) }}
    Z ::= Y - X
      {{ fun st => st Y = st X + st Z }}
  ELSE
      {{ fun st => True /\ ~(st X <= st Y) }} ->>
      {{ fun st => st X + st Z = st X + st Z }}
    Y ::= X + Z
      {{ fun st => st Y = st X + st Z }}
  FI
  {{fun st => st Y = st X + st Z}}.

Theorem if_minus_plus_correct :
  dec_correct if_minus_plus_dec.
Proof. verify. Qed.

Definition if_minus_dec :=
  {{fun st => True}}
  TEST X <= Y THEN
      {{fun st => True /\ st X <= st Y }} ->>
      {{fun st => (st Y - st X) + st X = st Y
               \/ (st Y - st X) + st Y = st X}}
    Z ::= Y - X
      {{fun st => st Z + st X = st Y \/ st Z + st Y = st X}}
  ELSE
      {{fun st => True /\ ~(st X <= st Y) }} ->>
      {{fun st => (st X - st Y) + st X = st Y
               \/ (st X - st Y) + st Y = st X}}
    Z ::= X - Y
      {{fun st => st Z + st X = st Y \/ st Z + st Y = st X}}
  FI
    {{fun st => st Z + st X = st Y \/ st Z + st Y = st X}}.

Theorem if_minus_correct :
  dec_correct if_minus_dec.
Proof. verify. Qed.

Definition div_mod_dec (a b : nat) : decorated :=
  {{ fun st => True }} ->>
  {{ fun st => b * 0 + a = a }}
  X ::= a
  {{ fun st => b * 0 + st X = a }};;
  Y ::= 0
  {{ fun st => b * st Y + st X = a }};;
  WHILE b <= X DO
    {{ fun st => b * st Y + st X = a /\ b <= st X }} ->>
    {{ fun st => b * (st Y + 1) + (st X - b) = a }}
    X ::= X - b
    {{ fun st => b * (st Y + 1) + st X = a }};;
    Y ::= Y + 1
    {{ fun st => b * st Y + st X = a }}
  END
  {{ fun st => b * st Y + st X = a /\ ~(b <= st X) }} ->>
  {{ fun st => b * st Y + st X = a /\ (st X < b) }}.

Theorem div_mod_dec_correct : forall a b,
  dec_correct (div_mod_dec a b).
Proof. intros a b. verify.
  rewrite mult_plus_distr_l. omega.
Qed.

Definition find_parity : com :=
  WHILE 2 <= X DO
     X ::= X - 2
  END.

Inductive ev : nat -> Prop :=
| ev_O : ev 0
| ev_SS (n : nat) : ev n -> ev (S (S n)).

Definition find_parity_dec m : decorated :=
  {{fun st => st X = m}} ->>
  {{fun st => ev m -> ev (st X)}}
  WHILE 2 <= X DO
    {{fun st => ev m -> ev (st X) /\ 2 <= st X}} ->>
    {{fun st => ev m -> ev (st X - 2)}}
    X ::= X - 2
    {{fun st => ev m -> ev (st X)}}
  END
  {{fun st => ev m -> ev (st X) /\ st X < 2}} ->>              
  {{fun st => ev m -> ev (st X)}}.

Theorem find_parity_correct : forall m,
  dec_correct (find_parity_dec m).
Proof.
  intro m. verify.
  - destruct (st X).
    + inversion H1.
    + apply H in H0.
      inversion H0. omega.
  - destruct (st X).
    + omega.
    + destruct n.
      * omega.
      * inversion H1.
  - apply H in H0.
    destruct H0 as [H1 H2].
    inversion H1.
    + rewrite <- H3 in H2. inversion H2.
    + simpl. rewrite sub_0_r. apply H3.
  - apply H. apply H0.
Qed.

Definition sqrt_dec m : decorated :=
    {{ fun st => st X = m }} ->>
    {{ fun st => st X = m /\ 0 * 0 <= m }}
  Z ::= 0
    {{ fun st => st X = m /\ st Z * st Z <= m }};;
  WHILE (Z+1)*(Z+1) <= X DO
      {{ fun st => (st X = m /\ st Z*st Z <= m)
                   /\ (st Z + 1)*(st Z + 1) <= st X }} ->>
      {{ fun st => st X = m /\ (st Z+1)*(st Z+1) <= m }}
    Z ::= Z + 1
      {{ fun st => st X = m /\ st Z*st Z <= m }}
  END
    {{ fun st => (st X = m /\ st Z*st Z <= m)
                   /\ ~((st Z + 1)*(st Z + 1) <= st X) }} ->>
    {{ fun st => st Z*st Z <= m /\  m < (st Z+1)*(st Z+1) }}.

Theorem sqrt_correct : forall m,
  dec_correct (sqrt_dec m).
Proof. intro m. verify. Qed.

Definition two_loops_dec (a b c : nat) : decorated :=
  {{ fun st => True }} ->>
  {{ fun st => c = 0 + c /\ 0 = 0 }}
  X ::= 0
  {{ fun st => c = st X + c /\ 0 = 0 }};;
  Y ::= 0
  {{ fun st => c = st X + c /\ st Y = 0 }};;
  Z ::= c
  {{ fun st => st Z = st X + c /\ st Y = 0 }};;
  WHILE ~(X = a) DO
    {{ fun st => (st Z = st X + c /\ st Y = 0) /\ st X <> a }} ->>
    {{ fun st => st Z + 1 = st X + 1 + c /\ st Y = 0 }}
    X ::= X + 1
    {{ fun st => st Z + 1 = st X + c /\ st Y = 0 }};;
    Z ::= Z + 1
    {{ fun st => st Z = st X + c /\ st Y = 0 }}
  END
  {{ fun st => (st Z = st X + c /\ st Y = 0) /\ st X = a }} ->>
  {{ fun st => st Z = a + st Y + c }};;
  WHILE ~(Y = b) DO
    {{ fun st => st Z = a + st Y + c /\ st Y <> b }} ->>
    {{ fun st => st Z + 1 = a + st Y + 1 + c }}
    Y ::= Y + 1
    {{ fun st => st Z + 1 = a + st Y + c }};;
    Z ::= Z + 1
    {{ fun st => st Z = a + st Y + c }}
  END
  {{ fun st => (st Z = a + st Y + c) /\ st Y = b }} ->>
  {{ fun st => st Z = a + b + c }}.

Theorem two_loops_correct : forall a b c,
    dec_correct (two_loops_dec a b c).
Proof. intros a b c. verify. Qed.

Fixpoint pow2 n :=
  match n with
  | 0 => 1
  | S n' => 2 * (pow2 n')
  end.

Definition dpow2_down (n : nat) :=
  {{ fun st => True }} ->>
  {{ fun st => 1 = (pow2 (0 + 1))-1 /\ 1 = pow2 0 }}
  X ::= 0
  {{ fun st => 1 = (pow2 (0 + 1))-1 /\ 1 = pow2 (st X) }};;
  Y ::= 1
  {{ fun st => st Y = (pow2 (st X + 1))-1 /\ 1 = pow2 (st X) }};;
  Z ::= 1
  {{ fun st => st Y = (pow2 (st X + 1))-1 /\ st Z = pow2 (st X) }};;
  WHILE ~(X = n) DO
    {{ fun st => (st Y = (pow2 (st X + 1))-1 /\ st Z = pow2 (st X))
                 /\ st X <> n }} ->>
    {{ fun st => st Y + 2 * st Z = (pow2 (st X + 2))-1
                 /\ 2 * st Z = pow2 (st X + 1) }}
    Z ::= 2 * Z
    {{ fun st => st Y + st Z = (pow2 (st X + 2))-1
                 /\ st Z = pow2 (st X + 1) }};;
    Y ::= Y + Z
    {{ fun st => st Y = (pow2 (st X + 2))-1
                 /\ st Z = pow2 (st X + 1) }};;
    X ::= X + 1
    {{ fun st => st Y = (pow2 (st X + 1))-1
                 /\ st Z = pow2 (st X) }}
  END
  {{ fun st => (st Y = (pow2 (st X + 1))-1 /\ st Z = pow2 (st X))
               /\ st X = n }} ->>
  {{ fun st => st Y = pow2 (n+1) - 1 }}.

Lemma pow2_plus_1 : forall n,
  pow2 (n+1) = pow2 n + pow2 n.
Proof. induction n; simpl. reflexivity. omega. Qed.

Lemma pow2_le_1 : forall n, pow2 n >= 1.
Proof. induction n. simpl. constructor. simpl. omega. Qed.

Theorem dpow2_down_correct : forall n,
  dec_correct (dpow2_down n).
Proof.
  intro m. verify.
  - (* 1 *)
    rewrite pow2_plus_1. rewrite <- H0. reflexivity.
  - (* 2 *)
    rewrite <- plus_n_O.
    rewrite <- pow2_plus_1. remember (st X) as n.
    replace (pow2 (n + 1) - 1 + pow2 (n + 1))
       with (pow2 (n + 1) + pow2 (n + 1) - 1) by omega.
    rewrite <- pow2_plus_1.
    replace (n + 1 + 1) with (n + 2) by omega.
    reflexivity.
  - (* 3 *)
    rewrite <- plus_n_O. rewrite <- pow2_plus_1.
    reflexivity.
  - (* 4 *)
    replace (st X + 1 + 1) with (st X + 2) by omega.
    reflexivity.
Qed.

Example slow_assignment_dec (m : nat) : decorated :=
  {{ fun st => st X = m }} ->>
  {{ fun st => st X + 0 = m}}
  Y ::= 0
  {{ fun st => st X + st Y = m }};;
  WHILE ~(X = 0) DO
    {{ fun st => st X + st Y = m /\ st X <> 0 }} ->>
    {{ fun st => (st X - 1) + (st Y + 1) = m }}
    X ::= X - 1
    {{ fun st => st X + (st Y + 1) = m }};;
    Y ::= Y + 1
    {{ fun st => st X + st Y = m }}
  END
  {{ fun st => st X + st Y = m /\ st X = 0 }} ->>
  {{ fun st => st Y = m }}.

Theorem slow_assignment_dec_correct : forall m,
    dec_correct (slow_assignment_dec m).
Proof. intro m. verify. Qed.

