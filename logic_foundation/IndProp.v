Set Warnings "-notation-overridden,-parsing".
From LF Require Export Logic.
Require Coq.omega.Omega.

Inductive even : nat -> Prop :=
| ev_O : even 0
| ev_SS (n : nat) (H : even n) : even (S (S n)).

Theorem ev_double : forall n, even (double n).
Proof.
  intro n. induction n as [| n' IHn'].
  - apply ev_O.
  - simpl. apply (ev_SS (double n') IHn').
Qed.

Theorem ev_inversion : forall (n : nat),
    even n ->
    (n = 0) \/ (exists n', n = S (S n') /\ even n').
Proof.
  intros n H. inversion H.
  - left. reflexivity.
  - right. exists n0. split.
    + reflexivity.
    + apply H0.
Qed.

Theorem SSSSev__even : forall n,
    even (S (S (S (S n)))) -> even n.
Proof.
  intros n H. apply ev_inversion in H.
  destruct H.
  - discriminate H.
  - destruct H as [n' [H1 H2]].
    apply ev_inversion in H2.
    destruct H2.
    + rewrite H in H1. discriminate H1.
    + destruct H as [n'0 [H2 H3]]. rewrite H2 in H1.
      inversion H1. apply H3.
Qed.

Theorem even5_nonsense : even 5 -> 2 + 2 = 9.
Proof.
  intro H. inversion H. inversion H1. inversion H3.
Qed.

Lemma ev_even : forall n,
    even n -> exists k, n = double k.
Proof.
  intros n H. induction H as [| n' H' IH].
  - exists 0. reflexivity.
  - destruct IH as [k IH].
    exists (S k). simpl. rewrite IH. reflexivity.
Qed.

Theorem ev_even_iff : forall n,
    even n <-> exists k, n = double k.
Proof.
  intro n. split.
  - apply ev_even.
  - intros [k Hk]. rewrite Hk. apply ev_double.
Qed.

Theorem ev_sum : forall n m, even n -> even m -> even (n + m).
Proof.
  intros n m Hn Hm.
  induction Hn as [|n' Hn' IH].
  - simpl. apply Hm.
  - simpl. apply ev_SS. apply IH.
Qed.

Inductive even' : nat -> Prop :=
| even'_O : even' 0
| even'_2 : even' 2
| even'_sum n m (Hn : even' n) (Hm : even' m) : even' (n + m).

Theorem even'_ev : forall n, even' n <-> even n.
Proof.
  intro n. split.
  - intro H. induction H.
    + constructor.
    + constructor. constructor.
    + apply ev_sum; [apply IHeven'1 | apply IHeven'2].
  - intro H. induction H.
    + constructor.
    + assert (H' : S (S n) = 2 + n). { reflexivity. }
      rewrite H'. apply even'_sum; [constructor | apply IHeven].
Qed.

Theorem ev_ev__ev : forall n m,
    even (n + m) -> even n -> even m.
Proof.
  intros n m H1 H2. induction H2 as [| n' H2' IH].
  - simpl in H1. apply H1.
  - apply IH. simpl in H1. inversion H1. apply H0.
Qed.

Theorem ev_plus_plus : forall n m p,
    even (n + m) -> even (n + p) -> even (m + p).
Proof.
  intros n m p H1 H2.
  apply (ev_ev__ev (n+p) (m+p)).
  - assert (H: n + p + (m + p) = (n + m) + (p + p)).
    { assert (H' : m + p = p + m).
      { apply plus_comm. }
      rewrite H'. rewrite plus_assoc. rewrite plus_comm.
      assert (H'': n + p + p = n + (p + p)).
      rewrite plus_assoc. reflexivity. rewrite H''.
      rewrite plus_assoc. rewrite (plus_comm n m).
      reflexivity. }
    rewrite H. apply ev_sum. apply H1. rewrite <- double_plus.
    apply ev_double.
  - apply H2.
Qed.

Module Playground.
  Inductive le : nat -> nat -> Prop :=
  | le_n n : le n n
  | le_S n m (H : le n m) : le n (S m).

  Notation "m <= n" := (le m n).

  Example test_le1 : 3 <= 3.
  Proof. apply (le_n 3). Qed.

  Example test_le2 : 3 <= 6.
  Proof.
    apply (le_S 3 5). apply (le_S 3 4). apply (le_S 3 3).
    apply (le_n 3).
  Qed.

  Example test_le3 : (2 <= 1) -> 2 + 2 = 5.
  Proof. intro H. inversion H. inversion H2. Qed.

End Playground.

Definition lt (n m : nat) := le (S n) m.

Notation "m < n" := (lt m n).

Inductive square_of : nat -> nat -> Prop :=
| sq n : square_of n (n * n).

Inductive next_nat : nat -> nat -> Prop :=
| nn n : next_nat n (S n).

Inductive next_even : nat -> nat -> Prop :=
| ne_1 n : even (S n) -> next_even n (S n)
| ne_2 n (H : even (S (S n))) : next_even n (S (S n)).

Inductive total_relation : nat -> nat -> Prop :=
| re_n n : total_relation n n
| arti_sym m n : total_relation m n -> total_relation m (S n).

Inductive empty_relation : nat -> Prop :=
| empty_n n : n < 0 -> empty_relation n.

Lemma le_trans : forall m n o, m <= n -> n <= o -> m <= o.
Proof.
  intros m n o H1 H2. induction H2.
  - assumption.
  - apply le_S. assumption.
Qed.

Theorem O_le_n : forall n, 0 <= n.
Proof.
  intro n. induction n as [| n' IHn'].
  - constructor.
  - apply le_S. apply IHn'.
Qed.

Theorem n_le_m__Sn_le_Sm : forall n m,
    n <= m -> S n <= S m.
Proof.
  intros n m H. induction H.
  - apply le_n.
  - apply (le_trans (S n) (S m) (S (S m))).
    + apply IHle.
    + apply le_S. apply le_n.
Qed.

Theorem Sn_le_Sm__n_le_m : forall n m,
    S n <= S m -> n <= m.
Proof.
  intros n m H. inversion H.
  - constructor.
  - apply (le_trans n (S n) m).
    + apply le_S. apply le_n.
    + apply H1.
Qed.

Theorem le_plus_1 : forall a b, a <= a + b.
Proof.
  intros a b. induction b as [| b' IH].
  - rewrite plus_comm. simpl. apply le_n.
  - rewrite plus_comm. simpl. rewrite plus_comm.
    apply le_S. apply IH.
Qed.

Theorem plus_lt : forall n1 n2 m,
    n1 + n2 < m -> n1 < m /\ n2 < m.
Proof.
  unfold lt. intros n1 n2 m H. split.
  - apply (le_trans (S n1) (S (n1 + n2)) m).
    induction n2 as [| n2' IH].
    + rewrite plus_comm. simpl. apply le_n.
    + rewrite plus_comm. simpl. rewrite plus_comm.
      rewrite plus_comm in H. simpl in H. rewrite plus_comm in H.
      apply (le_trans (S n1) (S (n1 + n2')) (S (S (n1 + n2')))).
      assert (H' : (S n1) + n2' = S (n1 + n2')).
      { simpl. reflexivity. }
      rewrite <- H'. apply le_plus_1.
      apply le_S. apply le_n.
    + apply H.
  - apply (le_trans (S n2) (S (n1 + n2)) m).
    + rewrite plus_comm.
      assert (H' : (S n2) + n1 = S(n2 + n1)).
      { simpl. reflexivity. }
      rewrite <- H'. apply le_plus_1.
    + apply H.
Qed.

Theorem lt_S : forall n m, n < m -> n < S m.
Proof.
  unfold lt. intros n m H.
  apply (le_trans (S n) m (S m)).
  - apply H.
  - apply le_S. apply le_n.
Qed.

Theorem leb_complete : forall n m,
    n <=? m = true -> n <= m.
Proof.
  intros n m.
  generalize dependent n.
  induction m as [|m' IHm].
  - intros n H. destruct n as [|n'].
    + apply le_n.
    + inversion H.
  - intros n H. destruct n as [|n'].
    + apply O_le_n.
    + simpl in H. apply IHm in H. apply n_le_m__Sn_le_Sm.
      apply H.
Qed.

Theorem leb_correct : forall n m,
    n <= m -> n <=? m = true.
Proof.
  intros n m. generalize dependent n.
  induction m as [| m' IHm'].
  - intros n H. inversion H. simpl. reflexivity.
  - intros n H. induction n as [| n' IHn'].
    + simpl. reflexivity.
    + simpl. apply IHm'. apply Sn_le_Sm__n_le_m. apply H.
Qed.

Theorem leb_true_trans : forall n m o,
    n <=? m = true -> m <=? o = true -> n <=? o = true.
Proof.
  intros n m o H1 H2.
  apply leb_correct.
  apply leb_complete in H1.
  apply leb_complete in H2.
  apply (le_trans n m o); assumption.
Qed.

Theorem leb_iff : forall n m,
    n <=? m = true <-> n <= m.
Proof. split; [apply leb_complete | apply leb_correct]. Qed.

Module R.

  Inductive R : nat -> nat -> nat -> Prop :=
  | c1 : R 0 0 0
  | c2 m n o (H : R m n o) : R (S m) n (S o)
  | c3 m n o (H : R m n o) : R m (S n) (S o)
  | c4 m n o (H : R (S m) (S n) (S (S o))) : R m n o
  | c5 m n o (H : R m n o) : R n m o.

  Definition fR : nat -> nat -> nat := plus.

  Theorem R_equiv_FR : forall m n o, R m n o <-> fR m n = o.
  Proof.
    intros m n o. split.
    - intro H. induction H.
      + reflexivity.
      + simpl. rewrite IHR. reflexivity.
      + unfold fR. rewrite plus_comm. simpl.
        rewrite plus_comm. unfold fR in IHR. rewrite IHR.
        reflexivity.
      + unfold fR in *. simpl in IHR.  rewrite plus_comm in IHR.
        simpl in IHR. rewrite plus_comm in IHR. injection IHR as IHR.
        apply IHR.
      + unfold fR. rewrite plus_comm. apply IHR.
    - generalize dependent o.
      induction m as [| m' IHm'].
      + intros o H. simpl in H. rewrite H.
        generalize dependent n.
        induction o as [| o' IHo'].
        * intros n H. apply c1.
        * intros n H. apply c3. induction n as [| n' IHn'].
          discriminate H. inversion H. apply IHo' in H1.
          apply H1.
      + intros o H. simpl in H. rewrite <- H. apply c2.
        induction o as [| o' IHo'].
        * discriminate H.
        * inversion H. rewrite H1. apply IHm'. apply H1.
  Qed.

End R.

Inductive subseq : list nat -> list nat -> Prop :=
| subseq_empty: forall l : list nat, subseq [] l
| subseq_cons : forall (n : nat) (l1 l2 : list nat),
    subseq l1 l2 -> subseq (n :: l1) (n :: l2)
| subseq_cons1: forall (n : nat) (l1 l2 : list nat),
    subseq l1 l2 -> subseq l1 (n :: l2).

Theorem subseq_refl : forall l : list nat, subseq l l.
Proof.
  intro l. induction l as [| h t IHt].
  - apply subseq_empty.
  - apply (subseq_cons h t t). apply IHt.
Qed.

Theorem subseq_app : forall l1 l2 l3 : list nat,
    subseq l1 l2 -> subseq l1 (l2 ++ l3).
Proof.
  intros l1 l2 l3 H. induction H.
  - apply subseq_empty.
  - simpl. apply subseq_cons. apply IHsubseq.
  - simpl. apply subseq_cons1. apply IHsubseq.
Qed.

Lemma subseq_contain : forall (n : nat) (l1 l2 : list nat),
    subseq (n :: l1) l2 -> subseq l1 l2.
Proof.
  intros. generalize dependent l1. induction l2.
  - intros. inversion H.
  - intros. inversion H.
    + apply subseq_cons1. apply H1.
    + apply IHl2 in H2. apply subseq_cons1. apply H2.
Qed.

Lemma subseq_contain1 : forall (n : nat) (l1 l2 : list nat),
    subseq (n :: l1) (n :: l2) -> subseq l1 l2.
Proof.
  intros. inversion H.
  - apply H1.
  - apply (subseq_contain n). apply H2.
Qed.

Theorem subseq_trans : forall l1 l2 l3 : list nat,
    subseq l1 l2 -> subseq l2 l3 -> subseq l1 l3.
Proof.
  intros l1 l2 l3. generalize dependent l2.
  generalize dependent l1. induction l3 as [| h3 t3 IHt3].
  - intros. inversion H0. subst. apply H.
  - intros. inversion H0.
    + subst. inversion H. apply subseq_empty.
    + subst. inversion H.
      * apply subseq_empty.
      * apply subseq_cons. apply (IHt3 l2 l0); assumption.
      * apply subseq_cons1. apply (IHt3 l1 l0); assumption.
    + apply subseq_cons1. apply (IHt3 l1 l2); assumption.
Qed.

Inductive reg_exp {T : Type} : Type :=
| EmptySet
| EmptyStr
| Char (t : T)
| App (r1 r2 : reg_exp)
| Union (r1 r2 : reg_exp)
| Star (r : reg_exp).

Inductive exp_match {T} : list T -> reg_exp -> Prop :=
| MEmpty : exp_match [] EmptyStr
| MChar x : exp_match [x] (Char x)
| MApp s1 re1 s2 re2 (H1 : exp_match s1 re1) (H2 : exp_match s2 re2) :
    exp_match (s1 ++ s2) (App re1 re2)
| MUnionL s1 re1 re2 (H1 : exp_match s1 re1) :
    exp_match s1 (Union re1 re2)
| MUnionR re1 s2 re2 (H2 : exp_match s2 re2) :
    exp_match s2 (Union re1 re2)
| MStar0 re : exp_match [] (Star re)
| MStarApp s1 s2 re (H1 : exp_match s1 re) (H2 : exp_match s2 (Star re)) :
    exp_match (s1 ++ s2) (Star re).

Notation "s =~ re" := (exp_match s re) (at level 80).

Example reg_exp_ex1 : [1] =~ Char 1.
Proof. apply MChar. Qed.

Example reg_exp_ex2 : [1; 2] =~ App (Char 1) (Char 2).
Proof. eapply (MApp [1] _  [2]); apply MChar. Qed.

Example reg_exp_ex3 : ~([1; 2] =~ Char 1).
Proof. intro H. inversion H. Qed.

Fixpoint reg_exp_of_list {T} (l : list T) :=
  match l with
  | [] => EmptyStr
  | x :: l' => App (Char x) (reg_exp_of_list l')
  end.

Example reg_exp_ex4 : [1; 2; 3] =~ reg_exp_of_list [1; 2; 3].
Proof.
  simpl. eapply (MApp [1] _ ([2] ++ ([3] ++ []))).
  - apply MChar.
  - apply MApp.
    + apply MChar.
    + apply MApp.
      * apply MChar.
      * apply MEmpty.
Qed.

Lemma MStar1 : forall T s (re : @reg_exp T),
    s =~ re -> s =~ Star re.
Proof.
  intros. rewrite <- (app_nil_r T s).
  apply MStarApp; [assumption | apply MStar0].
Qed.

Lemma empty_is_empty : forall T (s : list T),
    ~(s =~ EmptySet).
Proof. intros T s H. inversion H. Qed.

Lemma MUnion' : forall T (s : list T) (re1 re2 : @reg_exp T),
    s =~ re1 \/ s =~ re2 ->
    s =~ Union re1 re2.
Proof.
  intros T s re1 re2 [H1 | H2].
  - apply MUnionL. assumption.
  - apply MUnionR. assumption.
Qed.

Lemma MStar' : forall T (ss : list (list T)) (re : reg_exp),
    (forall s, In s ss -> s =~ re) ->
    fold app ss [] =~ Star re.
Proof.
  intros. induction ss as [| hss tss IH].
  - simpl. apply MStar0.
  - simpl. apply MStarApp.
    + apply H. simpl. left. reflexivity.
    + apply IH. intros. apply H. simpl. right. apply H0.
Qed.

Fixpoint re_chars {T} (re : reg_exp) : list T :=
  match re with
  | EmptySet => []
  | EmptyStr => []
  | Char x => [x]
  | App re1 re2 => re_chars re1 ++ re_chars re2
  | Union re1 re2 => re_chars re1 ++ re_chars re2
  | Star re => re_chars re
  end.

Theorem in_re_match : forall T (s : list T) (re : reg_exp) (x : T),
    s =~ re -> In x s -> In x (re_chars re).
Proof.
  intros T s re x Hmatch Hin.
  induction Hmatch as
      [| x'
       | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
       | s1 re1 re2 Hmatch IH
       | re1 s2 re2 Hmatch IH
       | re
       | s1 s2 re Hmatch1 IH1 Hmatch2 IH2].
  - inversion Hin.
  - simpl in Hin. destruct Hin.
    + rewrite H. simpl. left. reflexivity.
    + inversion H.
  - simpl. Search In. rewrite In_app_iff.
    rewrite In_app_iff in Hin. destruct Hin.
    + left. apply IH1. apply H.
    + right. apply IH2. apply H.
  - simpl. rewrite In_app_iff. left.
    apply IH. apply Hin.
  - simpl. rewrite In_app_iff. right.
    apply IH. apply Hin.
  - inversion Hin.
  - rewrite In_app_iff in Hin. destruct Hin.
    + simpl. apply IH1. apply H.
    + apply IH2. apply H.
Qed.

Fixpoint re_not_empty {T : Type} (re : @reg_exp T) : bool :=
  match re with
  | EmptySet => false
  | EmptyStr => true
  | Char x => true
  | App re1 re2 => andb (re_not_empty re1)  (re_not_empty re2)
  | Union re1 re2 => orb (re_not_empty re1)  (re_not_empty re2)
  | Star re => true
  end.

Lemma re_not_empty_correct : forall T (re : @reg_exp T),
    (exists s, s =~ re) <-> re_not_empty re = true.
Proof.
  intros T re. split.
  - intros H. inversion H. induction H0.
    + inversion H. reflexivity.
    + reflexivity.
    + simpl. rewrite Logic.andb_true_iff. split.
      * apply IHexp_match1. exists s1. apply H0_.
      * apply IHexp_match2. exists s2. apply H0_0.
    + simpl. rewrite orb_true_iff. left. apply IHexp_match.
      exists s1. apply H0.
    + simpl. rewrite orb_true_iff. right. apply IHexp_match.
      exists s2. apply H0.
    + simpl. reflexivity.
    + simpl. reflexivity.
  - intro H. induction re.
    + inversion H.
    + exists []. constructor.
    + exists [t]. constructor.
    + simpl in H. Search orb. rewrite andb_true_iff in H.
      destruct H. apply IHre1 in H. destruct H.
      apply IHre2 in H0. destruct H0.
      exists (x++x0). constructor; assumption.
    + simpl in H. rewrite orb_true_iff in H.
      destruct H.
      * apply IHre1 in H. destruct H. exists x.
        apply MUnionL. assumption.
      * apply IHre2 in H. destruct H. exists x.
        apply MUnionR. assumption.
    + exists []. constructor.
Qed.

Lemma star_app' : forall T (s1 s2 : list T) (re re' : reg_exp),
    re' = Star re ->
    s1 =~ re' ->
    s2 =~ Star re ->
    s1 ++ s2 =~ Star re.
Proof.
  intros T s1 s2 re re' H1 H2 H3.
  generalize dependent s2.
  induction H2.
  - intros s2 H3. simpl. apply H3.
  - discriminate H1.
  - discriminate H1.
  - discriminate H1.
  - discriminate H1.
  - intros s2 H3. simpl. apply H3.
  - intros s0 H3. Search list. rewrite <- app_assoc.
    constructor. inversion H1. subst. apply H2_.
    apply IHexp_match2.
    * apply H1.
    * apply H3.
Qed.

Lemma star_app : forall T (s1 s2 : list T) (re : reg_exp),
    s1 =~ Star re ->
    s2 =~ Star re ->
    s1 ++ s2 =~ Star re.
Proof.
  intros T s1 s2 re H1.
  remember (Star re) as re'.
  generalize dependent s2.
  induction H1.
  - discriminate Heqre'.
  - discriminate Heqre'.
  - discriminate Heqre'.
  - discriminate Heqre'.
  - discriminate Heqre'.
  - intros s2 H. simpl. apply H.
  - intros s0 H. rewrite <- app_assoc.
    constructor. inversion Heqre'. subst. apply H1_.
    apply IHexp_match2.
    * apply Heqre'.
    * apply H.
Qed.

Lemma MStar'' : forall T (s : list T) (re : reg_exp),
    s =~ Star re ->
    exists ss : list (list T),
      s = fold app ss []
      /\ forall s', In s' ss -> s' =~ re.
Proof.
  intros T s re. remember (Star re) as re'.
  intro H. induction H.
  - inversion Heqre'.
  - inversion Heqre'.
  - inversion Heqre'.
  - inversion Heqre'.
  - inversion Heqre'.
  - exists []. simpl. split.
    + reflexivity.
    + intros s' H. contradiction.
  - inversion Heqre'. apply IHexp_match2 in Heqre'. destruct Heqre'.
    destruct H1.
    exists (s1::x). split.
    + simpl. rewrite <- H1. reflexivity.
    + intros. inversion H4.
      * subst. apply H.
      * subst. apply H3. apply H5.
Qed.

Module Pumping.

  Fixpoint pumping_constant {T} (re : @reg_exp T) : nat :=
    match re with
    | EmptySet => 0
    | EmptyStr => 1
    | Char _ => 2
    | App re1 re2 | Union re1 re2 =>
      pumping_constant re1 + pumping_constant re2
    | Star _ => 1
    end.

  Fixpoint napp {T} (n : nat) (l : list T) : list T :=
    match n with
    | O => []
    | S n' => l ++ napp n' l
    end.

  Lemma napp_plus: forall T (n m : nat) (l : list T),
      napp (n + m) l = napp n l ++ napp m l.
  Proof.
    intros T n m l. induction n as [| n' IH].
    - simpl. reflexivity.
    - simpl. rewrite IH. rewrite app_assoc. reflexivity.
  Qed.

  Lemma pumping : forall T (re : @reg_exp T) s,
      s =~ re ->
      pumping_constant re <= length s ->
      exists s1 s2 s3,
        s = s1 ++ s2 ++ s3 /\
        s2 <> [] /\
        forall m, s1 ++ napp m s2 ++ s3 =~ re.
  Proof.
    Import Coq.omega.Omega.
    intros T re s H1. induction H1.
    - simpl. omega. 
    - simpl. omega.
    - simpl. Search length. rewrite app_length.
      intro H2.
      apply (Nat.add_le_cases (pumping_constant re1)
                              (pumping_constant re2)
                              (length s1)
                              (length s2)
            ) in H2.
      destruct H2.
      + apply IHexp_match1 in H. destruct H. destruct H. destruct H.
        destruct H. destruct H0.
        exists x, x0, (x1++s2).
        split.
        * rewrite H. rewrite app_assoc. rewrite app_assoc.
          rewrite app_assoc. reflexivity.
        * split.
          { apply H0. }
          { intro m. rewrite app_assoc. rewrite app_assoc.
            constructor. rewrite <- app_assoc. apply H1.
            apply H1_0. }
      + apply IHexp_match2 in H. destruct H. destruct H. destruct H.
        destruct H. destruct H0.
        exists (s1++x), x0, x1.
        split.
        * rewrite <- app_assoc. rewrite H. reflexivity.
        * split.
          { apply H0. }
          { intro m. rewrite <- app_assoc. constructor.
            apply H1_. apply H1. }
    - simpl. intro H2.
      assert (H : pumping_constant re1 <= length s1). { omega. }
      apply IHexp_match in H. destruct H. destruct H. destruct H. 
      destruct H. destruct H0.
      exists x, x0, x1. split.
      + apply H.
      + split.
        * apply H0.
        * intro m. apply MUnionL. apply H3.
    - simpl. intro H2.
      assert (H : pumping_constant re2 <= length s2). { omega. }
      apply IHexp_match in H. destruct H. destruct H. destruct H. 
      destruct H. destruct H0.
      exists x, x0, x1. split.
      + apply H.
      + split.
        * apply H0.
        * intro m. apply MUnionR. apply H3.
    - simpl. omega.
    - simpl in *. destruct s1 as [| s1'] eqn:E.
      + simpl. apply IHexp_match2.
      + destruct s2 as [| s2'] eqn:E1.
        * intro H. exists [], (s1'::l), [].
          simpl. split.
          { reflexivity. }
          { split.
            unfold not. intro H'. inversion H'.
            intro m. induction m as [| m' IH].
            simpl. constructor.
            simpl. rewrite app_nil_r.
            assert (H' : s1' :: l ++ napp m' (s1' :: l) = ( (s1' :: l) ++ napp m' (s1' :: l))).
            { simpl. reflexivity. }
            rewrite H'. constructor.
            apply H1_.
            rewrite app_nil_r in IH. apply IH. }
        * simpl in *. intro H.
          assert (H' : 1 <= S (length l0)). { omega. }
          apply IHexp_match2 in H'.
          destruct H'. destruct H0. destruct H0. destruct H0.
          destruct H1.
          exists ((s1' :: l) ++ x), x0, x1.
          split.
          { simpl. rewrite <- app_assoc. rewrite H0. reflexivity. }
          { split. apply H1. intro m. rewrite <- app_assoc.
            constructor. apply H1_. apply H2. }
  Qed.
End Pumping.

Theorem filter_not_empty_In : forall n l,
    filter (fun x => n =? x) l <> [] ->
    In n l.
Proof.
  intros n l H. induction l as [| h t IH].
  - simpl in H. unfold not in H. exfalso.
    apply H. reflexivity.
  - simpl in *. destruct (n =? h) eqn:E.
    + left. rewrite <- eqb_eq. apply E.
    + right. apply IH. apply H.
Qed.

Inductive reflect (P : Prop) : bool -> Prop :=
| ReflectT (H : P) : reflect P true
| ReflectF (H : ~P) : reflect P false.

Theorem iff_reflect : forall P b,
    (P <-> b = true) -> reflect P b.
Proof.
  intros P b H. destruct b eqn:E.
  - apply ReflectT. rewrite H. reflexivity.
  - apply ReflectF. rewrite H. intro H1. inversion H1.
Qed.

Theorem reflect_iff : forall P b,
    reflect P b -> (P <-> b = true).
Proof.
  intros P b H. split.
  - intro H1. inversion H.
    + reflexivity.
    + contradiction.
  - intro H1. rewrite H1 in H. inversion H. apply H0.
Qed.

Lemma eqbP : forall n m, reflect (n = m) (n =? m).
Proof.
  intros n m. apply iff_reflect.
  rewrite eqb_eq. reflexivity.
Qed.

Theorem filter_not_empty_In' : forall n l,
    filter (fun x => n =? x) l <> [] ->
    In n l.
Proof.
  intros n l. induction l as [| m l' IHl'].
  - simpl. intros H. apply H. reflexivity.
  - simpl. destruct (eqbP n m) as [H | H].
    + intro H1. left. apply H.
    + intro H1. right. apply IHl'. apply H1.
Qed.

Fixpoint count n l :=
  match l with
  | [] => 0
  | m :: l' => (if n =? m then 1 else 0) + count n l'
  end.

Theorem eqbP_practice : forall n l,
    count n l = 0 -> ~(In n l).
Proof.
  intros. induction l as [| h t IH].
  - simpl. intro H1. apply H1.
  - simpl. destruct (eqbP n h) as [H1 | H1].
    + simpl in H. rewrite <- eqb_eq in H1. rewrite H1 in H.
      discriminate H.
    + simpl in H. intros [H2 | H2].
      * contradiction.
      * rewrite <- eqb_neq in H1. rewrite H1 in H.
        simpl in H. apply IH in H. contradiction. 
Qed.

Inductive nostutter {X : Type} : list X -> Prop :=
| NostutterNil (l : list X) (H : l = [] ) : nostutter l
| NostutterSingle (a : X): nostutter [a]
| NostutterMulti (a b : X) (l : list X) (H1: a <> b)
  (H2: nostutter (b :: l)) : nostutter (a :: b :: l).

Example test_nostutter_1 : nostutter [3; 1; 4; 1; 5; 6].
Proof. repeat constructor; apply eqb_neq; auto.  Qed.

Example test_nostutter_2 : nostutter (@nil nat).
Proof. constructor. reflexivity. Qed.

Example test_nostutter_3 : nostutter [5].
Proof. apply NostutterSingle. Qed.

Example test_nostutter_4 : not (nostutter [3; 1; 1; 4]).
Proof.
  intro. inversion H. 
  - inversion H0.
  - inversion H4. inversion H5. unfold not in H7.
    apply H7. reflexivity.
Qed.

Inductive in_order_merge {X : Type}: list X -> list X -> list X -> Prop :=
| in_order_merge_case (test : X -> bool) (l1 l2 l3 : list X)
                      (H1 : filter test l1 = l1)
                      (H2 : filter test l2 = [])
                      (H3 : filter test l3 = l1)
                      (H4 : filter (fun x => negb (test x)) l3 = l2) :
    in_order_merge l1 l2 l3.

Example test_in_order_merge :
  in_order_merge [1; 6; 2] [4; 3] [1; 4; 6; 2; 3].
Proof.
  apply (in_order_merge_case (fun x => (x <=? 2) || (5 <=? x)));
    reflexivity.
Qed.

Theorem length_prop_filter : forall (test : nat -> bool) (l l1 : list nat),
    subseq l1 l ->
    length (filter test l1) <= length (filter test l).
Proof.
  intros test l l1 H. induction H.
  - simpl. apply le_0_n.
  - simpl. destruct (test n) eqn:E.
    + simpl. apply le_n_S. apply IHsubseq.
    + apply IHsubseq.
  - simpl. destruct (test n) eqn:E.
    + simpl. apply le_S. apply IHsubseq.
    + apply IHsubseq.
Qed.

Inductive pal {X : Type} : list X -> Prop :=
| PalEmpty : pal []
| PalSingle (a : X) : pal [a]
| PalApp (a : X) (l : list X) (H : pal l) : pal (a :: l ++ [a]).

Theorem pal_app_rev : forall (X : Type) (l : list X),
    pal (l ++ rev l).
Proof.
  intros X l. induction l as [| h t IH].
  - simpl. apply PalEmpty.
  - simpl. rewrite app_assoc. apply PalApp. apply IH.
Qed.

Theorem pal_rev : forall (X : Type) (l : list X),
    pal l -> l = rev l.
Proof.
  intros X l H. induction H.
  - reflexivity.
  - reflexivity.
  - simpl. Search rev. rewrite rev_app_distr. simpl.
    rewrite <- IHpal. reflexivity.
Qed.

Lemma rev_eq_pal_length: forall (X: Type) (n: nat) (l: list X),
    length l <= n -> l = rev l -> pal l.
Proof.
  induction n as [| n' IH].
  - intros. destruct l as [| h t] eqn:E.
    + constructor.
    + simpl in H. inversion H.
  - induction n' as [| n'' IH'].
    + intros. destruct l as [| h t] eqn:E.
      * constructor.
      * simpl in H. destruct t as [| h' t'] eqn:E'.
        { constructor. }
        { simpl in H. inversion H. inversion H2. }
    + intros. destruct l as [| h t] eqn:E.
      * constructor.
      * simpl in H. destruct t as [| h' t'] eqn:E'.
        { constructor. }
        { simpl in H0. assert (eq: exists l', t = l'++[h]).
          { destruct (rev t') as [| h'' t''] eqn:E''.
            simpl in H0. exists []. destruct t' as [| h3 t3] eqn:E3.
            inversion H0. rewrite E'. reflexivity.
            simpl in E''.
            destruct (rev t3) as [| h4 t4] eqn:E4.
            simpl in E''. inversion E''.
            simpl in E''. inversion E''.
            exists (t''++[h']). simpl in H0. inversion H0.
            rewrite E'. reflexivity.
          }
          destruct eq. rewrite <- E'. rewrite H1. constructor.
          rewrite <- E' in H. rewrite H1 in H.
          Search length. rewrite app_length in H.
          simpl in H. Search plus. rewrite plus_comm in H.
          simpl in H. apply le_S_n in H. Search le.
          apply Le.le_Sn_le in H. apply IH.
          apply H.
          subst. assert (eq: rev t' ++ [h'] = rev(h' :: t')).
          { simpl. reflexivity. }
          rewrite eq in H0. rewrite H1 in H0.
          simpl in H0. Search rev. rewrite rev_app_distr in H0.
          simpl in H0. inversion H0. assert (H4: rev (x ++ [h]) = rev(rev x ++ [h])).
          { rewrite H3. reflexivity. }
          rewrite rev_app_distr in H4. simpl in H4.
          rewrite rev_app_distr in H4. simpl in H4.
          inversion H4. Search rev. rewrite rev_involutive in H5. symmetry. apply H5.
        }
Qed.

Theorem rev_eq_list_is_pal : forall (X : Type) (l : list X),
    l = rev l -> pal l.
Proof.
  intros X l.
  apply (rev_eq_pal_length X (length l) l).
  auto.
Qed.

Definition disjoint {X : Type} (l1 : list X) (l2 : list X) : Prop :=
  forall x, ~(In x l1 /\ In x l2).

Inductive NoDup (X : Type): (list X) -> Prop :=
| NoDupEmpty : NoDup X []
| NoDupCons (x : X) (l : list X) (H : NoDup X l) :
    ~ (In x l) -> NoDup X (x :: l).

Example test_disjoint1: disjoint [1; 2; 3] [4; 5; 6].
Proof.
  unfold disjoint. unfold not. intros.
  destruct x as [| x1] eqn:E1.
  - destruct H. inversion H. inversion H1. inversion H1. inversion H2.
    inversion H2. inversion H3. inversion H3.
  - destruct H. inversion H. inversion H1. rewrite H3 in H0.
    inversion H0. inversion H2. inversion H2. inversion H4. inversion H4.
    inversion H5. inversion H5. inversion H1. rewrite H2 in H0. inversion H0.
    inversion H3. inversion H3. inversion H4. inversion H4. inversion H5.
    inversion H5. inversion H2. rewrite H3 in H0. inversion H0. inversion H4.
    inversion H4. inversion H5. inversion H5. inversion H6. inversion H6.
    inversion H3.
Qed.

Example test_NoDup: NoDup nat [1;2;3].
Proof.
  constructor. constructor. constructor.
  constructor. unfold not. intro H. inversion H.
  unfold not. intro H. inversion H. inversion H0. inversion H0.
  unfold not. intro H. inversion H. inversion H0. inversion H0.
  inversion H1. inversion H1.
Qed.

Lemma in_split : forall (X : Type) (x : X) (l : list X),
    In x l ->
    exists l1 l2, l = l1 ++ x :: l2.
Proof.
  intros. induction l as [| h t IH].
  - inversion H.
  - inversion H.
    + exists [], t. simpl.
      rewrite H0. reflexivity.
    + apply IH in H0. destruct H0.
      destruct H0.
      exists (h::x0), x1. rewrite H0.
      simpl. reflexivity.
Qed.

Inductive repeats {X:Type} : list X -> Prop :=
| RepeatsTwo (x : X): repeats [x; x]
| RepeatsMore (x : X) (l : list X) (H : repeats l) : repeats (x :: l)
| RepeatsIn (x : X) (l : list X) (H : In x l) : repeats (x :: l).

Theorem pigeonhole_principle: forall (X : Type) (l1 l2 : list X),
    excluded_middle ->
    (forall x, In x l1 -> In x l2) ->
    length l2 < length l1 ->
    repeats l1.
Proof.
  intros X l1. induction l1 as [| x l1' IHl1'].
  - intros l2 em H H1. simpl in H1. inversion H1.
  - intros l2 em H H1. unfold excluded_middle in em.
    assert(em': In x l1' \/ ~ In x l1'). apply em.
    destruct em'.
    + apply RepeatsIn. apply H0.
    + apply RepeatsMore.
      assert (eq_lst: exists l1 l3, l2 = l1 ++ [x] ++ l3).
      { apply (in_split X x l2). apply H. simpl. left.
        reflexivity. }
      destruct eq_lst. destruct H2.
      apply (IHl1' (x0++x1)).
      * unfold excluded_middle. apply em.
      * intros. assert (eq_in: In x2 (x :: l1')).
        { simpl. right. apply H3. }
        apply (H x2) in eq_in.
        assert (eq_em: x = x2 \/ ~ x = x2).
        { apply em. }
        destruct eq_em.
        { rewrite H4 in H0. contradiction. }
        { rewrite H2 in eq_in. rewrite In_app_iff in eq_in.
          rewrite In_app_iff in eq_in. simpl in eq_in.
          rewrite In_app_iff. destruct eq_in.
          left. apply H5.
          destruct H5. destruct H5. rewrite H5 in H3.
          contradiction. contradiction. right. apply H5. }
      * rewrite H2 in H1. rewrite app_length in H1.
        simpl in H1. rewrite <- plus_comm in H1. simpl in H1.
        rewrite plus_comm in H1. unfold lt in H1. unfold lt.
        Search le. apply le_S_n. rewrite app_length.
        apply H1.
Qed.

Require Export Coq.Strings.Ascii.

Definition string := list ascii.

Lemma provable_equiv_true : forall (P : Prop), P -> (P <-> True).
Proof.
  intros. split.
  - intro H1. apply I.
  - intro t. apply H.
Qed.

Lemma not_equiv_false : forall (P : Prop), ~P -> (P <-> False).
Proof.
  unfold not. intros. split.
  - apply H.
  - intro f. exfalso. apply f.
Qed.

Lemma null_matches_none : forall (s : string),
    (s =~ EmptySet) <-> False.
Proof.
  intros. split.
  - intro H. inversion H.
  - intro F. exfalso. apply F.
Qed.

Lemma empty_matches_eps : forall (s : string),
    s =~ EmptyStr <-> s = [].
Proof.
  intro s. split.
  - intro H. inversion H. reflexivity.
  - intro H. rewrite H. constructor.
Qed.

Lemma empty_nomatch_ne : forall (a : ascii) s,
    (a :: s =~ EmptyStr) <-> False.
Proof.
  intros a s. split.
  - intro H. inversion H.
  - intro F. contradiction.
Qed.

Lemma char_nomatch_char : forall (a b : ascii) s,
    b <> a -> (b :: s =~ Char a <-> False).
Proof.
  unfold not. intros a b s H. split.
  - intro H1. inversion H1. apply H. apply H4.
  - intro F. exfalso. apply F.
Qed.

Lemma char_eps_suffix : forall (a : ascii) s,
    a :: s =~ Char a <-> s = [].
Proof.
  intros a s. split.
  - intro H. inversion H. reflexivity.
  - intro H. rewrite H. constructor.
Qed.

Lemma app_exists : forall (s : string) re0 re1,
    s =~ App re0 re1 <->
    exists s0 s1, s = s0 ++ s1 /\ s0 =~ re0 /\ s1 =~ re1.
Proof.
  intros s re0 re1. split.
  - intro H. inversion H. exists s1, s2. split.
    + reflexivity.
    + split; assumption.
  - intros [s0 [s1 [H1 [H2 H3]]]]. rewrite H1.
    constructor; assumption.
Qed.

Lemma app_ne : forall (a : ascii) s re0 re1,
    a :: s =~ (App re0 re1) <->
    ([] =~ re0 /\ a :: s =~ re1) \/
    exists s0 s1, s = s0 ++ s1 /\ a :: s0 =~ re0 /\ s1 =~ re1.
Proof.
  intros a s re0 re1. split.
  - intro H. inversion H. destruct s1 as [| a' s1'] eqn:E.
    + left. split.
      * apply H3.
      * simpl. apply H4.
    + right. inversion H1. exists s1', s2.
      split.
      * reflexivity.
      * subst. split; assumption.
  - intros [[H0 H1] | [s0 [s1 [H0 [H1 H2]]]]].
    + apply (MApp [] _ (a::s) _); assumption.
    + rewrite H0. apply (MApp (a::s0) _ s1 _); assumption.
Qed.

Lemma union_disj : forall (s : string) re0 re1,
    s =~ Union re0 re1 <-> s =~ re0 \/ s =~ re1.
Proof.
  intros s re0 re1. split.
  - intro H. inversion H.
    + left. subst. apply H2.
    + right. subst. apply H1.
  - intros [H | H]; constructor; assumption.
Qed.

Lemma star_ne : forall (a : ascii) s re,
    a :: s =~ Star re <->
    exists s0 s1, s = s0 ++ s1 /\ a :: s0 =~ re /\ s1 =~ Star re.
Proof.
  intros a s re. split.
  - remember (Star re) as re'.
    remember (a :: s) as s'. (* This is the key step *)
    intro H. induction H.
    + inversion Heqs'.
    + inversion Heqre'.
    + inversion Heqre'.
    + inversion Heqre'.
    + inversion Heqre'.
    + inversion Heqs'.
    + intros. destruct s1.
      * simpl in Heqs'.
        apply IHexp_match2. apply Heqre'. apply Heqs'.
      * exists s1, s2. inversion Heqre'. subst.
        inversion Heqs'. split.
        { reflexivity. }
        { split. subst. apply H. apply H0. }
  - intros [s0 [s1 [H1 [H2 H3]]]].
    rewrite H1. eapply (MStarApp (a :: s0) s1); assumption.
Qed.

Definition refl_matches_eps m :=
  forall re : @reg_exp ascii, reflect ([] =~ re) (m re).

Fixpoint match_eps (re : @reg_exp ascii) : bool :=
  match re with
  | EmptySet => false
  | EmptyStr => true
  | Char _ => false
  | App r1 r2 => match_eps r1 && match_eps r2
  | Union r1 r2 => match_eps r1 || match_eps r2
  | Star r => true
  end.

Lemma match_eps_refl : refl_matches_eps match_eps.
Proof.
  intros re. induction re; simpl.
  - constructor. intro H. inversion H.
  - constructor. constructor.
  - constructor. intro H. inversion H.
  - inversion IHre1. inversion IHre2.
    + simpl. apply ReflectT. eapply (MApp [] _ []); assumption. 
    + simpl. apply ReflectF. intro H3.
      inversion H3. subst. destruct s1 as [| h1 t1].
      * destruct s2 as [| h2 t2].
        contradiction.
        simpl in H4. inversion H4.
      * simpl in H4. inversion H4.
    + simpl. constructor. intro H1. inversion H1.
      subst. destruct s1 as [| h1 t1].
      * destruct s2 as [| h2 t2].
        contradiction.
        simpl in H2. inversion H2.
      * simpl in H2. inversion H2.
  - inversion IHre1.
    + inversion IHre2.
      * simpl. apply ReflectT. apply MUnionL. assumption.
      * simpl. apply ReflectT. apply MUnionL. assumption.
    + inversion IHre2.
      * simpl. apply ReflectT. apply MUnionR. assumption.
      * simpl. apply ReflectF. intro H3. inversion H3; contradiction.
  - apply ReflectT. apply MStar0.
Qed.

Definition is_der re (a : ascii) re' :=
  forall s, a :: s =~ re <-> s =~ re'.

Definition derives d := forall a re, is_der re a (d a re).

Fixpoint derive (a : ascii) (re : @reg_exp ascii) : @reg_exp ascii :=
  match re with
  | EmptySet => EmptySet
  | EmptyStr => EmptySet
  | Char c => if eqb a c then EmptyStr else EmptySet
  | App EmptySet r2 => EmptySet
  | App EmptyStr r2 => derive a r2
  | App (Char c) r2 => if eqb a c then r2 else EmptySet
  | App r1 r2 =>
    if match_eps r1 then Union (derive a r2) (App (derive a r1) r2)
    else App (derive a r1) r2
  | Union r1 r2 => Union (derive a r1) (derive a r2)
  | Star (EmptySet) => EmptySet
  | Star (EmptyStr) => EmptySet
  | Star r => App (derive a r) re
  end.

Example c := ascii_of_nat 99.
Example d := ascii_of_nat 100.

(* "c" =~ EmptySet *)
Example test_der0 : match_eps (derive c (EmptySet)) = false.
Proof. reflexivity. Qed.

(* "c" =~ Char c *)
Example test_der1 : match_eps (derive c (Char c)) = true.
Proof. reflexivity. Qed.

(* "c" =~ Cahr d *)
Example test_der2 : match_eps (derive c (Char d)) = false.
Proof. reflexivity. Qed.

(* "c" =~ App (Char c) EmptyStr *)
Example test_der3 : match_eps (derive c (App (Char c) EmptyStr)) = true.
Proof. reflexivity. Qed.

(* "c" =~ App EmptyStr (Char c) *)
Example test_der4 : match_eps (derive c (App EmptyStr (Char c))) = true.
Proof. reflexivity. Qed.

(* "c" =~ Star c *)
Example test_der5 : match_eps (derive c (Star (Char c))) = true.
Proof. reflexivity. Qed.

(* "cd" =~ App (Char c) (Char d) *)
Example test_der6 :
  match_eps (derive d (derive c (App (Char c) (Char d)))) = true.
Proof. reflexivity. Qed.

(* "cd" =~ App (Char d) (Char c) *)
Example test_der7 :
  match_eps (derive d (derive c (App (Char d) (Char c)))) = false.
Proof. reflexivity. Qed.

Lemma derive_corr : derives derive.
Proof.
  unfold derives. intros a re.
  generalize dependent a.
  intro a.
  unfold is_der.
  induction re.
  - simpl. intro s. split.
    + intro H. inversion H.
    + intro H. inversion H.
  - simpl. intro s. split.
    + intro H. inversion H.
    + intro H. inversion H.
  - simpl. intro s. split.
    + intro H. inversion H. subst. destruct (t =? t)%char eqn:E.
      * apply MEmpty.
      * rewrite eqb_refl in E. discriminate E.
    + intro H. destruct (a =? t)%char eqn:E.
      * rewrite eqb_eq in E. rewrite E. inversion H. apply MChar.
      * inversion H.
  - simpl. intro s. split.
    + intro H. destruct re1 eqn:E.
      * inversion H. inversion H3.
      * inversion H. inversion H3. rewrite <- H5 in H1.
        simpl in *. rewrite H1 in H4. apply IHre2. assumption.
      * simpl. destruct (a =? t)%char eqn:E1.
        { rewrite eqb_eq in E1. rewrite <- E1 in H.
          inversion H. inversion H3. subst.
          assert (eq: s = [] ++ s).
          { reflexivity. }
          rewrite eq. simpl in H1. inversion H1. subst. apply H4. }
        { rewrite eqb_neq in E1. inversion H. inversion H3. subst.
          inversion H1. rewrite H2 in E1. contradiction. }
      * destruct (match_eps (App r1 r2)) eqn:E1.
        assert (H' : reflect ([] =~ (App r1 r2)) (match_eps (App r1 r2))).
        { apply match_eps_refl. }
        rewrite E1 in H'. inversion H'.
        inversion H.
        destruct s1 as [| h s1'].
        simpl in H1. subst.
        apply MUnionL. apply IHre2. apply H5.
        simpl in H1. inversion H1.
        apply MUnionR. apply MApp. apply IHre1.
        subst. apply H4.
        apply H5.
        inversion H.
        destruct s1 as [| h s1'].
        assert(H' : reflect ([] =~ (App r1 r2)) (match_eps (App r1 r2))).
        { apply match_eps_refl. }
        rewrite E1 in H'. inversion H'.
        contradiction.
        simpl in H1. inversion H1.
        subst. apply IHre1 in H3.
        apply MApp; assumption.
      * destruct (match_eps (Union r1 r2)) eqn:E1.
        assert (H' : reflect ([] =~ (Union r1 r2)) (match_eps (Union r1 r2))).
        { apply match_eps_refl. }
        rewrite E1 in H'. inversion H'.
        inversion H.
        destruct s1 as [| h s1'].
        simpl in H1. subst. apply MUnionL. apply IHre2. apply H5.
        simpl in H1. inversion H1. apply MUnionR. apply MApp.
        apply IHre1. subst. apply H4. apply H5.
        inversion H.
        destruct s1 as [| h s1'].
        assert (H' : reflect ([] =~ (Union r1 r2)) (match_eps (Union r1 r2))).
        { apply match_eps_refl. }
        rewrite E1 in H'. inversion H'. contradiction.
        simpl in H1. inversion H1.
        subst. apply IHre1 in H3.
        apply MApp; assumption.
      * destruct (match_eps (Star r)) eqn:E1.
        assert (H' : reflect ([] =~ (Star r)) (match_eps (Star r))).
        { apply match_eps_refl. }
        rewrite E1 in H'. inversion H'.
        inversion H.
        destruct s1 as [| h s1'].
        simpl in H1. subst. apply MUnionL. apply IHre2. apply H5.
        simpl in H1. inversion H1. apply MUnionR. apply MApp.
        apply IHre1. subst. apply H4. apply H5.
        inversion H.
        destruct s1 as [| h s1'].
        assert (H' : reflect ([] =~ (Star r)) (match_eps (Star r))).
        { apply match_eps_refl. }
        rewrite E1 in H'. inversion H'. contradiction.
        simpl in H1. inversion H1.
        subst. apply IHre1 in H3.
        apply MApp; assumption.
    + intro H. destruct re1.
      * inversion H.
      * assert (H' : a :: s = [] ++ (a :: s)). { reflexivity. }
        rewrite H'. apply MApp.
        { constructor. }
        { apply IHre2. apply H. }
      * destruct (a =? t)%char eqn:E.
        rewrite eqb_eq in E. subst.
        assert (H' : t :: s = [t] ++ s). { reflexivity. }
        rewrite H'. apply MApp.
        { apply MChar. }
        { apply H. }
        inversion H.
      * destruct (match_eps (App re1_1 re1_2)) eqn:E.
        assert (H' : reflect ([] =~ (App re1_1 re1_2)) (match_eps (App re1_1 re1_2))).
        { apply match_eps_refl. }
        rewrite E in H'. inversion H'.
        inversion H.
        assert (Heq : a :: s = [] ++ (a :: s)). { reflexivity. }
        rewrite Heq. apply MApp.
        { assumption. }
        { apply IHre2. apply H3. }
        subst. destruct re1_1.
        { inversion H3. inversion H5. }
        { inversion H3. subst.
          assert (Heq : a :: s1 ++ s2 = (a :: s1) ++ s2).
          { reflexivity. }
          rewrite Heq. apply MApp.
          apply IHre1. simpl. apply H5.
          apply H6.
        }
        { destruct (a =? t)%char eqn:E1.
          rewrite eqb_eq in E1. rewrite E1. inversion H0.
          subst. inversion H5. subst. inversion H1.
          inversion H0. inversion H5. subst. inversion H1. }
        { inversion H. 
          assert (Heq : a :: s = [] ++ (a :: s)).
          { reflexivity. }
          rewrite Heq.
          apply MApp. apply H0. apply IHre2. apply H4.
          inversion H4.
          assert (Heq : a :: s1 ++ s0 = (a :: s1) ++ s0).
          { reflexivity. }
          rewrite Heq. apply MApp.
          apply IHre1. assumption. assumption. 
        }
        { inversion H.
          assert (Heq : a :: s = [] ++ (a :: s)).
          { reflexivity. }
          rewrite Heq.
          apply MApp. apply H0. apply IHre2. apply H4.
          inversion H4.
          assert (Heq : a :: s1 ++ s0 = (a :: s1) ++ s0).
          { reflexivity. }
          rewrite Heq. apply MApp.
          apply IHre1. assumption. assumption. 
        }
        { inversion H.
          assert (Heq : a :: s = [] ++ (a :: s)).
          { reflexivity. }
          rewrite Heq.
          apply MApp. apply H0. apply IHre2. apply H4.
          inversion H4.
          assert (Heq : a :: s1 ++ s0 = (a :: s1) ++ s0).
          { reflexivity. }
          rewrite Heq. apply MApp.
          apply IHre1. assumption. assumption.
        }
        { inversion H.
          assert (Heq : a :: s1 ++ s2 = (a :: s1) ++ s2).
          { reflexivity. }
          rewrite Heq.
          apply MApp. apply IHre1. assumption. assumption.
        }
      * destruct (match_eps (Union re1_1 re1_2)) eqn:E.
        assert (H' : reflect ([] =~ (Union re1_1 re1_2)) (match_eps (Union re1_1 re1_2))).
        { apply match_eps_refl. }
        rewrite E in H'. inversion H'.
        inversion H.
        assert (Heq : a :: s = [] ++ (a :: s)). { reflexivity. }
        rewrite Heq. apply MApp.
        { assumption. }
        { apply IHre2. apply H3. }
        { inversion H3.
          assert (Heq : a :: s1 ++ s0 = (a :: s1) ++ s0).
          { reflexivity. }
          rewrite Heq. apply MApp. apply IHre1. simpl.
          assumption. assumption. 
        }
        { inversion H.
          assert (Heq : a :: s1 ++ s2 = (a :: s1) ++ s2).
          { reflexivity. }
          rewrite Heq.
          apply MApp. apply IHre1. assumption. assumption.
        } 
      * destruct (match_eps (Star re1)) eqn:E.
        { inversion H.
          { assert (Heq : a :: s = [] ++ (a :: s)).
            { reflexivity. }
            rewrite Heq. apply MApp.
            constructor.
            apply IHre2. apply H2.
          }
          { destruct re1.
            inversion H1. inversion H7.
            inversion H1. inversion H7.
            inversion H1. 
            destruct (a =? t)%char eqn: E1.
            rewrite eqb_eq in E1. rewrite E1.
            inversion H1. rewrite E1 in *. Search eqb.
            rewrite eqb_refl in *. inversion H7.
            inversion H17. simpl.
            assert (Heq : t :: s6 ++ s0 = ([t] ++ s6) ++ s0).
            { reflexivity. }
            rewrite Heq. apply MApp.
            apply MStarApp. apply MChar. apply H18. apply H8.
            inversion H1. inversion H7. inversion H17.
            inversion H1.
            assert (Heq : a :: s1 ++ s0 = ([a] ++ s1) ++ s0).
            { reflexivity. }
            destruct re1_1.
            inversion H7. inversion H12.
            inversion H7.
            assert(Heq1 : a :: (s3 ++ s4) ++ s0 = (a :: (s3 ++ s4)) ++ s0).
            { reflexivity. }
            rewrite Heq1. apply MApp.
            apply IHre1. simpl. apply MApp.
            apply H12. apply H13. apply H8.
            destruct (a =? t)%char eqn:E1.
            rewrite eqb_eq in E1.
            rewrite Heq.
            apply MApp. inversion H7.
            rewrite app_assoc.
            apply MStarApp.
            apply MApp. subst. apply MChar.
            apply H12. apply H13. apply H8.
            inversion H7. inversion H13. inversion H12.
            inversion H12.
            assert (Heq1 : a :: s1 ++ s0 = (a :: s1) ++ s0).
            { reflexivity. }
            rewrite Heq1. 
            apply MApp. rewrite IHre1. apply H7. apply H8.
            inversion H7.
            assert(Heq1 : a :: (s3 ++ s4) ++ s0 = (a :: (s3 ++ s4)) ++ s0).
            { reflexivity. }
            rewrite Heq1. apply MApp.
            rewrite IHre1. simpl. apply MApp.
            apply H12. apply H13. apply H8.
            assert(Heq1 : a :: s1 ++ s0 = (a :: s1) ++ s0).
            { reflexivity. }
            rewrite Heq1. apply MApp.
            inversion H7. rewrite IHre1.
            simpl. apply MApp. apply H12. apply H13. apply H8.
            inversion H1.
            assert(Heq : a :: s1 ++ s0 = (a :: s1) ++ s0).
            { reflexivity. }
            rewrite Heq. apply MApp. rewrite IHre1. apply H7.
            apply H8.
            inversion H1. destruct re1.
            inversion H7. inversion H12.
            inversion H7. inversion H12.
            inversion H7. destruct (a =? t)%char eqn:E1.
            rewrite eqb_eq in E1. subst.
            inversion H12. inversion H4. simpl in *.
            assert (Heq1 : t :: (s2 ++ s4) ++ s0 = (([t] ++ s2) ++ s4)++ s0).
            { reflexivity. }
            rewrite Heq1.
            apply MApp.
            apply MStarApp. apply MStarApp. apply MChar. apply H5.
            apply H13. apply H8.
            inversion H12. inversion H17.
            assert (Heq : a :: s1 ++ s0 = (a :: s1) ++ s0).
            { reflexivity. }
            rewrite Heq. apply MApp.
            inversion H7.
            destruct re1_1.
            inversion H12. inversion H17.
            rewrite IHre1. simpl. apply MApp. apply H12.
            apply H13.
            destruct (a =? t)%char eqn:E1.
            rewrite eqb_eq in E1. subst.
            assert (Heq1 : t :: s3 ++ s4 = ([t] ++ s3) ++ s4).
            { reflexivity. }
            rewrite Heq1.
            apply MStarApp.
            inversion H12.
            assert(Heq2 : [t] ++ s1 ++ s2 = ([t] ++ s1) ++ s2).
            { reflexivity. }
            rewrite Heq2. apply MStarApp.
            apply MApp. apply MChar. apply H4. apply H5. apply H13.
            inversion H12. inversion H17.
            inversion H12. apply IHre1. simpl.
            apply MApp. apply MApp. apply H17. apply H18. apply H13.
            apply IHre1. simpl. apply MApp.
            apply H12. apply H13.
            apply IHre1. simpl. apply MApp. apply H12. apply H13.
            apply H8.
            assert (Heq : a :: s1 ++ s0 = (a :: s1) ++ s0).
            { reflexivity. }
            rewrite Heq. apply MApp.
            apply IHre1. apply H7.
            apply H8.
            assert (Heq : a :: s1 ++ s0 = (a :: s1) ++ s0).
            { reflexivity. }
            rewrite Heq. apply MApp.
            apply IHre1. apply H7. apply H8.
          }
        }
        { simpl in E. discriminate. }
  - simpl. intro s. split.
    + intro H. inversion H.
      * apply MUnionL. apply IHre1. apply H2.
      * apply MUnionR. apply IHre2. apply H1.
    + intro H. inversion H.
      * apply MUnionL. apply IHre1. apply H2.
      * apply MUnionR. apply IHre2. apply H1.
  - intro s. split.
    + intro H. simpl. destruct re.
      * inversion H. inversion H2.
      * apply star_ne in H. destruct H.
        destruct H. destruct H. destruct H0.
        inversion H0.
      * destruct (a =? t)%char eqn:E.
        { rewrite eqb_eq in E. subst. simpl in *.
          Search eqb. rewrite eqb_refl in IHre.
          inversion H.
          inversion H2.
          subst. inversion H1. subst. rewrite eqb_refl.
          assert (Heq: s = [] ++ s).
          { reflexivity. }
          rewrite Heq. apply MApp. apply MEmpty.
          apply H3.
        }
        { inversion H. inversion H2. subst. inversion H1.
          subst. rewrite eqb_refl in E. discriminate E.
        }
      * apply star_ne in H. destruct H. destruct H.
        destruct H. destruct H0. rewrite IHre in H0.
        rewrite H. apply MApp. apply H0. apply H1.
      * apply star_ne in H. destruct H. destruct H.
        destruct H. destruct H0. rewrite IHre in H0.
        rewrite H. apply MApp. apply H0. apply H1.
      * apply star_ne in H. destruct H. destruct H.
        destruct H. destruct H0. rewrite IHre in H0.
        rewrite H. apply MApp. apply H0. apply H1.
    + intro H. simpl in H. destruct re eqn:E.
      * inversion H.
      * inversion H.
      * inversion H. destruct (a =? t)%char eqn:E1.
        { inversion H3. rewrite eqb_eq in E1. subst. simpl in *.
          assert (Heq : t :: s2 = [t] ++ s2).
          { reflexivity. }
          rewrite Heq. apply MStarApp.
          apply MChar. apply H4.
        }
        { inversion H3. }
      * inversion H. assert (Heq : a :: s1 ++ s2 = (a :: s1) ++ s2).
        { reflexivity. }
        rewrite Heq. apply MStarApp. rewrite IHre. apply H3.
        apply H4.
      * inversion H. assert (Heq : a :: s1 ++ s2 = (a :: s1) ++ s2).
        { reflexivity. }
        rewrite Heq. apply MStarApp. rewrite IHre. apply H3.
        apply H4.
      * inversion H. assert (Heq : a :: s1 ++ s2 = (a :: s1) ++ s2).
        { reflexivity. }
        rewrite Heq. apply MStarApp. rewrite IHre. apply H3.
        apply H4.
Qed.

Definition matches_regex m : Prop :=
  forall (s : string) re, reflect (s =~ re) (m s re).

Fixpoint regex_match (s : string) (re : @reg_exp ascii) : bool :=
  match re with
  | EmptySet => false
  | EmptyStr => match s with [] => true | _  => false end
  | Char a => match s with
              | [c] => if (a =? c)%char then true else false
              | _ => false end
  | App r1 r2 => match s with
                 | [] => match_eps re
                 | hd :: tl => regex_match tl (derive hd re)
                 end
  | Union r1 r2 => match s with
                   | [] => match_eps re
                   | hd :: tl => regex_match tl (derive hd re)
                   end
  | Star r => match s with
              | [] => true
              | hd :: tl => regex_match tl (derive hd re)
              end
  end.

Theorem regex_refl : matches_regex regex_match.
Proof.
  unfold matches_regex. intro s.
  induction s as [| h t IH].
  - intro re. destruct re; simpl.
    + apply ReflectF. intro H. inversion H.
    + apply ReflectT. apply MEmpty.
    + apply ReflectF. intro H. inversion H.
    + destruct (match_eps re1 && match_eps re2) eqn:E.
      * rewrite andb_true_iff in E. destruct E.
        apply ReflectT. eapply (MApp [] _ []).
        { assert (Heq : reflect ([] =~ re1) (match_eps re1)).
          apply match_eps_refl. rewrite H in Heq.
          inversion Heq. apply H1.
        }
        { assert (Heq : reflect ([] =~ re2) (match_eps re2)).
          apply match_eps_refl. rewrite H0 in Heq.
          inversion Heq. apply H1.
        }
      * apply ReflectF. intro H.
        inversion H. destruct s1 eqn:Es1.
        { destruct s2 eqn:Es2.
          assert (Heq : reflect ([] =~ re1) (match_eps re1)).
          { apply match_eps_refl. }
          inversion Heq.
          assert (Heq1 : reflect ([] =~ re2) (match_eps re2)).
          { apply match_eps_refl. }
          inversion Heq1.
          rewrite <- H5 in E; rewrite <- H7 in E;
          simpl in E; discriminate E.
          contradiction.
          contradiction.
          simpl in H1. inversion H1.
        }
        { inversion H1. }
    + simpl. destruct (match_eps re1 || match_eps re2) eqn:E.
      * apply ReflectT.
        destruct (match_eps re1) eqn:E1.
        { apply MUnionL.
          assert (Heq : reflect ([] =~ re1) (match_eps re1)).
          { apply match_eps_refl. }
          rewrite E1 in Heq. inversion Heq.
          apply H.
        }
        { simpl in E. apply MUnionR.
          assert (Heq : reflect ([] =~ re2) (match_eps re2)).
          { apply match_eps_refl. }
          rewrite E in Heq. inversion Heq.
          apply H.
        }
      * apply ReflectF. unfold not. intro H.
        inversion H. destruct (match_eps re1) eqn:E1.
        { simpl in E. discriminate E. }
        { simpl in E.
          assert (Heq : reflect ([] =~ re1) (match_eps re1)).
          { apply match_eps_refl. }
          rewrite E1 in Heq. inversion Heq.
          contradiction.
        }
        destruct (match_eps re2) eqn:E2.
        { destruct (match_eps re1); discriminate E. }
        { assert (Heq : reflect ([] =~ re2) (match_eps re2)).
          { apply match_eps_refl. }
          rewrite E2 in Heq. inversion Heq.
          contradiction.
        }
    + simpl. apply ReflectT. apply MStar0.
  - intro re. destruct re; simpl.
    + apply ReflectF. intro H. inversion H.
    + apply ReflectF. intro H. inversion H.
    + destruct (t0 =? h)%char eqn:E.
      * rewrite eqb_eq in E. rewrite E. destruct t as [| h' t'].
        { apply ReflectT. apply MChar. }
        { apply ReflectF. intro H. inversion H. }
      * destruct t as [| h' t'].
        { apply ReflectF. intro H. inversion H. rewrite H2 in E.
          rewrite eqb_refl in E. discriminate E. }
        { apply ReflectF. intro H. inversion H. }
    + destruct re1.
      * destruct t.
        { simpl. apply ReflectF. intro H. inversion H. inversion H3. }
        { simpl. apply ReflectF. intro H. inversion H. inversion H3. }
      * assert (Heq: reflect (t =~ (derive h re2)) (regex_match t (derive h re2)) ->
                reflect (h :: t =~ App EmptyStr re2) (regex_match t (derive h re2))).
        { intro H. inversion H.
          { apply ReflectT. eapply (MApp [] _ (h :: t)).
            { apply MEmpty. }
            { apply derive_corr. apply H1. }
          }
          { apply ReflectF. intro H2. inversion H2. inversion H6.
            subst. simpl in H3. rewrite H3 in H7. apply derive_corr in H7.
            contradiction.
          }
        }
        apply Heq. apply IH.
      * destruct (h =? t0)%char eqn:E.
        { rewrite eqb_eq in E. rewrite E.
          assert (Heq: reflect (t =~ re2) (regex_match t re2) ->
                       reflect (t0 :: t =~ App (Char t0) re2) (regex_match t re2)).
          { intro H. inversion H.
            { apply ReflectT. eapply (MApp [t0] _ t).
              { apply MChar. }
              { apply H1. }
            }
            { apply ReflectF. intro H2. inversion H2. inversion H6.
              subst. inversion H3. rewrite H5 in H7. contradiction. 
            }
          }
          apply Heq. apply IH.
        }
        { assert (Heq : reflect (t =~ EmptySet) (regex_match t EmptySet) ->
                        reflect (h :: t =~ App (Char t0) re2) (regex_match t EmptySet)).
          { intro H. inversion H.
            { inversion H1. }
            { apply ReflectF. intro H2. inversion H2. inversion H6.
              subst. inversion H3. rewrite H5 in E. rewrite eqb_refl in E.
              discriminate E.
            }
          }
          apply Heq. apply IH.
        }
      * destruct (match_eps (App re1_1 re1_2)) eqn:E.
        { assert (Heq : reflect (t =~ (Union (derive h re2) (App (derive h (App re1_1 re1_2)) re2)))
                                (regex_match t
                                             (Union (derive h re2) (App (derive h (App re1_1 re1_2)) re2))) ->
                        reflect (h :: t =~ App (App re1_1 re1_2) re2)
                                (regex_match t
                                             (Union (derive h re2) (App (derive h (App re1_1 re1_2)) re2)))
                 ).
          { intro H. inversion H.
            { simpl. rewrite <- H0. apply ReflectT. apply derive_corr.
              simpl. simpl in E. rewrite E. simpl in H1. apply H1.
            }
            { simpl. rewrite <- H0. apply ReflectF. intro H2.
              apply derive_corr in H2. simpl in H2. simpl in E.
            rewrite E in H2. simpl in H1. contradiction. }
          }
          apply Heq. apply IH.
        }
        { assert (Heq : reflect (t =~ App (derive h (App re1_1 re1_2)) re2) (regex_match t (App (derive h (App re1_1 re1_2)) re2))
          ->
          reflect (h :: t =~ App (App re1_1 re1_2) re2)
                  (regex_match t (App (derive h (App re1_1 re1_2)) re2))).
          { intro H. inversion H.
            { simpl. rewrite <- H0. apply ReflectT. apply derive_corr.
              simpl. simpl in E. rewrite E. simpl in H1. apply H1.
            }
            { simpl. rewrite <- H0. apply ReflectF. intro H2.
              apply derive_corr in H2. simpl in H2. simpl in E.
              rewrite E in H2. simpl in H1. contradiction. }
          }
          apply Heq. apply IH.
        }
      * destruct (match_eps (Union re1_1 re1_2)) eqn:E.
        { assert (Heq :  reflect (t =~ (Union (derive h re2)
          (App (derive h (Union re1_1 re1_2)) re2)))
    (regex_match t
       (Union (derive h re2)
          (App (derive h (Union re1_1 re1_2)) re2)))
                    ->
                    reflect (h :: t =~ App (Union re1_1 re1_2) re2)
    (regex_match t
       (Union (derive h re2)
          (App (derive h (Union re1_1 re1_2)) re2)))).
          { intro H. inversion H.
            { simpl. rewrite <- H0. apply ReflectT.  apply derive_corr.
              simpl. simpl in E. rewrite E. simpl in H1. apply H1.
            }
            { simpl. rewrite <- H0. apply ReflectF. intro H2.
              apply derive_corr in H2. simpl in H2. simpl in E.
              rewrite E in H2. simpl in H1. contradiction. }
          }
          apply Heq. apply IH.
        }
        { assert (Heq : reflect (t =~ App (derive h (Union re1_1 re1_2)) re2) (regex_match t (App (derive h (Union re1_1 re1_2)) re2))
                        ->
                        reflect (h :: t =~ App (Union re1_1 re1_2) re2)
                                (regex_match t (App (derive h (Union re1_1 re1_2)) re2))).
          { intro H. inversion H.
            { simpl. rewrite <- H0. apply ReflectT. apply derive_corr.
              simpl. simpl in E. rewrite E. simpl in H1. apply H1.
            }
            { simpl. rewrite <- H0. apply ReflectF. intro H2.
              apply derive_corr in H2. simpl in H2. simpl in E.
              rewrite E in H2. simpl in H1. contradiction. }
          }
          apply Heq. apply IH.
        }
      * assert (Heq : reflect (t =~ Union (derive h re2) (App (derive h (Star re1)) re2)) (regex_match t (Union (derive h re2) (App (derive h (Star re1)) re2)))
                      ->
                      reflect (h :: t =~ App (Star re1) re2)
                              (regex_match t
                                           (if match_eps (Star re1)
                                            then Union (derive h re2) (App (derive h (Star re1)) re2)
                                            else App (derive h (Star re1)) re2))).
        { intro H. inversion H.
          { simpl. rewrite <- H0. apply ReflectT. apply derive_corr.
            simpl. simpl in H1. apply H1.
          }
          { simpl. rewrite <- H0. apply ReflectF. intro H2.
            apply derive_corr in H2. simpl in H2. simpl in H1.
            contradiction.
          }
        }
        apply Heq. apply IH.
    + assert (Heq : reflect (t =~ (Union (derive h re1) (derive h re2)))
                            (regex_match t (Union (derive h re1) (derive h re2))) ->
                    reflect (h :: t =~ Union re1 re2)
                            (regex_match t (Union (derive h re1) (derive h re2)))).
      { intro H. inversion H.
        { apply ReflectT. apply derive_corr. simpl. apply H1. }
        { apply ReflectF. intro H2. apply derive_corr in H2.
          simpl in H2. contradiction.
        }
      }
      apply Heq. apply IH.
    + assert (Heq : reflect (t =~ derive h (Star re))
                            (regex_match t (derive h (Star re)))
                    ->
                    reflect (h :: t =~ Star re)
                            (regex_match t
                                         match re with
                                         | EmptySet | EmptyStr => EmptySet
                                         | _ => App (derive h re) (Star re)
                                         end)
             ).
      { intro H. inversion H.
        { apply ReflectT. apply derive_corr. simpl. simpl in H1.
          apply H1.
        }
        { apply ReflectF. intro H2. apply derive_corr in H2.
          contradiction.
        }
      }
      apply Heq. apply IH.
Qed.