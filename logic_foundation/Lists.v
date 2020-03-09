From LF Require Export Induction.
Module NatList.
  Inductive natprod : Type :=
  | pair (n1 n2 : nat).

  Definition fst (p : natprod) : nat :=
    match p with
    | pair n1 n2 => n1
    end.

  Definition snd (p : natprod) : nat :=
    match p with
    | pair _ n2 => n2
    end.

  Notation "( x , y )" := (pair x y).

  Definition swap_pair (p : natprod) : natprod :=
    match p with
    | pair x y => pair y x
    end.

  Theorem surjective_pairing : forall (p : natprod),
      p = (fst p, snd p).
  Proof.
    intro p. destruct p as [n m]. simpl. reflexivity.
  Qed.

  Theorem snd_fst_is_swap : forall (p : natprod),
      (snd p, fst p) = swap_pair p.
  Proof.
    intro p. destruct p as [n m]. simpl. reflexivity.
  Qed.

  Theorem fst_swap_is_snd : forall (p : natprod),
      fst (swap_pair p) = snd p.
  Proof.
    intro p. destruct p as [n m]. simpl. reflexivity.
  Qed.

  Inductive natlist : Type :=
  | nil
  | cons (n : nat) (l : natlist).

  Notation "x :: l" := (cons x l) (at level 60, right associativity).
  Notation "[ ]" := nil.
  Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

  Fixpoint repeat (n count : nat) : natlist :=
    match count with
    | O => []
    | S count' => n :: (repeat n count')
    end.

  Fixpoint length (l : natlist) : nat :=
    match l with
    | [] => O
    | h :: t => 1 + (length t)
    end.

  Fixpoint app (l1 l2 : natlist) : natlist :=
    match l1 with
    | [] => l2
    | h :: t => h :: (app t l2)
    end.

  Notation "x ++ y" := (app x y) (at level 60, right associativity).

  Example test_app1 : [1;2;3] ++ [4;5] = [1;2;3;4;5].
  Proof. reflexivity. Qed.
  Example test_app2 : [] ++ [4;5] = [4;5].
  Proof. reflexivity. Qed.
  Example test_app3 : [1;2;3] ++ [] = [1;2;3].
  Proof. reflexivity. Qed.

  Definition hd (default : nat) (l : natlist) : nat :=
    match l with
    | [] => default
    | h :: t => h
    end.

  Definition tl (l : natlist) : natlist :=
    match l with
    | [] => []
    | h :: t => t
    end.

  Fixpoint nonzeros (l : natlist) : natlist :=
    match l with
    | [] => []
    | O :: t => nonzeros t
    | h :: t => h :: (nonzeros t)
    end.

  Fixpoint nonzeros' (l : natlist) (acc : natlist) : natlist :=
    match l with
    | [] => acc
    | h :: t => if eqb h 0 then nonzeros' t acc else nonzeros' t acc++[h]
    end.

  Fixpoint oddmembers (l : natlist) : natlist :=
    match l with
    | [] => l
    | h :: t => if oddb h then h :: (oddmembers t) else oddmembers t
    end.

  Fixpoint countoddmembers (l : natlist) : nat :=
    match l with
    | [] => O
    | h :: t => if oddb h then S (countoddmembers t)
                else countoddmembers t
    end.

  Example test_countoddmembers1 :
    countoddmembers [1;0;3;1;4;5] = 4.
  Proof. reflexivity. Qed.

  Fixpoint alternate (l1 l2 : natlist) : natlist :=
    match l1, l2 with
    | [], _ => l2
    | _, [] => l1
    | h1 :: t1, h2 :: t2 => h1 :: h2 :: (alternate t1 t2)
    end.
  
  Example test_alternate1:
    alternate [1;2;3] [4;5;6] = [1;4;2;5;3;6].
  Proof. reflexivity. Qed.
  Example test_alternate2:
    alternate [1] [4;5;6] = [1;4;5;6].
  Proof. reflexivity. Qed.
  Example test_alternate3:
    alternate [1;2;3] [4] = [1;4;2;3].
  Proof. reflexivity. Qed.
  Example test_alternate4:
    alternate [] [20;30] = [20;30].
  Proof. reflexivity. Qed.
  
  Definition bag := natlist.
  
  Fixpoint count (v : nat) (s : bag) : nat :=
    match s with
    | [] => O
    | h :: s' => if eqb h v then S(count v s')
                 else count v s'
    end.
  
  Example test_count1: count 1 [1;2;3;1;4;1] = 3.
  Proof. reflexivity. Qed.
  Example test_count2: count 6 [1;2;3;1;4;1] = 0.
  Proof. reflexivity. Qed.
  
  Definition sum : bag -> bag -> bag := app.
  
  Example test_sum1: count 1 (sum [1;2;3] [1;4;1]) = 3.
  Proof. reflexivity. Qed.
  
  Definition add (v:nat) (s:bag) : bag := v :: s.
  
  Example test_add1: count 1 (add 1 [1;4;1]) = 3.
  Proof. reflexivity. Qed.
  Example test_add2: count 5 (add 1 [1;4;1]) = 0.
  Proof. reflexivity. Qed.
  
  Fixpoint member (v:nat) (s:bag) : bool :=
    match s with
    | [] => false
    | h :: t => if eqb v h then true
                else member v t
    end.
  
  Example test_member1: member 1 [1;4;1] = true.
  Proof. reflexivity. Qed.
  Example test_member2: member 2 [1;4;1] = false.
  Proof. reflexivity. Qed.
  
  Fixpoint remove_one (v:nat) (s:bag) : bag :=
    match s with
    | [] => s
    | h :: s' => if eqb v h then s'
                 else h :: (remove_one v s')
    end.
  
  Example test_remove_one1:
    count 5 (remove_one 5 [2;1;5;4;1]) = 0.
  Proof. reflexivity. Qed.
  Example test_remove_one2:
    count 5 (remove_one 5 [2;1;4;1]) = 0.
  Proof. reflexivity. Qed.
  Example test_remove_one3:
    count 4 (remove_one 5 [2;1;4;5;1;4]) = 2.
  Proof. reflexivity. Qed.
  Example test_remove_one4:
    count 5 (remove_one 5 [2;1;5;4;5;1;4]) = 1.
  Proof. reflexivity. Qed.
  
  Fixpoint remove_all (v:nat) (s:bag) : bag :=
    match s with
    | [] => []
    | h :: s' => if eqb v h then remove_all v s'
                 else h :: (remove_all v s')
    end.
  
  Example test_remove_all1: count 5 (remove_all 5 [2;1;5;4;1]) = 0.
  Proof. reflexivity. Qed.
  Example test_remove_all2: count 5 (remove_all 5 [2;1;4;1]) = 0.
  Proof. reflexivity. Qed.
  Example test_remove_all3: count 4 (remove_all 5 [2;1;4;5;1;4]) = 2.
  Proof. reflexivity. Qed.
  Example test_remove_all4: count 5 (remove_all 5 [2;1;5;4;5;1;4;5;1;4]) = 0.
  Proof. reflexivity. Qed.

  Fixpoint subset (s1:bag) (s2:bag) : bool :=
    match s1 with
    | [] => true
    | h :: t => if member h s2 then subset t (remove_one h s2)
                else false
    end.

  Example test_subset1: subset [1;2] [2;1;4;1] = true.
  Proof. reflexivity. Qed.
  Example test_subset2: subset [1;2;2] [2;1;4;1] = false.
  Proof. reflexivity. Qed.

  Theorem nil_app : forall l : natlist, [] ++ l = l.
  Proof. intro l. simpl. reflexivity. Qed.

  Theorem tl_length_pred : forall l : natlist,
      pred (length l) = length (tl l).
  Proof.
    intro l. destruct l.
    - reflexivity.
    - simpl. reflexivity.
  Qed.

  Theorem app_assoc : forall l1 l2 l3 : natlist,
      (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
  Proof.
    intros. induction l1 as [| n l1' IHl1'].
    - simpl. reflexivity.
    - simpl. rewrite IHl1'. reflexivity.
  Qed.

  Fixpoint rev (l : natlist) : natlist :=
    match l with
    | nil => nil
    | h :: t => (rev t) ++ [h]
    end.

  Example test_rev1: rev [1;2;3] = [3;2;1].
  Proof. reflexivity. Qed.
  Example test_rev2: rev nil = nil.
  Proof. reflexivity. Qed.

  Lemma app_length : forall l1 l2 : natlist,
      length (l1 ++ l2) = (length l1) + (length l2).
  Proof.
    intros l1 l2. induction l1.
    - simpl. reflexivity.
    - simpl. rewrite IHl1. reflexivity.
  Qed.
  
  Theorem rev_length : forall l : natlist,
      length (rev l) = length l.
  Proof.
    intro l. induction l as [| n l' IHl'].
    - reflexivity.
    - simpl. rewrite app_length. rewrite IHl'. simpl.
      rewrite plus_comm. simpl. reflexivity.
  Qed.

  Theorem app_nil_r : forall l : natlist, l ++ [] = l.
  Proof.
    intro l. induction l.
    - reflexivity.
    - simpl. rewrite -> IHl. reflexivity.
  Qed.

  Theorem rev_app_distr : forall l1 l2 : natlist,
      rev (l1 ++ l2) = rev l2 ++ rev l1.
  Proof.
    intros. induction l1.
    - simpl. rewrite app_nil_r. reflexivity.
    - simpl. rewrite IHl1. rewrite app_assoc. reflexivity.
  Qed.

  Theorem rev_involutive : forall l : natlist,
      rev (rev l) = l.
  Proof.
    intro l; induction l.
    - reflexivity.
    - simpl. rewrite rev_app_distr. rewrite IHl.
      simpl. reflexivity.
  Qed.

  Theorem app_assoc4 : forall l1 l2 l3 l4 : natlist,
      l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.
  Proof.
    intros. induction l1.
    - simpl. rewrite app_assoc. reflexivity.
    - simpl. rewrite IHl1. reflexivity.
  Qed.

  Lemma nonzeros_app : forall l1 l2 : natlist,
      nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2).
  Proof.
    intros. induction l1.
    - simpl. reflexivity.
    - simpl. destruct n as [| n'] eqn:E.
      + apply IHl1.
      + rewrite IHl1. simpl. reflexivity.
  Qed.

  Fixpoint eqblist (l1 l2 : natlist) : bool :=
    match l1, l2 with
    | nil, nil => true
    | h1 :: t1, h2 :: t2 => if eqb h1 h2 then eqblist t1 t2 else false
    | _, _ => false
    end.

  Example test_eqblist1 : (eqblist nil nil = true).
  Proof. reflexivity. Qed.
  Example test_eqblist2 : eqblist [1;2;3] [1;2;3] = true.
  Proof. reflexivity. Qed.
  Example test_eqblist3 : eqblist [1;2;3] [1;2;4] = false.
  Proof. reflexivity. Qed.

  Theorem eqb_refl : forall n : nat, true = eqb n n.
  Proof.
    intro n. induction n.
    - reflexivity.
    - simpl. apply IHn.
  Qed.

  Theorem eqblist_refl : forall l : natlist, true = eqblist l l.
  Proof.
    intro l. induction l.
    - reflexivity.
    - simpl. rewrite <- IHl. rewrite <- eqb_refl. reflexivity.
  Qed.

  Theorem count_member_nonzero : forall s : bag,
      1 <=? (count 1 (1 :: s)) = true.
  Proof.
    intro s. simpl. reflexivity. Qed.

  Theorem leb_n_Sn : forall n : nat, n <=? (S n) = true.
  Proof.
    intro n. induction n.
    - reflexivity.
    - simpl. apply IHn.
  Qed.

  Theorem remove_does_not_increase_count : forall s : bag,
      (count 0 (remove_one 0 s)) <=? (count 0 s) = true.
  Proof.
    intro s. induction s.
    - reflexivity.
    - simpl. destruct n.
      + simpl. rewrite leb_n_Sn. reflexivity.
      + simpl. apply IHs.
  Qed.

  Theorem rev_injective : forall l1 l2 : natlist,
      rev l1 = rev l2 -> l1 = l2.
  Proof.
    intros. rewrite <- rev_involutive. rewrite <- H.
    rewrite rev_involutive. reflexivity.
  Qed.

  Inductive natoption : Type :=
  | Some (n : nat)
  | None.

  Fixpoint nth_error (l : natlist) (n : nat) : natoption :=
    match l with
    | [] => None
    | h :: t => if n =? 0 then Some h else nth_error t (n - 1)
    end.

  Example test_nth_error1 : nth_error [4;5;6;7] 0 = Some 4.
  Proof. reflexivity. Qed.
  Example test_nth_error2 : nth_error [4;5;6;7] 3 = Some 7.
  Proof. reflexivity. Qed.
  Example test_nth_error3 : nth_error [4;5;6;7] 9 = None.
  Proof. reflexivity. Qed.

  Definition option_elim (d : nat) (o : natoption) : nat :=
    match o with
    | Some n' => n'
    | None => d
    end.

  Definition hd_error (l : natlist) : natoption :=
    match l with
    | nil => None
    | h :: t => Some h
    end.

  Theorem option_elim_hd : forall (l : natlist) (default : nat),
      hd default l = option_elim default (hd_error l).
  Proof.
    intros. destruct l as [| n l'].
    - reflexivity.
    - simpl. reflexivity.
  Qed.

End NatList.

Inductive id : Type :=
| Id (n : nat).

Definition eqb_id (x1 x2 : id) :=
  match x1, x2 with
  | Id n1, Id n2 => n1 =? n2
  end.

Theorem eqb_id_refl : forall x, true = eqb_id x x.
Proof.
  intro x. destruct x as [n].
  simpl. Search eqb. rewrite <- NatList.eqb_refl.
  reflexivity.
Qed.

Module PartialMap.
  Export NatList.

  Inductive partial_map : Type :=
  | empty
  | record (i : id) (v : nat) (m : partial_map).

  Definition update (d : partial_map) (x : id) (value : nat)
    : partial_map :=
    record x value d.

  Fixpoint find (x : id) (d : partial_map) : natoption :=
    match d with
    | empty => None
    | record k v d' => if eqb_id x k then Some v
                       else find x d'
    end.

  Theorem update_eq :
    forall (d : partial_map) (x : id) (v : nat),
      find x (update d x v) = Some v.
  Proof.
    intros. simpl. rewrite <- eqb_id_refl. reflexivity.
  Qed.

  Theorem update_neq :
    forall (d : partial_map) (x y : id) (o : nat),
      eqb_id x y = false -> find x (update d y o) = find x d.
  Proof. intros. simpl. rewrite H. reflexivity. Qed.

End PartialMap.