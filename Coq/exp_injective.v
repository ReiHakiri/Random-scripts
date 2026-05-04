Require Import Arith.
Require Import Lia.

Definition increasing (f: nat -> nat): Prop := forall n: nat, f n < f(n + 1).

Definition alt_increasing (f: nat -> nat): Prop := forall n m: nat, n < m -> f n < f m.

Lemma lt_to_eq: forall n m: nat, n < m -> exists d: nat, m = n + d /\ d <> 0.
Proof.
  intros. exists (m - n). split.
  - rewrite Nat.add_sub_assoc.
    -- rewrite Nat.add_comm. rewrite <- Nat.add_sub_assoc.
      --- rewrite Nat.sub_diag. rewrite Nat.add_comm. simpl. reflexivity.
      --- apply le_n.
    -- apply Nat.lt_le_incl. apply H.
  - unfold not. intros. assert ((m - n) + n = n).
    -- rewrite H0. simpl. reflexivity.
    -- rewrite Nat.add_comm in H1. rewrite Minus.le_plus_minus_r in H1.
      --- rewrite H1 in H. apply Lt.lt_irrefl in H. destruct H.
      --- apply Nat.lt_le_incl. apply H.
Qed.

Theorem increasing_eq: forall f: nat -> nat, increasing f <-> alt_increasing f.
Proof. Admitted.

Definition injective {A B: Type} (f: A -> B): Prop := forall x y: A, f x = f y -> x = y.

Theorem contrapositive: forall P Q: Prop, (P -> Q) -> (~ Q -> ~ P).
Proof. Admitted.

Theorem increasing_imply_injective: forall f: nat -> nat, increasing f -> injective f.
Proof.
  unfold injective. intros. apply increasing_eq in H. unfold alt_increasing in H.
  pose proof H. specialize (H x y). specialize (H1 y x).
  assert (~ f x < f y).
  - unfold not. intros. rewrite H0 in H2. apply Lt.lt_irrefl in H2. destruct H2.
  - assert (~ f y < f x).
    -- unfold not. intros. rewrite H0 in H3. apply Lt.lt_irrefl in H3. destruct H3.
    -- apply contrapositive in H. apply contrapositive in H1.
      --- apply not_lt in H. apply not_lt in H1.
          pose proof Nat.le_antisymm. specialize (H4 x y). apply H4 in H1.
          ---- apply H1.
          ---- apply H.
      --- apply H3.
      --- apply H2.
Qed.

Theorem exp_increasing: forall a: nat, a > 1 -> increasing (fun n: nat => a ^ n).
Proof.
  unfold increasing. intros. induction n.
  - simpl. rewrite Nat.mul_1_r. apply H.
  - replace (a ^ (S n + 1)) with (a * a ^ (n + 1)). replace (a ^ (S n)) with (a * a ^ n).
    -- apply Nat.mul_lt_mono_pos_l. assert (0 < 1). lia. pose proof lt_trans.
       specialize (H1 0 1 a). apply H1 in H. apply H. apply H0. apply IHn.
    -- simpl. reflexivity.
    -- simpl. reflexivity.
Qed.

Theorem exp_injective: forall a: nat, a > 1 -> injective (fun n: nat => a ^ n).
Proof.
  intros. apply exp_increasing in H. apply increasing_imply_injective. apply H.
Qed.
