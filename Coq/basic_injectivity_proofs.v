Definition injective {A B: Type} (f: A -> B): Prop := forall x y: A, f x = f y -> x = y.

Example all_inner_injective: forall A B C: Type, forall (f: B -> C) (g: A -> B),
  injective (fun x => f(g x)) -> injective g.
Proof.
  intros A B C f g.
  intro. unfold injective.
  intros x y. intros.
  unfold injective in H. specialize (H x y).
  assert (f(g x) = f(g y)).
  - rewrite H0. reflexivity.
  - apply H in H1. apply H1.
Qed.

Inductive e_1: Type :=
  | v_1.

Inductive e_2: Type :=
  | v_2
  | v_3.
  
Inductive e_3: Type :=
  | v_4.
  
Definition g (x: e_1): e_2 :=
  match x with
  | v_1 => v_2
  end.

Definition f (x: e_2): e_3 :=
  match x with
  | v_2 => v_4
  | v_3 => v_4
  end.

Example not_all_outer_injective: ~ forall A B C: Type, forall (f: B -> C) (g: A -> B),
  injective (fun x => f(g x)) -> injective f.
Proof.
  unfold not. intros.
  specialize (H e_1 e_2 e_3). specialize (H f g).
  assert (injective (fun x => f(g x))).
  - unfold injective. intros. destruct x.
    -- destruct y.
      --- reflexivity.
  - apply H in H0. unfold injective in H0.
    specialize (H0 v_2 v_3).
    assert (f v_2 = f v_3).
    -- simpl. reflexivity.
    -- apply H0 in H1. congruence.
Qed.
