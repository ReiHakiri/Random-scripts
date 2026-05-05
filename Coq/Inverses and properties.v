Definition c_injective {A B: Type} (f: A -> B) := exists g: B -> A, forall x: A, x = g(f x).

Definition injective {A B: Type} (f: A -> B) := forall x y: A, f x = f y -> x = y.

Theorem c_injective_imply_injective: forall A B: Type, forall f: A -> B, c_injective f -> injective f.
Proof.
  unfold injective. unfold c_injective. intros.
  destruct H as [g H]. assert (g(f x) = g(f y)).
  - rewrite H0. reflexivity.
  - rewrite <- H in H1. rewrite <- H in H1. apply H1.
Qed.

Definition c_surjective {A B: Type} (f: A -> B) := exists g: B -> A, forall x: B, x = f(g x).

Definition surjective {A B: Type} (f: A -> B) := forall y: B, exists x: A, y = f x.

Theorem c_surjective_imply_surjective: forall A B: Type, forall f: A -> B, c_surjective f -> surjective f.
Proof.
  unfold surjective. unfold c_surjective. intros.
  intros. destruct H as [g H]. exists (g y). rewrite <- H. reflexivity.
Qed.
