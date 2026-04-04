Record category: Type := {
  obj: Type;
  hom: obj -> obj -> Type;
  id: forall a: obj, hom a a;
  o: forall {a b c: obj}, hom b c -> hom a b -> hom a c;
  o_assoc:
  forall {a b c d: obj} (h: hom c d) (g: hom b c) (f: hom a b),
  o h (o g f) = o (o h g) f;
  id_l: forall {a b: obj} (f: hom a b), o (id b) f = f;
  id_r: forall {a b: obj} (f: hom a b), o f (id a) = f}.

Definition is_l_id {C: category} {a: obj C} (f: hom C a a) :=
  forall (b: obj C) (g: hom C b a), o C f g = g.

Theorem identity_unique_l: forall C: category, forall a: obj C, forall f: hom C a a, is_l_id f -> f = id C a.
Proof.
  intros. unfold is_l_id in H.
  assert (o C f (id C a) = f). apply (id_r C).
  assert (o C f (id C a) = id C a). apply H.
  rewrite H0 in H1. apply H1.
Qed.

Definition is_r_id {C: category} {a: obj C} (f: hom C a a) :=
  forall (b: obj C) (g: hom C a b), o C g f = g.

Theorem identity_unique_r: forall C: category, forall a: obj C, forall f: hom C a a, is_r_id f -> f = id C a.
Proof.
  intros. unfold is_r_id in H.
  assert (o C (id C a) f = f). apply (id_l C).
  assert (o C (id C a) f = id C a). apply H.
  rewrite H0 in H1. apply H1.
Qed.
