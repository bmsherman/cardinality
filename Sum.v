Require Import Finite finite_iso.

Lemma injective_plus_Some {A B} (i : Iso.T (option A) (option B))
 (HN : Iso.to i None = None)
  : forall x : A, Some (Iso.to (injective_plus i) x) = Iso.to i (Some x).
Proof.
unfold injective_plus.
intros.
Abort. 

 
Section Monoid.

Variable A : Type.
Variable zero : A.
Variable plus : A -> A -> A.

Local Infix "+" := plus.

Axiom plus_comm : forall x y : A, x + y = y + x.
Axiom plus_assoc : forall x y z, x + (y + z) = (x + y) + z.
Axiom zero_l : forall x, zero + x = x.

Lemma plus_r : forall x y y', y = y' -> x + y = x + y'.
Proof.
intros. subst. reflexivity.
Qed.

Fixpoint sum_finite {n : nat} : (Fin n -> A) -> A := match n with
  | 0 => fun _ => zero
  | S n' => fun f => f None + sum_finite (fun x => f (Some x))
  end.

Definition leA (x y : A) : Type :=
  { z : A | x + z = y }.

Infix "<=" := leA.

Lemma leA_trans (x y z : A) : x <= y -> y <= z -> x <= z.
Proof.
intros. destruct X, X0.
exists (x0 + x1). subst. apply plus_assoc.
Qed.

Lemma sum_finite_le {m n : nat} (i : Fin m -> Fin n)
  (i_mono : forall x y, i x = i y -> x = y)
  (f : Fin n -> A)
  : sum_finite (fun x => f (i x)) <= sum_finite f.
Proof.
Abort.

Require Import FunctionalExtensionality.

Lemma sum_finite_well_def {m n : nat} (H : Iso.T (Fin n) (Fin m))
  (f : Fin m -> A)
  : sum_finite f = sum_finite (fun x => f (Iso.to H x)).
Proof.
assert (m = n). apply fin_iso.
apply fin_iso_to_fint. apply Iso.Sym. assumption.
induction H0.
induction m.
- simpl. reflexivity.
- simpl in H. simpl.
  destruct (Iso.to H (@None _)) eqn:fN;
    setoid_rewrite fN.
  + admit.
  + apply plus_r. 
    specialize (IHm (injective_plus H) (fun x => f (Some x))).
    simpl in IHm. rewrite IHm.

    unfold injective_plus.
Abort.

End Monoid.