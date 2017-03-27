Require Import Finite finite_iso
  Coq.Lists.List
  Coq.Sorting.Permutation.
 
Section CommutativeSemiGroup.

Context {R : Type}.
Variable zero : R.
Variable plus : R -> R -> R.

Local Infix "+" := plus.

Axiom plus_comm : forall x y : R, x + y = y + x.
Axiom plus_assoc : forall x y z, x + (y + z) = (x + y) + z.

Lemma sum_list_perm_invariant : forall (xs ys : list R),
  Permutation xs ys 
  -> fold_right plus zero xs = fold_right plus zero ys.
Proof.
intros. induction H; simpl.
- reflexivity.
- rewrite IHPermutation; reflexivity.
- rewrite !plus_assoc. rewrite (plus_comm y x). reflexivity.
- etransitivity; eassumption.
Qed.

Fixpoint sum_Fin {n : nat} : (Finite.Fin n -> R) -> R := match n with
  | 0 => fun f => zero
  | S n' => fun f => f None + sum_Fin (fun x => f (Some x))
  end.

Fixpoint sum_finiteT {A} (F : Finite.T A) 
  : (A -> R) -> R := match F with
  | Finite.F0 => fun _ => zero
  | Finite.FS F' => fun f => f None + sum_finiteT F' (fun x => f (Some x))
  | Finite.FIso F' iso => fun f =>
     sum_finiteT F' (fun i => f (Iso.to iso i))
  end.

Definition sum_finiteT' {A} (F : Finite.T' A)
  (f : A -> R) : R := sum_Fin (fun x => f (Iso.from (Tiso F) x)).

Lemma plus_r : forall x y y', y = y' -> x + y = x + y'.
Proof.
intros. subst. reflexivity.
Qed.

Lemma sum_finiteT_list_same {A} (F : Finite.T A) (f : A -> R)
  : sum_finiteT F f = fold_right plus zero
  (List.map f (Finite.elements F)).
Proof.
induction F; simpl; intros.
- reflexivity.
- apply plus_r. rewrite List.map_map. apply IHF.
- rewrite List.map_map. apply IHF. 
Qed.

Lemma sum_Fin_list_same (n : nat) (f : Fin n -> R)
  : sum_Fin f = fold_right plus zero (List.map f (elements_Fin n)).
Proof.
induction n; simpl.
- reflexivity.
- apply plus_r. rewrite List.map_map.
  apply IHn.
Qed.

Lemma sum_finiteT'_list_same {A} (F : Finite.T' A) (f : A -> R)
  : sum_finiteT' F f = fold_right plus zero
  (List.map f (Finite.elements' F)).
Proof.
unfold elements', sum_finiteT'.
rewrite List.map_map.
apply sum_Fin_list_same.
Qed.

Lemma sum_finiteT_well_def {A} (F1 F2 : Finite.T A)
  (f : A -> R)
  : sum_finiteT F1 f = sum_finiteT F2 f.
Proof.
rewrite !sum_finiteT_list_same.
apply sum_list_perm_invariant.
apply Permutation_map.
apply Finite.elements_Permutation.
Qed.

Lemma sum_finiteT_extensional {A} {F : Finite.T A}
  (f f' : A -> R)
  (H : forall a, f a = f' a)
  : sum_finiteT F f = sum_finiteT F f'.
Proof.
induction F; simpl.
- reflexivity.
- f_equal; auto.
- auto.
Qed.

End CommutativeSemiGroup.